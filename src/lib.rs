//! 自动扩展槽位的对象槽。
//! 由多个固定槽构成，每个固定槽用不扩容的数组来装元素。
//! 当槽位上的数组长度不够时，不会扩容，而是线程安全的到下一个槽位分配新数组。
//! 第一个固定槽位的数组长度为32。
//! 迭代跳过未分配的槽；已分配的槽包含所有默认初始化的元素。

use std::marker::PhantomData;
use std::mem::replace;
use std::ops::{Index, IndexMut, Range};
use std::ptr::{self, null_mut, NonNull};
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Mutex;

// skip the shorter buckets to avoid unnecessary allocations.
// this also reduces the maximum capacity of a arr.
pub const SKIP: usize = 32;
pub const SKIP_BUCKET: usize = ((usize::BITS - SKIP.leading_zeros()) as usize) - 1;
pub const BUCKETS: usize = (u32::BITS as usize) - SKIP_BUCKET;
/// Maximum valid index, not a length. The exclusive range bound is MAX_ENTRIES + 1.
pub const MAX_ENTRIES: usize = (u32::MAX as usize) - SKIP;

/// Creates default-initialized buckets, then replaces the listed entries.
/// Remaining entries of allocated buckets retain their default values.
/// ```
/// let arr = pi_buckets::buckets![1, 2, 3];
/// assert_eq!(arr[1], 2);
/// let repeated = pi_buckets::buckets![7; 3];
/// assert_eq!(repeated[2], 7);
/// ```
#[macro_export]
macro_rules! buckets {
    () => { $crate::Buckets::new() };
    ($elem:expr; $n:expr) => {{
        let mut arr = $crate::Buckets::with_capacity($n);
        arr.extend(::core::iter::repeat($elem).take($n));
        arr
    }};
    ($($x:expr),+ $(,)?) => (
        <$crate::Buckets<_> as core::iter::FromIterator<_>>::from_iter([$($x),+])
    );
}

/// Stable-address, default-initialized buckets. First allocation uses a mutex;
/// readers acquire the fully initialized allocation without locking.
/// Shared reads may coexist with allocation, but not unsafe writes to their entries.
pub struct Buckets<T> {
    buckets: [AtomicPtr<T>; BUCKETS],
    lock: Mutex<()>,
}

impl<T> Default for Buckets<T> {
    fn default() -> Self {
        Self {
            buckets: [null_mut(); BUCKETS].map(AtomicPtr::new),
            lock: Mutex::new(()),
        }
    }
}

// Ownership transfers all allocated T values to the receiving thread.
unsafe impl<T: Send> Send for Buckets<T> {}
// Shared allocation can initialize on one thread and destroy on another;
// shared references also expose T to readers.
unsafe impl<T: Send + Sync> Sync for Buckets<T> {}

impl<T> Buckets<T> {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn get(&self, location: &Location) -> Option<&T> {
        // 安全：Location 的私有桶索引已由构造函数验证。
        let ptr = unsafe { self.buckets.get_unchecked(location.bucket) }.load(Ordering::Acquire);
        if ptr.is_null() {
            return None;
        }
        // Location is validated; publication initializes the entire allocation.
        Some(unsafe { &*ptr.add(location.entry) })
    }

    #[inline]
    pub fn get_mut(&mut self, location: &Location) -> Option<&mut T> {
        // 安全：Location 保证桶索引有效，self 为独占借用。
        let ptr = *unsafe { self.buckets.get_unchecked_mut(location.bucket) }.get_mut();
        if ptr.is_null() {
            return None;
        }
        // Exclusive self borrow excludes all other access to this allocation.
        Some(unsafe { &mut *ptr.add(location.entry) })
    }

    /// # Safety
    /// The location's bucket must be allocated. No conflicting unsafe access may
    /// occur for the lifetime of the returned reference, which is tied to self.
    #[inline]
    pub unsafe fn get_unchecked(&self, location: &Location) -> &T {
        unsafe { &*self.entries(location.bucket).add(location.entry) }
    }

    /// # Safety
    /// The location's bucket must be allocated.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, location: &Location) -> &mut T {
        // 安全：Location 保证桶索引有效，self 为独占借用。
        let ptr = *unsafe { self.buckets.get_unchecked_mut(location.bucket) }.get_mut();
        // 安全：调用方保证桶已分配，Location 保证元素在桶内。
        unsafe { &mut *ptr.add(location.entry) }
    }

    /// Shared-reference mutable access. Prefer get_mut with exclusive ownership.
    ///
    /// # Safety
    /// The selected element must have no live shared or mutable references and
    /// no concurrent accesses until the returned borrow ends. The allocation
    /// must remain owned by self for that lifetime. Synchronize across threads;
    /// different entries may be accessed independently, but slices/iterators can
    /// borrow many entries at once.
    /// ```
    /// use pi_buckets::{Buckets, Location};
    /// let arr = Buckets::<usize>::with_capacity(1);
    /// unsafe { *arr.load(&Location::of(0)).unwrap() = 4; }
    /// assert_eq!(arr[0], 4);
    /// ```
    #[allow(clippy::mut_from_ref)] // 调用方通过 unsafe 契约保证元素独占访问。
    #[inline]
    pub unsafe fn load(&self, location: &Location) -> Option<&mut T> {
        // 安全：Location 的私有桶索引已由构造函数验证。
        let ptr = unsafe { self.buckets.get_unchecked(location.bucket) }.load(Ordering::Acquire);
        if ptr.is_null() {
            return None;
        }
        // Caller guarantees exclusive access to the selected element.
        Some(unsafe { &mut *ptr.add(location.entry) })
    }

    /// # Safety
    /// The bucket must be allocated and all aliasing, lifetime and thread
    /// requirements of load apply.
    #[allow(clippy::mut_from_ref)] // 与 load 相同的元素独占访问契约。
    #[inline]
    pub unsafe fn load_unchecked(&self, location: &Location) -> &mut T {
        unsafe { &mut *self.entries(location.bucket).add(location.entry) }
    }

    /// Transfer all allocations out of self. Existing borrows exclude this call.
    pub fn take(&mut self) -> [Vec<T>; BUCKETS] {
        let mut result = std::array::from_fn(|_| Vec::new());
        for (i, bucket) in self.buckets.iter_mut().enumerate() {
            let ptr = replace(bucket.get_mut(), null_mut());
            if !ptr.is_null() {
                // Exclusive ownership, exact boxed-slice layout, detached once.
                result[i] = unsafe { to_bucket_vec(ptr, i) };
            }
        }
        result
    }

    pub fn iter(&self) -> BucketIter<'_, T> {
        self.slice(0..MAX_ENTRIES + 1)
    }

    /// Iterate allocated entries in a validated half-open range, skipping gaps.
    /// ```
    /// let arr = pi_buckets::buckets![1, 2, 4];
    /// assert_eq!(arr.slice(1..3).copied().collect::<Vec<_>>(), [2, 4]);
    /// ```
    pub fn slice(&self, range: Range<usize>) -> BucketIter<'_, T> {
        BucketIter::with_prefix(&[], self, range)
    }

    /// Bucket-only iteration using absolute indices after an external prefix.
    /// The range must start at or after capacity; no prefix is read.
    pub fn slice_row(&self, range: Range<usize>, capacity: usize) -> BucketIter<'_, T> {
        assert!(
            range.start >= capacity,
            "range starts inside omitted prefix"
        );
        BucketIter {
            cursor: SegmentCursor::new(
                NonNull::dangling().as_ptr(),
                capacity,
                Some(&self.buckets),
                range,
            ),
        }
    }

    /// Yield contiguous slices, clipped to the range, skipping unallocated gaps.
    pub fn segments(&self, range: Range<usize>) -> BucketSegments<'_, T> {
        BucketSegments {
            cursor: self.slice(range).cursor,
        }
    }

    pub fn iter_mut(&mut self) -> BucketIterMut<'_, T> {
        self.slice_mut(0..MAX_ENTRIES + 1)
    }

    pub fn slice_mut(&mut self, range: Range<usize>) -> BucketIterMut<'_, T> {
        // The exclusive self borrow lasts for the returned iterator's lifetime.
        BucketIterMut {
            cursor: SegmentCursor::new(NonNull::dangling().as_ptr(), 0, Some(&self.buckets), range),
            exclusive: PhantomData,
        }
    }

    pub fn segments_mut(&mut self, range: Range<usize>) -> BucketSegmentsMut<'_, T> {
        BucketSegmentsMut {
            cursor: self.slice_mut(range).cursor,
            exclusive: PhantomData,
        }
    }

    /// # Safety
    /// bucket must be less than BUCKETS. The pointer is borrowed, may be null,
    /// and must not be freed. Dereferencing requires initialized, in-bounds
    /// access and the usual aliasing/thread rules; self must remain alive.
    #[inline]
    pub unsafe fn entries(&self, bucket: usize) -> *mut T {
        // 安全：调用方按契约保证 bucket 小于 BUCKETS。
        unsafe { self.buckets.get_unchecked(bucket) }.load(Ordering::Acquire)
    }

    /// # Safety
    /// All requirements of entries apply.
    pub unsafe fn load_entries(&self, bucket: usize) -> *mut T {
        unsafe { self.entries(bucket) }
    }

    /// # Safety
    /// bucket must be in bounds. The pointer must not outlive self or be freed;
    /// any access must respect the exclusive borrow and initialized bounds.
    #[inline]
    pub unsafe fn entries_mut(&mut self, bucket: usize) -> *mut T {
        // 安全：调用方保证桶索引有效，self 为独占借用。
        *unsafe { self.buckets.get_unchecked_mut(bucket) }.get_mut()
    }

    // The raw atomic pointer table is deliberately not exposed: replacing a
    // published allocation would invalidate safe references and ownership.
}

impl<T: Default> Buckets<T> {
    /// Allocates enough whole buckets for capacity entries, not capacity + 1.
    /// Previously installed buckets are owned by the result during unwinding.
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(capacity <= MAX_ENTRIES + 1, "exceeded maximum length");
        let mut result = Self::new();
        if capacity != 0 {
            for bucket in 0..=Location::bucket(capacity - 1) {
                *result.buckets[bucket].get_mut() = bucket_alloc(Location::bucket_len(bucket));
            }
        }
        result
    }

    pub fn alloc(&mut self, location: &Location) -> &mut T {
        let ptr = self.alloc_bucket(location);
        // Exclusive self borrow and validated location.
        unsafe { &mut *ptr.add(location.entry) }
    }

    pub fn set(&mut self, location: &Location, value: T) -> T {
        replace(self.alloc(location), value)
    }

    /// # Safety
    /// All aliasing, lifetime and thread requirements of load apply. Allocation
    /// initializes the whole bucket; readers must not observe conflicting writes.
    #[allow(clippy::mut_from_ref)] // 分配不替代调用方的元素独占访问保证。
    pub unsafe fn load_alloc(&self, location: &Location) -> &mut T {
        let ptr = self.load_alloc_bucket(location);
        unsafe { &mut *ptr.add(location.entry) }
    }

    /// # Safety
    /// No other access or reference to the selected element may overlap this
    /// replacement (including destruction of the old value). Synchronize across
    /// threads and obey load's lifetime/aliasing requirements.
    /// ```
    /// let arr = pi_buckets::buckets![1, 2];
    /// unsafe { arr.insert(&pi_buckets::Location::of(2), 3); }
    /// assert_eq!(arr[2], 3);
    /// ```
    pub unsafe fn insert(&self, location: &Location, value: T) -> T {
        unsafe { replace(self.load_alloc(location), value) }
    }

    /// Return a borrowed raw pointer to a fully initialized, stable allocation.
    /// Safe to request concurrently. Dereferencing is unsafe: the caller must
    /// respect bounds, self's lifetime, aliases and synchronization, and must
    /// never free this allocation. The length is derived from location's bucket.
    pub fn load_alloc_bucket(&self, location: &Location) -> *mut T {
        // 安全：Location 的私有桶索引已由构造函数验证。
        let bucket = unsafe { self.buckets.get_unchecked(location.bucket) };
        let mut ptr = bucket.load(Ordering::Acquire);
        if ptr.is_null() {
            // A default constructor can panic before publication. Recover poison
            // explicitly while retaining the guard for the whole initialization.
            let _guard = self
                .lock
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            ptr = bucket.load(Ordering::Acquire);
            if ptr.is_null() {
                ptr = bucket_alloc(location.len());
                bucket.store(ptr, Ordering::Release);
            }
        }
        ptr
    }

    pub fn alloc_bucket(&mut self, location: &Location) -> *mut T {
        self.load_alloc_bucket(location)
    }
}

impl<T> Index<usize> for Buckets<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        self.get(&Location::of(index))
            .expect("bucket not allocated")
    }
}
impl<T> IndexMut<usize> for Buckets<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(&Location::of(index))
            .expect("bucket not allocated")
    }
}
impl<T> Drop for Buckets<T> {
    fn drop(&mut self) {
        for (i, bucket) in self.buckets.iter_mut().enumerate() {
            let ptr = *bucket.get_mut();
            if !ptr.is_null() {
                // Self owns each exact-sized boxed slice, with no live borrows.
                unsafe {
                    drop(Box::from_raw(ptr::slice_from_raw_parts_mut(
                        ptr,
                        Location::bucket_len(i),
                    )))
                };
            }
        }
    }
}
impl<T: Default> FromIterator<T> for Buckets<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut result = Self::with_capacity(iter.size_hint().0);
        result.extend(iter);
        result
    }
}
impl<T: Default> Extend<T> for Buckets<T> {
    /// Replaces entries starting at index zero (there is no logical length).
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for (i, value) in iter.into_iter().enumerate() {
            self.set(&Location::of(i), value);
        }
    }
}
impl<T: Clone> Clone for Buckets<T> {
    fn clone(&self) -> Self {
        let mut result = Self::new();
        for (i, bucket) in self.buckets.iter().enumerate() {
            let ptr = bucket.load(Ordering::Acquire);
            if !ptr.is_null() {
                // Borrow source, never reconstruct source ownership. Both the
                // partial clone and installed target buckets have RAII owners.
                let source = unsafe { std::slice::from_raw_parts(ptr, Location::bucket_len(i)) };
                let target = source.to_vec().into_boxed_slice();
                *result.buckets[i].get_mut() = Box::into_raw(target).cast::<T>();
            }
        }
        result
    }
}

/// Allocates exactly len default-initialized entries using a boxed-slice layout.
/// The caller owns the returned allocation and must eventually reconstruct
/// Box<[T]> with exactly len entries (or Vec with length/capacity len for non-ZST).
/// Default panics destroy any already initialized entries.
pub fn bucket_alloc<T: Default>(len: usize) -> *mut T {
    let entries: Box<[T]> = std::iter::repeat_with(T::default).take(len).collect();
    Box::into_raw(entries).cast::<T>()
}

unsafe fn to_bucket_vec<T>(ptr: *mut T, bucket: usize) -> Vec<T> {
    // Only detached allocations owned by Buckets reach this conversion.
    unsafe {
        Box::from_raw(ptr::slice_from_raw_parts_mut(
            ptr,
            Location::bucket_len(bucket),
        ))
        .into_vec()
    }
}

/// A validated element address, never an iterator sentinel or one-past position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    bucket: usize,
    entry: usize,
    len: usize,
}
impl Default for Location {
    #[inline]
    fn default() -> Self {
        Self::new(0, 0)
    }
}
impl Location {
    /// Validates the bucket and entry, caching the derived bucket length.
    #[inline]
    pub const fn new(bucket: usize, entry: usize) -> Self {
        let len = Self::bucket_len(bucket);
        assert!(entry < len, "invalid entry");
        Self { bucket, entry, len }
    }
    #[inline]
    pub const fn of(index: usize) -> Self {
        assert!(index <= MAX_ENTRIES, "exceeded maximum index");
        let skipped = index + SKIP;
        let bucket = (usize::BITS - skipped.leading_zeros()) as usize - SKIP_BUCKET - 1;
        let len = Self::bucket_len(bucket);
        Self {
            bucket,
            entry: skipped - len,
            len,
        }
    }
    pub const fn bucket(index: usize) -> usize {
        Self::of(index).bucket
    }
    #[inline]
    pub const fn bucket_index(&self) -> usize {
        self.bucket
    }
    #[inline]
    pub const fn entry(&self) -> usize {
        self.entry
    }
    #[allow(clippy::len_without_is_empty)] // 表示所属桶容量，不是 Location 集合长度。
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }
    pub const fn bucket_len(bucket: usize) -> usize {
        assert!(bucket < BUCKETS, "invalid bucket");
        1usize << (bucket + SKIP_BUCKET)
    }
    pub const fn bucket_capacity(bucket: usize) -> usize {
        // Subtract before adding: the last bucket's power-of-two end would
        // overflow usize on 32-bit, although its actual capacity is representable.
        let len = Self::bucket_len(bucket);
        (len - SKIP) + len
    }
    #[inline]
    pub const fn index(&self, capacity: usize) -> usize {
        let index = self.len - SKIP + self.entry;
        match capacity.checked_add(index) {
            Some(index) => index,
            None => panic!("index overflow"),
        }
    }
}

// Iterator position is separate from Location. Each selected segment uses the
// same pointer + remaining representation, whether prefix or bucket storage.
struct SegmentCursor<'a, T> {
    ptr: *mut T,
    remaining: usize,
    position: usize,
    scan: usize,
    end: usize,
    prefix: *const T,
    prefix_len: usize,
    buckets: Option<&'a [AtomicPtr<T>; BUCKETS]>,
    lifetime: PhantomData<&'a T>,
}
impl<'a, T> SegmentCursor<'a, T> {
    fn new(
        prefix: *const T,
        prefix_len: usize,
        buckets: Option<&'a [AtomicPtr<T>; BUCKETS]>,
        range: Range<usize>,
    ) -> Self {
        assert!(range.start <= range.end, "reversed range");
        assert!(
            range.end.saturating_sub(prefix_len) <= MAX_ENTRIES + 1,
            "exceeded maximum range"
        );
        let mut result = Self {
            ptr: NonNull::dangling().as_ptr(),
            remaining: 0,
            position: range.start,
            scan: range.start,
            end: range.end,
            prefix,
            prefix_len,
            buckets,
            lifetime: PhantomData,
        };
        result.advance();
        result
    }

    #[cold]
    #[inline(never)]
    fn advance(&mut self) -> bool {
        if self.scan < self.end && self.scan < self.prefix_len {
            let len = self.end.min(self.prefix_len) - self.scan;
            // Only safe slice or caller-validated raw prefix constructors can
            // reach this branch, and the clipped segment is within the prefix.
            self.ptr = unsafe { self.prefix.add(self.scan) }.cast_mut();
            self.position = self.scan;
            self.scan += len;
            self.remaining = len;
            return true;
        }
        if let Some(buckets) = self.buckets {
            while self.scan < self.end {
                let location = Location::of(self.scan - self.prefix_len);
                let len = (location.len() - location.entry).min(self.end - self.scan);
                // 安全：Location::of 已验证桶索引，桶表通过共享引用访问。
                let ptr = unsafe { buckets.get_unchecked(location.bucket) }.load(Ordering::Acquire);
                self.position = self.scan;
                self.scan += len;
                if !ptr.is_null() {
                    // Validated entry; Acquire observes fully initialized storage.
                    self.ptr = unsafe { ptr.add(location.entry) };
                    self.remaining = len;
                    return true;
                }
            }
        }
        self.position = self.end;
        self.scan = self.end;
        self.remaining = 0;
        false
    }

    #[inline(always)]
    fn next_ptr(&mut self) -> Option<*mut T> {
        if self.remaining == 0 && !self.advance() {
            return None;
        }
        let ptr = self.ptr;
        // Current initialized segment has at least one remaining element.
        self.ptr = unsafe { self.ptr.add(1) };
        self.remaining -= 1;
        self.position += 1;
        Some(ptr)
    }

    fn next_segment(&mut self) -> Option<(*mut T, usize)> {
        if self.remaining == 0 && !self.advance() {
            return None;
        }
        let segment = (self.ptr, self.remaining);
        self.position += self.remaining;
        self.remaining = 0;
        Some(segment)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // 最小为当前连续段的entry数量；中间未分配槽只能计入上界。
        (self.remaining, Some(self.end - self.position))
    }
}

/// Shared entry iterator. Gaps are skipped; index() is the next logical position
/// (after next(), index() - 1 is the yielded entry's index). Not a snapshot:
/// allocation may become visible before a future bucket is visited.
pub struct BucketIter<'a, T> {
    cursor: SegmentCursor<'a, T>,
}
impl<'a, T> BucketIter<'a, T> {
    pub fn empty() -> Self {
        Self {
            cursor: SegmentCursor::new(NonNull::dangling().as_ptr(), 0, None, 0..0),
        }
    }
    /// Read an initialized prefix followed by bucket entries at prefix.len().
    pub fn with_prefix(prefix: &'a [T], buckets: &'a Buckets<T>, range: Range<usize>) -> Self {
        Self {
            cursor: SegmentCursor::new(
                prefix.as_ptr(),
                prefix.len(),
                Some(&buckets.buckets),
                range,
            ),
        }
    }
    /// Raw-prefix replacement for the former arbitrary-pointer constructor.
    ///
    /// # Safety
    /// If prefix_len is nonzero, prefix must point to prefix_len initialized,
    /// aligned T values in one allocation, valid for 'a. Their total byte size
    /// must not exceed isize::MAX. No mutation, deallocation or conflicting
    /// aliases may occur while any yielded reference lives, including across
    /// threads. For zero length prefix may be null and is never dereferenced.
    /// The bucket borrow also lasts for 'a. This does not assume ownership.
    pub unsafe fn from_raw_prefix(
        prefix: *const T,
        prefix_len: usize,
        buckets: &'a Buckets<T>,
        range: Range<usize>,
    ) -> Self {
        Self {
            cursor: SegmentCursor::new(prefix, prefix_len, Some(&buckets.buckets), range),
        }
    }
    pub fn index(&self) -> usize {
        self.cursor.position
    }
    pub fn into_segments(self) -> BucketSegments<'a, T> {
        BucketSegments {
            cursor: self.cursor,
        }
    }
}
impl<'a, T> Iterator for BucketIter<'a, T> {
    type Item = &'a T;
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Cursor only visits initialized storage borrowed for 'a.
        self.cursor.next_ptr().map(|ptr| unsafe { &*ptr })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.cursor.size_hint()
    }
}

pub struct BucketIterMut<'a, T> {
    cursor: SegmentCursor<'a, T>,
    exclusive: PhantomData<&'a mut T>,
}
impl<T> BucketIterMut<'_, T> {
    pub fn index(&self) -> usize {
        self.cursor.position
    }
}
impl<'a, T> Iterator for BucketIterMut<'a, T> {
    type Item = &'a mut T;
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Exclusive borrow; each entry is visited only once, even across gaps.
        self.cursor.next_ptr().map(|ptr| unsafe { &mut *ptr })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.cursor.size_hint()
    }
}

pub struct BucketSegments<'a, T> {
    cursor: SegmentCursor<'a, T>,
}
impl<T> BucketSegments<'_, T> {
    pub fn index(&self) -> usize {
        self.cursor.position
    }
}
impl<'a, T> Iterator for BucketSegments<'a, T> {
    type Item = &'a [T];
    fn next(&mut self) -> Option<Self::Item> {
        // Each nonempty span is initialized, contiguous, and borrowed for 'a.
        self.cursor
            .next_segment()
            .map(|(ptr, len)| unsafe { std::slice::from_raw_parts(ptr, len) })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            usize::from(self.cursor.remaining != 0),
            Some(self.cursor.end - self.cursor.position),
        )
    }
}
pub struct BucketSegmentsMut<'a, T> {
    cursor: SegmentCursor<'a, T>,
    exclusive: PhantomData<&'a mut T>,
}
impl<'a, T> Iterator for BucketSegmentsMut<'a, T> {
    type Item = &'a mut [T];
    fn next(&mut self) -> Option<Self::Item> {
        // Exclusive self borrow and disjoint, one-time segment visitation.
        self.cursor
            .next_segment()
            .map(|(ptr, len)| unsafe { std::slice::from_raw_parts_mut(ptr, len) })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            usize::from(self.cursor.remaining != 0),
            Some(self.cursor.end - self.cursor.position),
        )
    }
}
