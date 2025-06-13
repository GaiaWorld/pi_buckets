//! 自动扩展槽位的对象槽。
//! 由多个固定槽构成，每个固定槽用不扩容的Vec来装元素。
//! 当槽位上的Vec长度不够时，不会扩容Vec，而是线程安全的到下一个槽位分配新Vec。
//! 第一个固定槽位的Vec长度为32。
//! 固定槽迭代性能比Vec慢1-10倍， 主要损失在切换bucket时，原子操作及缓存失效。

#![feature(test)]
extern crate test;

use std::mem::{forget, replace, transmute, ManuallyDrop};
use std::ops::{Index, IndexMut, Range};
use std::ptr::{null, null_mut};
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Mutex;

// skip the shorter buckets to avoid unnecessary allocations.
// this also reduces the maximum capacity of a arr.
pub const SKIP: usize = 32;
pub const SKIP_BUCKET: usize = ((usize::BITS - SKIP.leading_zeros()) as usize) - 1;

pub const BUCKETS: usize = (u32::BITS as usize) - SKIP_BUCKET;
pub const MAX_ENTRIES: usize = (u32::MAX as usize) - SKIP;

/// Creates a [`Buckets`] containing the given elements.
///
/// `buckets!` allows `Buckets`s to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
///
/// - Create a [`Buckets`] containing a given list of elements:
///
/// ```
/// let arr = pi_buckets::buckets![1, 2, 3];
/// assert_eq!(arr[0], 1);
/// assert_eq!(arr[1], 2);
/// assert_eq!(arr[2], 3);
/// ```
///
/// - Create a [`Buckets`] from a given element and size:
///
/// ```
/// let arr = pi_buckets::buckets![1; 3];
/// assert_eq!(arr[0], 1);
/// assert_eq!(arr[1], 1);
/// assert_eq!(arr[2], 1);
/// ```
#[macro_export]
macro_rules! buckets {
    () => {
        $crate::Buckets::new()
    };
    ($elem:expr; $n:expr) => {{
        let mut arr = $crate::Buckets::with_capacity($n);
        arr.extend(::core::iter::repeat($elem).take($n));
        arr
    }};
    ($($x:expr),+ $(,)?) => (
        <$crate::Buckets<_> as core::iter::FromIterator<_>>::from_iter([$($x),+])
    );
}

/// A lock-free, auto-expansion buckets.
///
/// See [the crate documentation](crate) for details.
///
/// # Notes
///
/// The bucket array is stored inline, meaning that the
/// `Buckets<T>` is quite large. It is expected that you
/// store it behind an [`Arc`](std::sync::Arc) or similar.
pub struct Buckets<T> {
    buckets: [AtomicPtr<T>; BUCKETS],
    lock: Mutex<()>,
}

impl<T> Default for Buckets<T> {
    fn default() -> Self {
        let buckets = [null_mut(); BUCKETS];
        Buckets {
            buckets: buckets.map(AtomicPtr::new),
            lock: Mutex::default(),
        }
    }
}

unsafe impl<T: Send> Send for Buckets<T> {}
unsafe impl<T: Sync> Sync for Buckets<T> {}

impl<T: Default> Buckets<T> {
    /// Constructs a new, empty `Buckets<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::pi_buckets;
    /// let arr: pi_buckets::Buckets<i32> = pi_buckets::Buckets::new();
    /// ```
    #[inline]
    pub fn new() -> Buckets<T> {
        Buckets::default()
    }

    /// Constructs a new, empty `Buckets<T>` with the specified capacity.
    ///
    /// Capacity will be aligned to a power of 2 size.
    /// The array will be able to hold at least `capacity` elements
    /// without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let mut arr = pi_buckets::Buckets::with_capacity(10);
    ///
    /// for i in 0..32 {
    ///     // will not allocate
    ///     arr.set(&Location::of(i), i);
    /// }
    ///
    /// // may allocate
    /// arr.set(&Location::of(33), 33);
    /// ```
    #[inline(always)]
    pub fn with_capacity(capacity: usize) -> Buckets<T> {
        Self::with_capacity_multiple(capacity, 1)
    }

    pub fn with_capacity_multiple(capacity: usize, multiple: usize) -> Buckets<T> {
        let mut buckets = [null_mut(); BUCKETS];
        if capacity == 0 {
            return Buckets {
                buckets: buckets.map(AtomicPtr::new),
                lock: Mutex::default(),
            };
        }
        let end = Location::of(capacity).bucket as usize;
        for (i, bucket) in buckets[..=end].iter_mut().enumerate() {
            let len = Location::bucket_len(i);
            *bucket = bucket_alloc(len * multiple);
        }

        Buckets {
            buckets: buckets.map(AtomicPtr::new),
            lock: Mutex::default(),
        }
    }

    /// Returns a reference to the element at the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![10, 40, 30];
    /// assert_eq!(Some(&40), arr.get(&Location::of(1)));
    /// assert_eq!(None, arr.get(&Location::of(33)));
    /// ```
    #[inline(always)]
    pub fn get(&self, location: &Location) -> Option<&T> {
        // safety: `location.bucket` is always in bounds
        let entries = unsafe { self.entries(location.bucket as usize) };

        // bucket is uninitialized
        if entries.is_null() {
            return None;
        }

        // safety: `location.entry` is always in bounds for it's bucket
        Some(unsafe { &*entries.add(location.entry) })
    }

    /// Returns a reference to an element, without doing bounds
    /// checking or verifying that the element is fully initialized.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index, or for an element that
    /// is being concurrently initialized is **undefined behavior**, even if
    /// the resulting reference is not used.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![1, 2, 4];
    ///
    /// unsafe {
    ///     assert_eq!(arr.get_unchecked(&Location::of(1)), &2);
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, location: &Location) -> &T {
        &*self.entries(location.bucket as usize).add(location.entry)
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let mut arr = pi_buckets::buckets![10, 40, 30];
    /// assert_eq!(Some(&mut 40), arr.get_mut(&Location::of(1)));
    /// assert_eq!(None, arr.get_mut(&Location::of(33)));
    /// ```
    #[inline(always)]
    pub fn get_mut(&mut self, location: &Location) -> Option<&mut T> {
        let entries = unsafe { self.entries(location.bucket as usize) };

        // bucket is uninitialized
        if entries.is_null() {
            return None;
        }

        // safety: `location.entry` is always in bounds for it's bucket
        Some(unsafe { &mut *entries.add(location.entry) })
    }

    /// Returns a mutable reference to an element, without doing bounds
    /// checking or verifying that the element is fully initialized.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is **undefined
    /// behavior**, even if the resulting reference is not used.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let mut arr = pi_buckets::buckets![1, 2, 4];
    ///
    /// unsafe {
    ///     assert_eq!(arr.get_unchecked_mut(&Location::of(1)), &mut 2);
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, location: &Location) -> &mut T {
        &mut *self.entries(location.bucket as usize).add(location.entry)
    }
    /// Returns a mutable reference to the element at the given index.
    /// If the bucket corresponding to the index is not allocated,
    /// it will be allocated automatically, and the returned T is null
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let mut arr = pi_buckets::buckets![10, 40, 30];
    /// assert_eq!(40, *arr.alloc(&Location::of(1)));
    /// assert_eq!(0, *arr.alloc(&Location::of(3)));
    /// ```
    #[inline(always)]
    pub fn alloc(&mut self, location: &Location) -> &mut T {
        let entries = self.alloc_bucket(location);
        // safety: `location.entry` is always in bounds for it's bucket
        unsafe { &mut *entries.add(location.entry) }
    }
    /// set element at the given index.
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let mut arr = crate::pi_buckets::buckets![10, 40, 30];
    /// assert_eq!(40, arr.set(&Location::of(1), 20));
    /// assert_eq!(Some(&20), arr.get(&Location::of(1)));
    /// assert_eq!(0, arr.set(&Location::of(33), 5));
    /// assert_eq!(Some(&5), arr.get(&Location::of(33)));
    /// ```
    #[inline(always)]
    pub fn set(&mut self, location: &Location, value: T) -> T {
        replace(self.alloc(location), value)
    }

    /// Returns a mutable reference to the element at the given index.
    /// If the bucket corresponding to the index is not allocated,
    /// it will not be allocated automatically, and the returned None.
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![10, 40, 30];
    /// assert_eq!(10, *arr.load(&Location::of(0)).unwrap());
    /// assert_eq!(Some(&mut 40), arr.load(&Location::of(1)));
    /// assert_eq!(0, *arr.load(&Location::of(3)).unwrap());
    /// assert_eq!(None, arr.load(&Location::of(33)));
    /// ```
    #[inline(always)]
    pub fn load(&self, location: &Location) -> Option<&mut T> {
        let entries = unsafe { self.load_entries(location.bucket as usize) };

        // bucket is uninitialized
        if entries.is_null() {
            return None;
        }

        // safety: `location.entry` is always in bounds for it's bucket
        Some(unsafe { &mut *entries.add(location.entry) })
    }

    /// Returns a mutable reference to an element, without doing bounds
    /// checking or verifying that the element is fully initialized.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is **undefined
    /// behavior**, even if the resulting reference is not used.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![1, 2, 4];
    ///
    /// unsafe {
    ///     assert_eq!(arr.load_unchecked(&Location::of(1)), &mut 2);
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn load_unchecked(&self, location: &Location) -> &mut T {
        &mut *self
            .load_entries(location.bucket as usize)
            .add(location.entry)
    }

    /// Returns a mutable reference to the element at the given index.
    /// If the bucket corresponding to the index is not allocated,
    /// it will be allocated automatically, and the returned T is null
    /// # Examples
    ///
    /// ```
    ///
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![10, 40, 30];
    /// assert_eq!(40, *arr.load_alloc(&Location::of(1)));
    /// assert_eq!(0, *arr.load_alloc(&Location::of(3)));
    /// ```
    #[inline(always)]
    pub fn load_alloc(&self, location: &Location) -> &mut T {
        let entries = self.load_alloc_bucket(location);
        // safety: `location.entry` is always in bounds for it's bucket
        unsafe { transmute(entries.add(location.entry)) }
    }
    /// insert an element at the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![1, 2];
    /// arr.insert(&Location::of(2), 3);
    /// assert_eq!(arr[0], 1);
    /// assert_eq!(arr[1], 2);
    /// assert_eq!(arr[2], 3);
    /// ```
    #[inline(always)]
    pub fn insert(&self, location: &Location, value: T) -> T {
        replace(self.load_alloc(location), value)
    }
    /// take buckets.
    pub fn take(&self) -> [Vec<T>; BUCKETS] {
        let mut buckets = [0; BUCKETS].map(|_| Vec::new());
        for (i, p) in self.buckets.iter().enumerate() {
            let ptr = p.swap(null_mut(), Ordering::Relaxed);
            if ptr.is_null() {
                continue;
            }
            buckets[i] = to_bucket_vec(ptr, i);
        }
        buckets
    }

    /// Returns an iterator over the array.
    ///
    /// Values are yielded in the form `Entry`. The array may
    /// have in-progress concurrent writes that create gaps, so `index`
    /// may not be strictly sequential.
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// use crate::{pi_buckets, pi_buckets::Location};
    /// let arr = pi_buckets::buckets![1, 2, 4];
    /// arr.insert(&Location::of(98), 98);
    /// let mut iterator = arr.iter();
    /// assert_eq!(iterator.size_hint().0, 32);
    /// let r = iterator.next().unwrap();
    /// assert_eq!((iterator.index() - 1, *r), (0, 1));
    /// let r = iterator.next().unwrap();
    /// assert_eq!((iterator.index() - 1, *r), (1, 2));
    /// let r = iterator.next().unwrap();
    /// assert_eq!((iterator.index() - 1, *r), (2, 4));
    /// for i in 3..32 {
    ///     let r = iterator.next().unwrap();
    ///     assert_eq!((iterator.index() - 1, *r), (i, 0));
    /// }
    /// for i in 96..98 {
    ///     let r = iterator.next().unwrap();
    ///     assert_eq!((iterator.index() - 1, *r), (i, 0));
    /// }
    /// let r = iterator.next().unwrap();
    /// assert_eq!((iterator.index() - 1, *r), (98, 98));
    /// for i in 99..224 {
    ///     let r = iterator.next().unwrap();
    ///     assert_eq!((iterator.index() - 1, *r), (i, 0));
    /// }
    /// assert_eq!(iterator.next(), None);
    /// assert_eq!(iterator.size_hint().0, 0);
    /// ```
    #[inline]
    pub fn iter(&self) -> BucketIter<'_, T> {
        self.slice_row(0..MAX_ENTRIES, 0)
    }

    /// Returns an iterator over the array at the given range.
    ///
    /// Values are yielded in the form `Entry`.
    ///
    /// # Examples
    ///
    /// ```
    /// let arr = crate::pi_buckets::buckets![1, 2, 4, 6];
    /// let mut iterator = arr.slice(1..3);
    ///
    /// let r = iterator.next().unwrap();
    /// assert_eq!(*r, 2);
    /// let r = iterator.next().unwrap();
    /// assert_eq!(*r, 4);
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn slice(&self, range: Range<usize>) -> BucketIter<'_, T> {
        self.slice_row(range, 0)
    }
    pub fn slice_row(&self, range: Range<usize>, capacity: usize) -> BucketIter<'_, T> {
        let start = Location::of(range.start - capacity);
        let end = Location::of(range.end - capacity);
        BucketIter::new(
            null_mut(),
            start,
            end.entry,
            end.bucket,
            &self,
            capacity,
        )
        .init_iter()
    }

    #[inline(always)]
    pub unsafe fn load_entries(&self, bucket: usize) -> *mut T {
        self.buckets.get_unchecked(bucket).load(Ordering::Relaxed)
    }
    #[inline(always)]
    pub unsafe fn entries(&self, bucket: usize) -> *mut T {
        *self.buckets.get_unchecked(bucket).as_ptr()
    }
    #[inline(always)]
    pub unsafe fn entries_mut(&mut self, bucket: usize) -> *mut T {
        *self.buckets.get_unchecked_mut(bucket).get_mut()
    }
    #[inline(always)]
    pub fn load_alloc_bucket(&self, location: &Location) -> *mut T {
        let bucket = unsafe { self.buckets.get_unchecked(location.bucket as usize) };
        // safety: `location.bucket` is always in bounds
        let mut entries = bucket.load(Ordering::Relaxed);
        // bucket is uninitialized
        if entries.is_null() {
            entries = bucket_init(bucket, location.len, &self.lock)
        }
        entries
    }
    #[inline(always)]
    pub fn alloc_bucket(&mut self, location: &Location) -> *mut T {
        let bucket = unsafe { self.buckets.get_unchecked_mut(location.bucket as usize) };
        // safety: `location.bucket` is always in bounds
        let mut entries = *bucket.get_mut();

        // bucket is uninitialized
        if entries.is_null() {
            entries = bucket_init(bucket, location.len, &self.lock);
        }
        entries
    }
    #[inline(always)]
    pub fn buckets(&self) -> &[AtomicPtr<T>] {
        &self.buckets
    }
}


impl<T: Default> Index<usize> for Buckets<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(&Location::of(index))
            .expect("no element found at index {index}")
    }
}

impl<T: Default> IndexMut<usize> for Buckets<T> {
    #[inline(always)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(&Location::of(index))
            .expect("no element found at index_mut {index}")
    }
}
impl<T> Drop for Buckets<T> {
    fn drop(&mut self) {
        for (i, bucket) in self.buckets.iter_mut().enumerate() {
            let ptr = *bucket.get_mut();
            if ptr.is_null() {
                continue;
            }
            // safety: in drop
            to_bucket_vec(ptr, i);
        }
    }
}


impl<T: Default> FromIterator<T> for Buckets<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();

        let (lower, _) = iter.size_hint();
        let mut arr = Buckets::with_capacity(lower);
        for (i, value) in iter.enumerate() {
            arr.set(&Location::of(i), value);
        }
        arr
    }
}

impl<T: Default> Extend<T> for Buckets<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        for (i, value) in iter.enumerate() {
            self.set(&Location::of(i), value);
        }
    }
}

impl<T: Default + Clone> Clone for Buckets<T> {
    fn clone(&self) -> Buckets<T> {
        let mut buckets: [*mut T; BUCKETS] = [null_mut(); BUCKETS];

        for (i, bucket) in buckets.iter_mut().enumerate() {
            let ptr = unsafe { self.load_entries(i) };
            if ptr.is_null() {
                continue;
            }
            let vec = to_bucket_vec(ptr, i);
            *bucket = ManuallyDrop::new(vec.clone()).as_mut_ptr();
            forget(vec);
        }
        Buckets {
            buckets: buckets.map(AtomicPtr::new),
            lock: Mutex::default(),
        }
    }
}

/// An iterator over the elements of a [`Buckets<T>`].
///
/// See [`Buckets::iter`] for details.
pub struct BucketIter<'a, T> {
    ptr: *mut T,
    start: Location,
    end_entry: usize,
    end_bucket: isize,
    buckets: &'a Buckets<T>,
    capacity: usize,
}

impl<'a, T> BucketIter<'a, T> {
    #[inline(always)]
    pub fn empty() -> Self {
        BucketIter {
            ptr: null_mut(),
            start: Location::default(),
            end_entry: 0,
            end_bucket: 0,
            buckets: unsafe { transmute(null::<[AtomicPtr<T>; BUCKETS]>()) },
            capacity: 0,
        }
    }
    #[inline(always)]
    pub fn new(
        ptr: *mut T,
        start: Location,
        end_entry: usize,
        end_bucket: isize,
        buckets: &'a Buckets<T>,
        capacity: usize,
    ) -> Self {
        BucketIter {
            ptr,
            start,
            end_entry,
            end_bucket,
            buckets,
            capacity,
        }
    }
    #[inline(always)]
    fn init_iter(mut self) -> Self {
        if self.start.bucket > self.end_bucket {
            self.start.len = self.start.entry;
            return self;
        }
        if self.start.bucket == self.end_bucket {
            self.start.len = self.end_entry;
            if self.start.len == 0 {
                return self;
            }
        }
        self.load_ptr();
        if self.ptr.is_null() {
            self.start.len = self.start.entry;
        }
        self
    }
    #[inline(always)]
    pub fn index(&self) -> usize {
        self.start.index(self.capacity)
    }
    #[inline(always)]
    pub(crate) fn get(&mut self) -> &'a mut T {
        unsafe { transmute(self.ptr.add(self.start.entry)) }
    }
    #[inline(always)]
    fn load_ptr(&mut self) {
        self.ptr = unsafe {
            self.buckets.buckets
                .get_unchecked(self.start.bucket as usize)
                .load(Ordering::Relaxed)
        };
    }
    #[inline]
    pub(crate) fn next_bucket(&mut self) -> Option<&'a mut T> {
        loop {
            if self.start.bucket >= self.end_bucket {
                return None;
            }
            self.start.bucket += 1;
            self.load_ptr();
            if self.ptr.is_null() {
                continue;
            }
            if self.start.bucket == self.end_bucket {
                if self.end_entry == 0 {
                    return None;
                }
                self.start.len = self.end_entry;
            } else {
                self.start.len = Location::bucket_len(self.start.bucket as usize);
            }
            self.start.entry = 1;
            return Some(unsafe { transmute(self.ptr) });
        }
    }
    fn size(&self) -> (usize, Option<usize>) {
        if self.start.bucket > self.end_bucket {
            return (0, Some(0));
        }
        // 最小为起始槽的entry数量
        let min = self.start.len.saturating_sub(self.start.entry);
        // println!("size: {:?}", (min, self.start.len, self.start.entry));
        let c = self.end_bucket - self.start.bucket;
        if c == 0 {
            return (min, Some(min));
        }
        if c == 1 {
            return (min, Some(min + self.end_entry));
        }
        if self.start.bucket < 0 {
            let end = Location::new(c - 1, 0, self.end_entry);
            return (min, Some(min + end.index(0)));
        }
        // 中间槽的entry数量
        let n = self.start.len * (1 << (c - 1));
        (min, Some(min + n + self.end_entry))
    }
}

impl<'a, T> Iterator for BucketIter<'a, T> {
    type Item = &'a mut T;
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start.entry < self.start.len {
                let r = self.get();
                self.start.entry += 1;
                return Some(r);
            }
        return self.next_bucket();
        // 将代码内联后， 性能由10ns变为40ns
    }
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size()
    }
}


/// take vec.
#[inline(always)]
fn to_bucket_vec<T>(ptr: *mut T, bucket: usize) -> Vec<T> {
    let len = Location::bucket_len(bucket);
    unsafe { Vec::from_raw_parts(ptr, len, len) }
}

pub fn bucket_alloc<T: Default>(len: usize) -> *mut T {
    let mut entries: Vec<T> = Vec::with_capacity(len);
    entries.resize_with(entries.capacity(), || T::default());
    ManuallyDrop::new(entries).as_mut_ptr()
}

fn bucket_init<T: Default>(share_ptr: &AtomicPtr<T>, len: usize, lock: &Mutex<()>) -> *mut T {
    let _lock = lock.lock();
    let mut ptr = share_ptr.load(Ordering::Relaxed);
    if ptr.is_null() {
        ptr = bucket_alloc(len);
        share_ptr.store(ptr, Ordering::Relaxed);
    }
    ptr
}


#[derive(Debug, Default, Clone)]
pub struct Location {
    // the length
    pub len: usize,
    // the index of the entry in `bucket`
    pub entry: usize,
    // the index of the bucket
    pub bucket: isize,
}

impl Location {
    #[inline(always)]
    pub const fn new(bucket: isize, bucket_len: usize, entry: usize) -> Self {
        Location {
            len: bucket_len,
            entry,
            bucket,
        }
    }
    #[inline(always)]
    pub const fn bucket(index: usize) -> usize {
        let skipped = index.checked_add(SKIP).expect("exceeded maximum length");
        let bucket = usize::BITS - skipped.leading_zeros();
        (bucket as usize) - (SKIP_BUCKET + 1)
    }
    #[inline(always)]
    pub const fn of(index: usize) -> Location {
        let skipped = index.checked_add(SKIP).expect("exceeded maximum length");
        let bucket = usize::BITS - skipped.leading_zeros();
        let bucket = (bucket as usize) - (SKIP_BUCKET + 1);
        let bucket_len = Location::bucket_len(bucket);
        let entry = skipped ^ bucket_len;

        Location {
            len: bucket_len,
            entry,
            bucket: bucket as isize,
        }
    }
    #[inline(always)]
    pub const fn bucket_len(bucket: usize) -> usize {
        1 << (bucket + SKIP_BUCKET)
    }
    #[inline(always)]
    pub const fn bucket_capacity(bucket: usize) -> usize {
        (1 << (bucket + SKIP_BUCKET + 1)) - SKIP
    }
    #[inline(always)]
    pub const fn index(&self, capacity: usize) -> usize {
        if self.bucket < 0 {
            return self.entry;
        }
        ((i32::MAX as u32) >> (u32::BITS - 1 - self.bucket as u32) << SKIP_BUCKET) as usize
            + self.entry
            + capacity
    }
}

#[cfg(test)]
mod tests {
    use std::{mem::ManuallyDrop, sync::{Arc, Mutex}};

    use test::Bencher;

    use crate::*;
    static mut AAA: u64 = 0;

    #[test]
    fn test_iter () {
    let arr = buckets![1, 2, 4];
    arr.insert(&Location::of(98), 98);
    let mut iterator = arr.iter();
    assert_eq!(iterator.size_hint().0, 32);
    let r = iterator.next().unwrap();
    assert_eq!((iterator.index() - 1, *r), (0, 1));
    let r = iterator.next().unwrap();
    assert_eq!((iterator.index() - 1, *r), (1, 2));
    let r = iterator.next().unwrap();
    assert_eq!((iterator.index() - 1, *r), (2, 4));
    for i in 3..32 {
        let r = iterator.next().unwrap();
        assert_eq!((iterator.index() - 1, *r), (i, 0));
    }
    for i in 96..98 {
        let r = iterator.next().unwrap();
        assert_eq!((iterator.index() - 1, *r), (i, 0));
    }
    let r = iterator.next().unwrap();
    assert_eq!((iterator.index() - 1, *r), (98, 98));
    for i in 99..224 {
        let r = iterator.next().unwrap();
        assert_eq!((iterator.index() - 1, *r), (i, 0));
    }
    assert_eq!(iterator.next(), None);
    assert_eq!(iterator.size_hint().0, 0);

    }
    #[test]
    fn test_arc() {
        let arr = Arc::new(crate::Buckets::new());

        // spawn 6 threads that append to the arr
        let threads = (0..6)
            .map(|i| {
                let arr = arr.clone();

                std::thread::spawn(move || {
                    arr.insert(&Location::of(i), i);
                })
            })
            .collect::<Vec<_>>();

        // wait for the threads to finish
        for thread in threads {
            thread.join().unwrap();
        }

        for i in 0..6 {
            assert!(arr.iter().any(|x| *x == i));
        }
    }
    #[test]
    fn test_arc1() {
        let vec: Vec<Option<Arc<usize>>> = Vec::new();
        let vec1 = vec.clone();
        println!("test_arc1 start:, {:?}", ManuallyDrop::new(vec1).as_mut_ptr());
        let a1 = {
            let arr = crate::Buckets::new();
            for i in 0..6 {
                arr.insert(&Location::of(i), Some(Arc::new(i)));
            }

            for i in 0..6 {
                assert_eq!(arr[i].as_ref().unwrap().as_ref(), &i);
            }
            let a2 = arr.clone();
            assert_eq!(Arc::<usize>::strong_count(a2[0].as_ref().unwrap()), 2);
            a2
        };
        assert_eq!(Arc::<usize>::strong_count(a1[0].as_ref().unwrap()), 1);
        println!("test_arc1 {:?}", a1[0]);
    }
    #[test]
    fn test_mutex() {
        let arr = Arc::new(crate::Buckets::new());

        // set an element
        arr.insert(&Location::of(0), Some(Mutex::new(1)));

        let thread = std::thread::spawn({
            let arr = arr.clone();
            move || {
                // mutate through the mutex
                *(arr[0].as_ref().unwrap().lock().unwrap()) += 1;
            }
        });

        thread.join().unwrap();

        let x = arr[0].as_ref().unwrap().lock().unwrap();
        assert_eq!(*x, 2);
    }
    #[test]
    fn location() {
        assert_eq!(Location::of(31).bucket, 0);
        assert_eq!(Location::of(31).entry, 31);
        assert_eq!(Location::of(31).len, 32);
        assert_eq!(Location::of(32).bucket, 1);
        assert_eq!(Location::of(32).entry, 0);
        assert_eq!(Location::of(32).len, 64);
        assert_eq!(Location::bucket_len(0), 32);
        assert_eq!(0usize.saturating_sub(0), 0);
        assert_eq!(Location::new(-1, 32, 1).index(0), 1);

        for i in 0..32 {
            let loc = Location::of(i);
            assert_eq!(loc.len, 32);
            assert_eq!(loc.bucket, 0);
            assert_eq!(loc.entry, i);
            assert_eq!(loc.index(0), i);
            assert_eq!(Location::bucket(i), loc.bucket as usize);
            assert_eq!(Location::bucket_capacity(loc.bucket as usize), 32);
        }

        assert_eq!(Location::bucket_len(1), 64);
        for i in 33..96 {
            let loc = Location::of(i);
            assert_eq!(loc.len, 64);
            assert_eq!(loc.bucket, 1);
            assert_eq!(loc.entry, i - 32);
            assert_eq!(loc.index(0), i);
            assert_eq!(Location::bucket(i), loc.bucket as usize);
            assert_eq!(Location::bucket_capacity(loc.bucket as usize), 96);
        }

        assert_eq!(Location::bucket_len(2), 128);
        for i in 96..224 {
            let loc = Location::of(i);
            assert_eq!(loc.len, 128);
            assert_eq!(loc.bucket, 2);
            assert_eq!(loc.entry, i - 96);
            assert_eq!(loc.index(0), i);
            assert_eq!(Location::bucket(i), loc.bucket as usize);
            assert_eq!(Location::bucket_capacity(loc.bucket as usize), 224);
        }

        let max = Location::of(MAX_ENTRIES);
        assert_eq!(max.bucket as usize, BUCKETS - 1);
        assert_eq!(max.len, 1 << 31);
        assert_eq!(max.entry, (1 << 31) - 1);
    }
    #[bench]
    fn bench_loc(b: &mut Bencher) {
        b.iter(move || {
            for i in 0..1000 {
                unsafe { AAA += Location::of(i).entry as u64 };
            }
        });
    }
    #[bench]
    fn bench_arr(b: &mut Bencher) {
        let mut arr = Buckets::new();
        for i in 0..2000 {
            *arr.alloc(&Location::of(i)) = 0;
        }
        b.iter(move || {
            for i in arr.slice(100..200) {
                unsafe { AAA += *i };
            }
        });
    }
    #[bench]
    fn bench_vec(b: &mut Bencher) {
        let mut arr: Vec<u64> = Vec::with_capacity(0);
        for _ in 0..100 {
            arr.push(0u64);
        }
        b.iter(move || {
            for i in arr.iter() {
                unsafe { AAA += *i };
            }
        });
    }
    #[bench]
    fn bench_vec1(b: &mut Bencher) {
        let mut arrs = [0; 1].map(|_| Vec::with_capacity(0));
        for _ in 0..1000 {
            for j in arrs.iter_mut() {
                j.push(0u64);
            }
        }
        let mut c = 0u64;
        b.iter(move || {
            for i in 0..100 {
                for j in arrs.iter() {
                    c += unsafe { j.get_unchecked(i) };
                }
            }
        });
        assert_eq!(c, 0);
    }
}
