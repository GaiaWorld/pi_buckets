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
/// 首桶元素数，也是索引映射时跳过的小桶总容量。
pub const SKIP: usize = 32;
/// 首桶容量的以 2 为底的指数。
pub const SKIP_BUCKET: usize = ((usize::BITS - SKIP.leading_zeros()) as usize) - 1;
/// 可寻址的桶数量。
pub const BUCKETS: usize = (u32::BITS as usize) - SKIP_BUCKET;
/// 最大有效索引而非长度；半开范围的最大结束位置为 `MAX_ENTRIES + 1`。
pub const MAX_ENTRIES: usize = (u32::MAX as usize) - SKIP;

/// 创建默认初始化的桶，再从索引零开始填入列表或重复值。
/// 已分配桶中未被替换的元素保留默认值；空形式不分配。
/// 元素数超过 `MAX_ENTRIES + 1` 或默认构造发生 panic 时会 panic。
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

/// 地址稳定、整桶默认初始化的对象槽，没有独立的逻辑长度。
/// 首次分配使用互斥锁，读取通过原子发布获取已初始化的桶，无需加锁。
/// 共享读取可与分配并存；元素写入仍须遵守引用别名和线程同步规则。
pub struct Buckets<T> {
    buckets: [AtomicPtr<T>; BUCKETS],
    lock: Mutex<()>,
}

impl<T> Default for Buckets<T> {
    /// 创建未分配任何桶的对象槽。
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
    /// 创建未分配任何桶的对象槽，不要求元素实现 `Default`。
    pub fn new() -> Self {
        Self::default()
    }

    /// 共享借用位置对应的元素；桶未分配时返回 `None`，不会触发分配。
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

    /// 独占借用位置对应的元素；桶未分配时返回 `None`，不会触发分配。
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

    /// 不检查桶是否分配，直接返回位置对应的共享引用。
    ///
    /// # Safety
    /// 对应桶必须已分配。返回引用的生命周期绑定到 `self`，期间桶须有效且归其所有，
    /// 不得存在冲突的整元素可变引用或在 `UnsafeCell` 外修改元素。
    /// 内部可变性须遵守其自身契约，跨线程访问须同步以避免数据竞争。
    #[inline]
    pub unsafe fn get_unchecked(&self, location: &Location) -> &T {
        unsafe { &*self.entries(location.bucket).add(location.entry) }
    }

    /// 不检查桶是否分配，直接返回位置对应的独占引用。
    ///
    /// # Safety
    /// 对应桶必须已分配。返回引用借用 `self`，期间桶须有效且归其所有，
    /// 不得通过遗留裸指针或其他线程对该元素进行任何重叠访问。
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, location: &Location) -> &mut T {
        // 安全：Location 保证桶索引有效，self 为独占借用。
        let ptr = *unsafe { self.buckets.get_unchecked_mut(location.bucket) }.get_mut();
        // 安全：调用方保证桶已分配，Location 保证元素在桶内。
        unsafe { &mut *ptr.add(location.entry) }
    }

    /// 通过共享对象槽获取元素的可变引用；桶未分配时返回 `None`。
    /// 有独占对象槽时优先使用 [`Self::get_mut`]。
    ///
    /// # Safety
    /// 从创建到返回引用失效期间，该元素不得有其他存活的共享或可变引用，
    /// 也不得有其他访问（包括内部可变性访问）。桶须有效且归 `self` 所有，
    /// 返回引用的生命周期绑定到 `self`。跨线程须同步以保证这一独占性；
    /// 不同元素可独立访问，但切片和迭代器可能同时借用多个元素。
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

    /// 不检查桶是否分配，通过共享对象槽获取元素的可变引用。
    ///
    /// # Safety
    /// 对应桶必须已分配，并满足 [`Self::load`] 的全部别名、生命周期、
    /// 桶所有权和跨线程独占访问要求。
    #[allow(clippy::mut_from_ref)] // 与 load 相同的元素独占访问契约。
    #[inline]
    pub unsafe fn load_unchecked(&self, location: &Location) -> &mut T {
        unsafe { &mut *self.entries(location.bucket).add(location.entry) }
    }

    /// 将所有桶的所有权转移到按桶编号排列的向量数组，并清空对象槽。
    /// 未分配桶对应空向量；向量包含整桶元素（含默认值），并负责销毁和释放。
    /// 独占借用排除存活的安全引用。
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

    /// 按索引顺序借用所有已分配元素（含默认值），跳过未分配桶。
    /// 不是分配快照：访问后续桶前的新分配可能可见。
    pub fn iter(&self) -> BucketIter<'_, T> {
        self.slice(0..MAX_ENTRIES + 1)
    }

    /// 按半开范围 `start..end` 借用已分配元素，跳过未分配桶，不触发分配。
    /// `start > end` 或 `end > MAX_ENTRIES + 1` 时 panic；合法空范围不返回元素。
    /// 不是分配快照，访问后续桶前的新分配可能可见。
    /// ```
    /// let arr = pi_buckets::buckets![1, 2, 4];
    /// assert_eq!(arr.slice(1..3).copied().collect::<Vec<_>>(), [2, 4]);
    /// ```
    pub fn slice(&self, range: Range<usize>) -> BucketIter<'_, T> {
        BucketIter::with_prefix(&[], self, range)
    }

    /// 以 `capacity` 为外部前缀长度，按绝对半开范围迭代桶元素，但不读取前缀。
    /// 桶内逻辑索引为绝对索引减去 `capacity`，未分配桶会跳过。
    /// `start < capacity`、`start > end` 或 `end - capacity > MAX_ENTRIES + 1` 时 panic。
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

    /// 返回半开范围内按桶边界裁剪的非空共享切片，跳过未分配桶。
    /// 范围验证和非快照语义与 [`Self::slice`] 相同；不合规范围会 panic。
    pub fn segments(&self, range: Range<usize>) -> BucketSegments<'_, T> {
        BucketSegments {
            cursor: self.slice(range).cursor,
        }
    }

    /// 按索引顺序独占借用所有已分配元素（含默认值），跳过未分配桶。
    /// 每个元素至多返回一次，迭代器存活期间独占借用对象槽。
    pub fn iter_mut(&mut self) -> BucketIterMut<'_, T> {
        self.slice_mut(0..MAX_ENTRIES + 1)
    }

    /// 在半开范围内逐个独占借用已分配元素，跳过未分配桶，不分配。
    /// `start > end` 或 `end > MAX_ENTRIES + 1` 时 panic；每个元素至多返回一次。
    pub fn slice_mut(&mut self, range: Range<usize>) -> BucketIterMut<'_, T> {
        // The exclusive self borrow lasts for the returned iterator's lifetime.
        BucketIterMut {
            cursor: SegmentCursor::new(NonNull::dangling().as_ptr(), 0, Some(&self.buckets), range),
            exclusive: PhantomData,
        }
    }

    /// 返回半开范围内按桶边界裁剪的非空、互不重叠的独占切片，跳过未分配桶。
    /// `start > end` 或 `end > MAX_ENTRIES + 1` 时 panic。
    pub fn segments_mut(&mut self, range: Range<usize>) -> BucketSegmentsMut<'_, T> {
        BucketSegmentsMut {
            cursor: self.slice_mut(range).cursor,
            exclusive: PhantomData,
        }
    }

    /// 获取桶首地址的借用裸指针；桶未分配时返回空指针，不触发分配。
    ///
    /// # Safety
    /// `bucket < BUCKETS`。返回指针不转移所有权，不得释放或重建拥有者；
    /// 使用期间桶须有效且归 `self` 所有，不得在 `take` 或销毁后继续访问。
    /// 解引用前须确认非空且偏移小于 `Location::bucket_len(bucket)`；共享访问不得
    /// 与整元素可变引用冲突，写入须独占或使用合法内部可变性，跨线程须同步。
    #[inline]
    pub unsafe fn entries(&self, bucket: usize) -> *mut T {
        // 安全：调用方按契约保证 bucket 小于 BUCKETS。
        unsafe { self.buckets.get_unchecked(bucket) }.load(Ordering::Acquire)
    }

    /// 获取桶首地址的借用裸指针，与 [`Self::entries`] 相同，不分配。
    ///
    /// # Safety
    /// 须满足 [`Self::entries`] 的桶编号、边界、生命周期、所有权、
    /// 别名和线程同步要求；未分配桶返回空指针。
    pub unsafe fn load_entries(&self, bucket: usize) -> *mut T {
        unsafe { self.entries(bucket) }
    }

    /// 在独占借用下获取桶首地址；桶未分配时返回空指针，不分配。
    ///
    /// # Safety
    /// `bucket < BUCKETS`。指针仍归 `self` 所有，不得释放或重建拥有者；
    /// 使用时桶须有效且未被转移或销毁，解引用须非空且在整桶初始化边界内。
    /// 裸指针不延长独占借用：每次访问都须排除冲突引用和访问，跨线程须同步。
    #[inline]
    pub unsafe fn entries_mut(&mut self, bucket: usize) -> *mut T {
        // 安全：调用方保证桶索引有效，self 为独占借用。
        *unsafe { self.buckets.get_unchecked_mut(bucket) }.get_mut()
    }

    // The raw atomic pointer table is deliberately not exposed: replacing a
    // published allocation would invalidate safe references and ownership.
}

impl<T: Default> Buckets<T> {
    /// 分配足以容纳 `capacity` 个元素的连续整桶，所有元素用 `T::default` 初始化。
    /// 容量零时不分配；整桶取整可能分配更多元素，并不记录逻辑长度。
    /// `capacity > MAX_ENTRIES + 1` 或默认构造发生 panic 时会 panic；
    /// 展开时已创建元素和已安装的桶会被销毁。
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

    /// 确保位置所在整桶已默认初始化，返回该元素的独占引用。
    /// 默认构造的 panic 会传播，不发布未完成的桶。
    pub fn alloc(&mut self, location: &Location) -> &mut T {
        let ptr = self.alloc_bucket(location);
        // Exclusive self borrow and validated location.
        unsafe { &mut *ptr.add(location.entry) }
    }

    /// 必要时分配整桶，替换位置对应的元素并返回旧值（可能为默认值）。
    /// 首次分配时默认构造的 panic 会向调用方传播。
    pub fn set(&mut self, location: &Location, value: T) -> T {
        replace(self.alloc(location), value)
    }

    /// 必要时默认初始化整桶，通过共享对象槽返回该元素的可变引用。
    /// 默认构造的 panic 会传播，不发布未完成的桶。
    ///
    /// # Safety
    /// 须满足 [`Self::load`] 的全部引用别名、生命周期、所有权和线程独占要求。
    /// 线程安全的桶分配不保证元素写入安全，也不允许读取者与该可变引用重叠。
    #[allow(clippy::mut_from_ref)] // 分配不替代调用方的元素独占访问保证。
    pub unsafe fn load_alloc(&self, location: &Location) -> &mut T {
        let ptr = self.load_alloc_bucket(location);
        unsafe { &mut *ptr.add(location.entry) }
    }

    /// 通过共享对象槽替换元素并返回旧值；必要时默认初始化整桶。
    /// 首次分配时默认构造的 panic 会向调用方传播。
    ///
    /// # Safety
    /// 替换期间须满足 [`Self::load`] 的别名、生命周期、所有权和线程独占要求：
    /// 目标元素不得有其他存活引用或重叠访问，跨线程须同步。
    /// 旧值的所有权返回给调用方，本方法不会销毁旧值。
    /// ```
    /// let arr = pi_buckets::buckets![1, 2];
    /// unsafe { arr.insert(&pi_buckets::Location::of(2), 3); }
    /// assert_eq!(arr[2], 3);
    /// ```
    pub unsafe fn insert(&self, location: &Location, value: T) -> T {
        unsafe { replace(self.load_alloc(location), value) }
    }

    /// 确保整桶已默认初始化，返回稳定的桶首借用裸指针；可并发请求分配。
    /// 桶长度为 `location.len()`，所有权仍归 `self`，不得释放或重建拥有者。
    /// 解引用须在桶有效、未被转移或销毁时，且偏移在初始化边界内；
    /// 读取不得与整元素可变引用冲突，写入须独占或使用合法内部可变性，跨线程须同步。
    /// 默认构造发生 panic 时不发布未完成的桶，已初始化元素会被销毁。
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

    /// 在独占借用下确保整桶已初始化并返回桶首裸指针，长度为 `location.len()`。
    /// 分配、panic 和指针所有权约束与 [`Self::load_alloc_bucket`] 相同；
    /// 指针不延长独占借用，后续解引用仍须确保生命周期、边界和无冲突访问。
    pub fn alloc_bucket(&mut self, location: &Location) -> *mut T {
        self.load_alloc_bucket(location)
    }
}

impl<T> Index<usize> for Buckets<T> {
    type Output = T;
    /// 按逻辑索引读取元素，不分配；索引超过 `MAX_ENTRIES` 或桶未分配时 panic。
    fn index(&self, index: usize) -> &T {
        self.get(&Location::of(index))
            .expect("bucket not allocated")
    }
}
impl<T> IndexMut<usize> for Buckets<T> {
    /// 按逻辑索引独占借用元素；索引超过 `MAX_ENTRIES` 或桶未分配时 panic。
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
    /// 从索引零开始填入元素，按迭代器长度下界预分配整桶，其余元素保留默认值。
    /// 下界或实际元素数超过最大长度、默认构造或输入迭代发生 panic 时会 panic。
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut result = Self::with_capacity(iter.size_hint().0);
        result.extend(iter);
        result
    }
}
impl<T: Default> Extend<T> for Buckets<T> {
    /// 从索引零开始替换元素，必要时默认初始化整桶；不追加到某个逻辑长度。
    /// 元素数超过 `MAX_ENTRIES + 1` 或默认构造发生 panic 时会 panic。
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for (i, value) in iter.into_iter().enumerate() {
            self.set(&Location::of(i), value);
        }
    }
}
impl<T: Clone> Clone for Buckets<T> {
    /// 克隆所有已观察到的已分配桶及其整桶元素，未分配桶仍保持未分配。
    /// 并发分配不构成快照；元素克隆发生 panic 时会销毁已创建的副本。
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

/// 按装箱切片布局分配恰好 `len` 个默认初始化元素，将所有权交给调用方。
/// 调用方最终须用该指针和原始 `len` 重建 `Box<[T]>` 并释放一次；
/// 非零大小类型也可用长度、容量均为 `len` 的 `Vec` 接管，不可重复接管。
/// 零长度指针仍须按原布局回收，不能解引用；访问须遵守边界、别名和线程同步规则。
/// 默认构造或容量检查发生 panic 时会传播，已初始化元素会被销毁。
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

/// 已验证的桶内元素位置，不表示迭代终点或尾后位置，也不保证对应桶已分配。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    bucket: usize,
    entry: usize,
    len: usize,
}
impl Default for Location {
    /// 返回首桶首元素的位置，不触发桶分配。
    #[inline]
    fn default() -> Self {
        Self::new(0, 0)
    }
}
impl Location {
    /// 从桶编号和桶内偏移构造位置，缓存由桶编号推导的长度。
    /// `bucket >= BUCKETS` 或 `entry >= bucket_len(bucket)` 时 panic。
    #[inline]
    pub const fn new(bucket: usize, entry: usize) -> Self {
        let len = Self::bucket_len(bucket);
        assert!(entry < len, "invalid entry");
        Self { bucket, entry, len }
    }
    /// 从无前缀的逻辑索引构造位置；`index > MAX_ENTRIES` 时 panic。
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
    /// 返回无前缀逻辑索引所属的桶编号；`index > MAX_ENTRIES` 时 panic。
    pub const fn bucket(index: usize) -> usize {
        Self::of(index).bucket
    }
    /// 返回已验证的桶编号，始终小于 `BUCKETS`。
    #[inline]
    pub const fn bucket_index(&self) -> usize {
        self.bucket
    }
    /// 返回桶内偏移，始终小于所属桶的长度。
    #[inline]
    pub const fn entry(&self) -> usize {
        self.entry
    }
    /// 返回所属整桶的元素数（恒为正数），不是当前位置之后的剩余长度。
    #[allow(clippy::len_without_is_empty)] // 表示所属桶容量，不是 Location 集合长度。
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }
    /// 返回桶编号对应的元素数；`bucket >= BUCKETS` 时 panic。
    pub const fn bucket_len(bucket: usize) -> usize {
        assert!(bucket < BUCKETS, "invalid bucket");
        1usize << (bucket + SKIP_BUCKET)
    }
    /// 返回从首桶到指定桶的累计容量，即该桶末尾的无前缀半开结束索引。
    /// 不检查实际分配情况；`bucket >= BUCKETS` 时 panic。
    pub const fn bucket_capacity(bucket: usize) -> usize {
        // Subtract before adding: the last bucket's power-of-two end would
        // overflow usize on 32-bit, although its actual capacity is representable.
        let len = Self::bucket_len(bucket);
        (len - SKIP) + len
    }
    /// 返回加入外部前缀长度 `capacity` 后的绝对索引；加法溢出时 panic。
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
    /// 当前连续段中下一个待返回元素的指针；remaining 为零时不解引用。
    ptr: *mut T,
    /// 当前连续段尚未返回的元素数，也是逐元素热路径的边界判断依据。
    remaining: usize,
    /// 相对于扩展桶起点的扫描位置；桶段中为当前段末尾，前缀段中为零。
    scan: usize,
    /// 相对于扩展桶起点的半开结束位置；范围完全位于前缀时为零。
    end: usize,
    /// 借用扩展桶指针表；空迭代器为 None，切段时使用 Acquire 读取。
    buckets: Option<&'a [AtomicPtr<T>; BUCKETS]>,
    /// 将裸指针所指元素的借用生命周期绑定到迭代器，不承担所有权。
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
        let remaining = range.end.min(prefix_len).saturating_sub(range.start);
        let mut result = Self {
            ptr: NonNull::dangling().as_ptr(),
            remaining,
            scan: range.start.saturating_sub(prefix_len),
            end: range.end.saturating_sub(prefix_len),
            buckets,
            lifetime: PhantomData,
        };
        if remaining != 0 {
            // 安全：非零 remaining 保证 start < prefix_len，首段已裁剪到有效前缀内。
            // 构造入口保证前缀的初始化、对齐、单一分配和借用生命周期。
            result.ptr = unsafe { prefix.add(range.start) }.cast_mut();
        } else {
            result.advance();
        }
        result
    }

    #[cold]
    #[inline(never)]
    fn advance(&mut self) -> bool {
        // 仅在当前段耗尽时调用；扫描每次裁剪到 end，失败返回时无需重置状态。
        if let Some(buckets) = self.buckets {
            while self.scan < self.end {
                let location = Location::of(self.scan);
                let len = (location.len() - location.entry).min(self.end - self.scan);
                // 安全：Location::of 已验证桶索引，桶表通过共享引用访问。
                let ptr = unsafe { buckets.get_unchecked(location.bucket) }.load(Ordering::Acquire);
                self.scan += len;
                if !ptr.is_null() {
                    // Validated entry; Acquire observes fully initialized storage.
                    self.ptr = unsafe { ptr.add(location.entry) };
                    self.remaining = len;
                    return true;
                }
            }
        }
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
        Some(ptr)
    }

    fn next_segment(&mut self) -> Option<(*mut T, usize)> {
        if self.remaining == 0 && !self.advance() {
            return None;
        }
        let segment = (self.ptr, self.remaining);
        self.remaining = 0;
        Some(segment)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // 当前段保证可返回；尚未扫描的桶跨度（含空桶）仅计入上界。
        // 总和不超过已验证的原始范围长度，不会溢出。
        (
            self.remaining,
            Some(self.remaining + (self.end - self.scan)),
        )
    }
}

/// 共享元素迭代器，按逻辑索引递增并跳过未分配桶，包含已分配桶中的默认值。
/// 不是分配快照：访问后续桶前的新分配可能可见。
pub struct BucketIter<'a, T> {
    cursor: SegmentCursor<'a, T>,
}
impl<'a, T> BucketIter<'a, T> {
    /// 创建不借用任何桶或前缀的空迭代器，剩余元素数为零。
    pub fn empty() -> Self {
        Self {
            cursor: SegmentCursor::new(NonNull::dangling().as_ptr(), 0, None, 0..0),
        }
    }
    /// 在绝对半开范围内先读取前缀，再读取偏移为 `prefix.len()` 的桶元素。
    /// 返回引用借用前缀和对象槽至 `'a`，未分配桶会跳过，不触发分配。
    /// `start > end` 或 `end.saturating_sub(prefix.len()) > MAX_ENTRIES + 1` 时 panic。
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
    /// 从借用的原始前缀和对象槽构造共享迭代器，不取得前缀的所有权。
    /// 绝对半开范围、桶偏移和 panic 条件与 [`Self::with_prefix`] 相同，
    /// 其中前缀长度使用 `prefix_len`；范围内未分配桶会跳过。
    ///
    /// # Safety
    /// `prefix_len != 0` 时，`prefix` 须非空、对齐，并指向单一分配内
    /// `prefix_len` 个已初始化的有效 `T`，总字节数不得超过 `isize::MAX`。
    /// 前缀须在整个 `'a` 内保持有效，不得释放或移动；对象槽也借用至 `'a`。
    /// 迭代器可能读取的元素及其返回引用存活期间，不得有冲突的整元素可变引用，
    /// 也不得在 `UnsafeCell` 外修改元素。允许遵守内部可变性契约且经必要同步的
    /// `UnsafeCell` 内部修改；跨线程访问须避免数据竞争，同步不能豁免引用别名规则。
    /// `prefix_len == 0` 时允许空指针，不进行前缀指针运算或解引用。
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
    /// 将尚未返回的元素改为按连续非空切片迭代，保留范围和当前游标。
    /// 不复制、不重新分配；切片借用至 `'a`，此前返回的共享引用仍有效。
    pub fn into_segments(self) -> BucketSegments<'a, T> {
        BucketSegments {
            cursor: self.cursor,
        }
    }
}
impl<'a, T> Iterator for BucketIter<'a, T> {
    type Item = &'a T;
    /// 返回下一个已分配元素的共享引用，跳过空桶；范围耗尽时返回 `None`。
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Cursor only visits initialized storage borrowed for 'a.
        self.cursor.next_ptr().map(|ptr| unsafe { &*ptr })
    }
    /// 下界为当前段剩余元素数，上界为剩余逻辑跨度（包括未分配桶）。
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.cursor.size_hint()
    }
}

/// 独占元素迭代器，按索引递增跳过未分配桶，每个元素至多返回一次。
/// 对象槽的独占借用覆盖迭代器和所返回引用的生命周期。
pub struct BucketIterMut<'a, T> {
    cursor: SegmentCursor<'a, T>,
    exclusive: PhantomData<&'a mut T>,
}
impl<'a, T> Iterator for BucketIterMut<'a, T> {
    type Item = &'a mut T;
    /// 返回下一个元素的独占引用，每个元素至多一次；范围耗尽时返回 `None`。
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // Exclusive borrow; each entry is visited only once, even across gaps.
        self.cursor.next_ptr().map(|ptr| unsafe { &mut *ptr })
    }
    /// 下界为当前段剩余元素数，上界为剩余逻辑跨度（包括未分配桶）。
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.cursor.size_hint()
    }
}

/// 共享连续段迭代器，返回按前缀或桶边界裁剪的非空切片，跳过未分配桶。
/// 切片借用至 `'a`；后续桶的并发分配可能可见，不构成快照。
pub struct BucketSegments<'a, T> {
    cursor: SegmentCursor<'a, T>,
}
impl<'a, T> Iterator for BucketSegments<'a, T> {
    type Item = &'a [T];
    /// 返回下一个非空共享连续段，跳过空桶；范围耗尽时返回 `None`。
    fn next(&mut self) -> Option<Self::Item> {
        // Each nonempty span is initialized, contiguous, and borrowed for 'a.
        self.cursor
            .next_segment()
            .map(|(ptr, len)| unsafe { std::slice::from_raw_parts(ptr, len) })
    }
    /// 当前段非空时段数下界为一，否则为零；上界为剩余逻辑跨度。
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            usize::from(self.cursor.remaining != 0),
            self.cursor.size_hint().1,
        )
    }
}
/// 独占连续段迭代器，返回非空且互不重叠的桶切片，跳过未分配桶。
/// 对象槽的独占借用覆盖迭代器和所返回切片的生命周期。
pub struct BucketSegmentsMut<'a, T> {
    cursor: SegmentCursor<'a, T>,
    exclusive: PhantomData<&'a mut T>,
}
impl<'a, T> Iterator for BucketSegmentsMut<'a, T> {
    type Item = &'a mut [T];
    /// 返回下一个非空独占连续段，各段互不重叠；范围耗尽时返回 `None`。
    fn next(&mut self) -> Option<Self::Item> {
        // Exclusive self borrow and disjoint, one-time segment visitation.
        self.cursor
            .next_segment()
            .map(|(ptr, len)| unsafe { std::slice::from_raw_parts_mut(ptr, len) })
    }
    /// 当前段非空时段数下界为一，否则为零；上界为剩余逻辑跨度。
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            usize::from(self.cursor.remaining != 0),
            self.cursor.size_hint().1,
        )
    }
}
