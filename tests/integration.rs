use pi_buckets::{buckets, BucketIter, Buckets, Location, BUCKETS, MAX_ENTRIES};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};

#[test]
fn locations_and_capacity_boundaries() {
    let default = Location::default();
    assert_eq!(default, Location::new(0, 0));
    assert_eq!(default, Location::of(0));
    assert_eq!(default.bucket_index(), 0);
    assert_eq!(default.entry(), 0);
    assert_eq!(default.len(), 32);
    assert_eq!(default.index(0), 0);
    for b in 0..BUCKETS {
        let len = Location::bucket_len(b);
        let start = len - pi_buckets::SKIP;
        for index in [start, start + len - 1] {
            let loc = Location::of(index);
            assert_eq!(loc.bucket_index(), b);
            assert_eq!(loc.entry(), index - start);
            assert_eq!(loc.len(), len);
            assert_eq!(loc.index(0), index);
            assert_eq!(Location::new(b, loc.entry()), loc);
        }
        assert!(catch_unwind(|| Location::new(b, len)).is_err());
        assert!(catch_unwind(|| Location::new(b, usize::MAX)).is_err());
        assert_eq!(Location::bucket_capacity(b), start + len);
    }
    assert_eq!(Location::of(MAX_ENTRIES).entry(), (1usize << 31) - 1);
    assert!(catch_unwind(|| Location::of(MAX_ENTRIES + 1)).is_err());
    assert!(catch_unwind(|| Location::new(BUCKETS, 0)).is_err());
    assert!(catch_unwind(|| Location::new(usize::MAX, 0)).is_err());
    assert!(catch_unwind(|| Location::bucket_len(BUCKETS)).is_err());
    assert!(catch_unwind(|| Location::of(1).index(usize::MAX)).is_err());
    for (capacity, count) in [(0, 0), (1, 32), (32, 32), (33, 96), (96, 96), (97, 224)] {
        let arr = Buckets::<u8>::with_capacity(capacity);
        assert_eq!(arr.iter().count(), count);
    }
    let arr = Buckets::<u8>::new();
    assert_eq!(arr.slice(MAX_ENTRIES..MAX_ENTRIES + 1).count(), 0);
    assert_eq!(arr.slice(MAX_ENTRIES + 1..MAX_ENTRIES + 1).count(), 0);
    let reversed = std::ops::Range { start: 2, end: 1 };
    assert!(catch_unwind(|| arr.slice(reversed)).is_err());
    assert!(catch_unwind(|| arr.slice(0..MAX_ENTRIES + 2)).is_err());
    assert!(catch_unwind(|| arr.slice_row(0..1, 1)).is_err());
}

#[test]
fn shared_gaps_content_and_hints() {
    let mut arr = buckets![1, 2, 4];
    arr.set(&Location::of(98), 98);
    let mut it = arr.slice(1..100);
    assert_eq!(it.size_hint(), (31, Some(99)));
    let expected = (1..32).chain(96..100).map(|i| arr[i]).collect::<Vec<_>>();
    let mut seen = Vec::new();
    loop {
        let (lower, upper) = it.size_hint();
        let actual = expected.len() - seen.len();
        assert!(lower <= actual && actual <= upper.unwrap());
        match it.next() {
            Some(value) => seen.push(*value),
            None => break,
        }
    }
    assert_eq!(seen, expected);
    assert_eq!(seen[31], 0);
    assert_eq!(seen[33], 98);
    assert_eq!(it.size_hint(), (0, Some(0)));
    assert_eq!(it.next(), None);
    // Shared iterators may coexist and their yielded values remain shared.
    let first = arr.iter().next().unwrap();
    assert_eq!(arr.iter().next(), Some(first));
}

#[test]
fn prefix_within_crossing_empty_and_raw() {
    let arr = buckets![10, 11, 12];
    let prefix = [1, 2, 3];
    assert_eq!(
        BucketIter::with_prefix(&prefix, &arr, 1..3)
            .copied()
            .collect::<Vec<_>>(),
        [2, 3]
    );
    assert_eq!(
        BucketIter::with_prefix(&prefix, &arr, 2..6)
            .copied()
            .collect::<Vec<_>>(),
        [3, 10, 11, 12]
    );
    assert_eq!(
        BucketIter::with_prefix(&[], &arr, 0..3)
            .copied()
            .collect::<Vec<_>>(),
        [10, 11, 12]
    );
    assert_eq!(BucketIter::with_prefix(&prefix, &arr, 3..3).count(), 0);
    assert_eq!(
        BucketIter::with_prefix(&prefix, &arr, 3..6)
            .copied()
            .collect::<Vec<_>>(),
        [10, 11, 12]
    );
    // Prefix is initialized and remains immutably borrowed through the iterator.
    let it = unsafe { BucketIter::from_raw_prefix(prefix.as_ptr(), prefix.len(), &arr, 1..5) };
    assert_eq!(it.copied().collect::<Vec<_>>(), [2, 3, 10, 11]);
    let it = unsafe { BucketIter::from_raw_prefix(std::ptr::null(), 0, &arr, 0..0) };
    assert_eq!(it.count(), 0);
    assert_eq!(
        arr.slice_row(3..6, 3).copied().collect::<Vec<_>>(),
        [10, 11, 12]
    );
    let mut within = BucketIter::with_prefix(&prefix, &arr, 1..3);
    assert_eq!(within.size_hint(), (2, Some(2)));
    assert_eq!(within.next(), Some(&2));
    assert_eq!(within.size_hint(), (1, Some(1)));
    let mut parts = within.into_segments();
    assert_eq!(parts.size_hint(), (1, Some(1)));
    assert_eq!(parts.next(), Some(&[3][..]));
    assert_eq!(parts.size_hint(), (0, Some(0)));
    assert_eq!(parts.next(), None);

    let mut crossing = BucketIter::with_prefix(&prefix, &arr, 1..6);
    assert_eq!(crossing.size_hint(), (2, Some(5)));
    assert_eq!(crossing.next(), Some(&2));
    assert_eq!(crossing.size_hint(), (1, Some(4)));
    let mut parts = crossing.into_segments();
    assert_eq!(parts.size_hint(), (1, Some(4)));
    assert_eq!(parts.next(), Some(&[3][..]));
    assert_eq!(parts.size_hint(), (0, Some(3)));
    assert_eq!(parts.next(), Some(&[10, 11, 12][..]));
    assert_eq!(parts.size_hint(), (0, Some(0)));
    assert_eq!(parts.next(), None);

    let mut crossing = BucketIter::with_prefix(&prefix, &arr, 2..6);
    assert_eq!(crossing.next(), Some(&3));
    assert_eq!(crossing.size_hint(), (0, Some(3)));
    assert_eq!(crossing.next(), Some(&10));
    assert_eq!(crossing.size_hint(), (2, Some(2)));
    let mut parts = crossing.into_segments();
    assert_eq!(parts.size_hint(), (1, Some(2)));
    assert_eq!(parts.next(), Some(&[11, 12][..]));
    assert_eq!(parts.size_hint(), (0, Some(0)));
    assert_eq!(parts.next(), None);

    for range in [1..1, 3..3, 6..6] {
        let mut empty = BucketIter::with_prefix(&prefix, &arr, range);
        assert_eq!(empty.size_hint(), (0, Some(0)));
        assert_eq!(empty.next(), None);
        let mut parts = empty.into_segments();
        assert_eq!(parts.size_hint(), (0, Some(0)));
        assert_eq!(parts.next(), None);
    }
    let reversed = std::ops::Range { start: 2, end: 1 };
    assert!(catch_unwind(|| BucketIter::with_prefix(&prefix, &arr, reversed)).is_err());
    assert!(catch_unwind(|| {
        BucketIter::with_prefix(&prefix, &arr, 0..prefix.len() + MAX_ENTRIES + 2)
    })
    .is_err());
}

#[test]
fn segment_slices_and_exclusive_iteration() {
    let mut arr = Buckets::<usize>::with_capacity(97);
    for (i, value) in arr.iter_mut().enumerate() {
        *value = i;
    }
    let parts = arr.segments(30..99).collect::<Vec<_>>();
    assert_eq!(
        parts.iter().map(|part| part.len()).collect::<Vec<_>>(),
        [2, 64, 3]
    );
    assert_eq!(parts.concat(), (30..99).collect::<Vec<_>>());
    let prefix = [300, 301];
    let parts = BucketIter::with_prefix(&prefix, &arr, 1..5)
        .into_segments()
        .collect::<Vec<_>>();
    assert_eq!(parts, [&[301][..], &[0, 1, 2][..]]);
    {
        let mut mutable = arr.slice_mut(31..34);
        let a = mutable.next().unwrap();
        let b = mutable.next().unwrap();
        *a = 700;
        *b = 701;
    }
    assert_eq!((arr[31], arr[32]), (700, 701));
    for part in arr.segments_mut(30..99) {
        part.fill(9);
    }
    assert!(arr.slice(30..99).all(|x| *x == 9));
    let mut gaps = Buckets::<usize>::new();
    gaps.set(&Location::of(98), 8);
    assert_eq!(
        gaps.segments(0..100)
            .map(|part| part.len())
            .collect::<Vec<_>>(),
        [4]
    );
    let mut mutable = gaps.slice_mut(0..100);
    assert_eq!(mutable.size_hint(), (4, Some(4)));
    assert_eq!(mutable.next(), Some(&mut 0));
    assert_eq!(mutable.size_hint(), (3, Some(3)));
    assert_eq!(mutable.map(|value| *value).collect::<Vec<_>>(), [0, 8, 0]);
    let mut parts = gaps.segments_mut(0..100);
    assert_eq!(parts.size_hint(), (1, Some(4)));
    assert_eq!(parts.next().unwrap(), [0, 0, 8, 0]);
    assert_eq!(parts.size_hint(), (0, Some(0)));
    assert_eq!(parts.next(), None);
}

#[test]
fn empty_iterators_and_zst() {
    let mut empty = BucketIter::<usize>::empty();
    assert_eq!(empty.size_hint(), (0, Some(0)));
    assert_eq!(empty.next(), None);
    assert_eq!(empty.into_segments().count(), 0);
    let mut arr = Buckets::<()>::with_capacity(33);
    assert_eq!(arr.iter().count(), 96);
    assert_eq!(arr.iter_mut().collect::<Vec<_>>().len(), 96);
    assert_eq!(arr.clone().take().iter().map(Vec::len).sum::<usize>(), 96);
    assert_eq!(Buckets::<u8>::new().iter().count(), 0);
}

static LIVE: AtomicUsize = AtomicUsize::new(0);
static DEFAULTS: AtomicUsize = AtomicUsize::new(0);
static CLONES: AtomicUsize = AtomicUsize::new(0);
static PANIC_DEFAULT: AtomicUsize = AtomicUsize::new(usize::MAX);
static PANIC_CLONE: AtomicUsize = AtomicUsize::new(usize::MAX);
struct Tracked {
    _value: usize,
}
impl Default for Tracked {
    fn default() -> Self {
        let n = DEFAULTS.fetch_add(1, Ordering::SeqCst);
        assert_ne!(n, PANIC_DEFAULT.load(Ordering::SeqCst), "default panic");
        LIVE.fetch_add(1, Ordering::SeqCst);
        Self { _value: 1 }
    }
}
impl Clone for Tracked {
    fn clone(&self) -> Self {
        let n = CLONES.fetch_add(1, Ordering::SeqCst);
        assert_ne!(n, PANIC_CLONE.load(Ordering::SeqCst), "clone panic");
        LIVE.fetch_add(1, Ordering::SeqCst);
        Self {
            _value: self._value,
        }
    }
}
impl Drop for Tracked {
    fn drop(&mut self) {
        LIVE.fetch_sub(1, Ordering::SeqCst);
    }
}

// All counter scenarios run in one test so they cannot race other counter tests.
#[test]
fn panic_raii_poison_recovery_and_destructors() {
    PANIC_DEFAULT.store(40, Ordering::SeqCst);
    assert!(catch_unwind(|| Buckets::<Tracked>::with_capacity(33)).is_err());
    assert_eq!(LIVE.load(Ordering::SeqCst), 0);
    PANIC_DEFAULT.store(usize::MAX, Ordering::SeqCst);
    let mut arr = Buckets::<Tracked>::with_capacity(33);
    assert_eq!(LIVE.load(Ordering::SeqCst), 96);
    PANIC_CLONE.store(40, Ordering::SeqCst);
    let source_ref = arr.get(&Location::of(0)).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| arr.clone())).is_err());
    assert_eq!(LIVE.load(Ordering::SeqCst), 96);
    assert!(std::ptr::eq(source_ref, arr.get(&Location::of(0)).unwrap()));
    assert_eq!(arr.iter().count(), 96);
    PANIC_CLONE.store(usize::MAX, Ordering::SeqCst);
    let clone = arr.clone();
    assert_eq!(LIVE.load(Ordering::SeqCst), 192);
    drop(clone);
    let detached = arr.take();
    assert_eq!(arr.iter().count(), 0);
    drop(arr);
    assert_eq!(LIVE.load(Ordering::SeqCst), 96);
    drop(detached);
    assert_eq!(LIVE.load(Ordering::SeqCst), 0);
    let arr = Buckets::<Tracked>::new();
    PANIC_DEFAULT.store(DEFAULTS.load(Ordering::SeqCst) + 3, Ordering::SeqCst);
    assert!(catch_unwind(AssertUnwindSafe(|| arr.load_alloc_bucket(&Location::of(0)))).is_err());
    assert_eq!(LIVE.load(Ordering::SeqCst), 0);
    PANIC_DEFAULT.store(usize::MAX, Ordering::SeqCst);
    arr.load_alloc_bucket(&Location::of(0));
    assert_eq!(arr.iter().count(), 32);
    drop(arr);
    assert_eq!(LIVE.load(Ordering::SeqCst), 0);
}

#[test]
fn concurrent_first_allocation_and_read_publication() {
    let arr = Arc::new(Buckets::<usize>::new());
    let barrier = Arc::new(Barrier::new(5));
    let done = Arc::new(AtomicBool::new(false));
    let mut threads = Vec::new();
    for _ in 0..4 {
        let arr = arr.clone();
        let barrier = barrier.clone();
        threads.push(std::thread::spawn(move || {
            barrier.wait();
            let ptr = arr.load_alloc_bucket(&Location::of(0));
            assert_eq!(arr.get(&Location::of(31)), Some(&0));
            assert_eq!(arr.slice(0..32).count(), 32);
            ptr as usize
        }));
    }
    let reader = {
        let arr = arr.clone();
        let done = done.clone();
        std::thread::spawn(move || {
            while !done.load(Ordering::Acquire) {
                if let Some(value) = arr.get(&Location::of(0)) {
                    assert_eq!(*value, 0);
                }
                for value in arr.slice(0..32) {
                    assert_eq!(*value, 0);
                }
            }
        })
    };
    barrier.wait();
    let addresses = threads
        .into_iter()
        .map(|thread| thread.join().unwrap())
        .collect::<Vec<_>>();
    done.store(true, Ordering::Release);
    reader.join().unwrap();
    assert!(addresses.iter().all(|address| *address == addresses[0]));
}

#[test]
fn unsafe_shared_mutation_and_raw_allocation() {
    let arr = Buckets::<usize>::new();
    let location = Location::of(2);
    assert!(unsafe { arr.load(&location) }.is_none());
    // Each mutable borrow ends before any subsequent access; no other threads.
    unsafe {
        *arr.load_alloc(&location) = 7;
        assert_eq!(arr.insert(&location, 8), 7);
        *arr.load_unchecked(&location) = 9;
    }
    assert_eq!(arr.get(&location), Some(&9));
    assert_eq!(unsafe { arr.get_unchecked(&location) }, &9);
    let raw = pi_buckets::bucket_alloc::<usize>(3);
    // Raw allocation transfers ownership, initialized with an exact slice layout.
    let owned = unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(raw, 3)) };
    assert_eq!(&*owned, &[0, 0, 0]);
}
