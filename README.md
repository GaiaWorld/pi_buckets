# pi_buckets - 自动扩展的并发存储桶

[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](https://github.com/yourusername/pi_buckets)
[![Rust](https://img.shields.io/badge/rust-stable-green.svg)](https://www.rust-lang.org)

`pi_buckets` 是一个自动扩展的存储桶集合库，支持无锁读取，首次分配通过互斥锁串行初始化后发布。已分配元素地址保持稳定，共享引用写入要求调用方保证独占访问和线程同步。

## 主要特性

- **自动扩展的存储桶**：当现有桶填满时自动创建新桶
- **无锁读取**：支持并发读取而无需阻塞
- **独占写入**：安全修改要求 `&mut Buckets<T>`；共享引用修改接口为 `unsafe`
- **固定桶大小**：每个桶都是精确长度的 `Box<[T]>`，永不调整大小
- **高效迭代**：以最小开销遍历所有元素
- **最小化分配**：仅在需要时分配存储桶
- **超大容量**：`MAX_ENTRIES = u32::MAX - 32` 是最大索引，最大元素数量为 `MAX_ENTRIES + 1`

## 设计原理

`Buckets<T>` 结构由多个固定大小的存储桶组成：
- 第一个桶：32 个元素
- 后续每个桶：前一个桶大小的两倍
- 当一个桶填满时，会分配一个新桶
- 桶永远不会调整大小 - 新元素会放入新桶中

这种设计避免了传统向量昂贵的重分配成本，同时保持了 O(1) 的访问时间复杂度。

## 性能特点

逐元素迭代使用统一的当前连续段指针和剩余数量，只有段边界需要冷路径处理：
- 切换桶时的原子操作
- 跨桶边界时的缓存失效
- `segments(range)` 直接返回连续切片，适合批量扫描；本次修改未进行性能基准测量

## 使用示例

### 基本用法

```rust
use pi_buckets::{buckets, Location};

// 创建存储桶
let mut arr = buckets![1, 2, 3];

// 获取元素
assert_eq!(arr.get(&Location::of(1)), Some(&2));

// 设置元素
arr.set(&Location::of(1), 20);
assert_eq!(arr.get(&Location::of(1)), Some(&20));

// 自动分配
*arr.alloc(&Location::of(3)) = 4;
assert_eq!(arr.get(&Location::of(3)), Some(&4));

```

### 并发使用
```rust
use pi_buckets::{Buckets, Location};
use std::sync::Arc;

let arr = Arc::new(Buckets::new());

// 创建多个线程并发写入
let threads = (0..6)
    .map(|i| {
        let arr = arr.clone();
        std::thread::spawn(move || {
            // 每个线程只修改各自的元素，且所有读取发生在 join 之后。
            unsafe { arr.insert(&Location::of(i), i); }
        })
    })
    .collect::<Vec<_>>();

// 等待所有线程完成
for thread in threads {
    thread.join().unwrap();
}

// 验证所有写入都成功
for i in 0..6 {
    assert!(arr.iter().any(|x| *x == i));
}
```

### 高级操作

```rust
use pi_buckets::{buckets, Location};

let mut arr = buckets![1, 2, 4, 8];

// 范围迭代
let mut slice_iter = arr.slice(1..3);
assert_eq!(slice_iter.next(), Some(&2));
assert_eq!(slice_iter.next(), Some(&4));
assert_eq!(slice_iter.next(), None);

// 克隆存储桶
let mut cloned = arr.clone();
cloned.set(&Location::of(0), 10);
assert_eq!(arr[0], 1); // 原始未改变
assert_eq!(cloned[0], 10); // 克隆已修改

// 没有逻辑长度；extend 从索引零开始替换，并非追加。
arr.extend([16, 32, 64].iter().copied());
assert_eq!(arr[0], 16);
assert_eq!(arr[1], 32);
assert_eq!(arr[2], 64);

// 批量扫描连续切片，或通过独占借用修改元素。
assert_eq!(arr.segments(0..3).flatten().copied().sum::<i32>(), 112);
for value in arr.slice_mut(0..3) { *value += 1; }

```

### 宏支持
`buckets!` 宏提供了方便的初始化语法：
```rust
// 创建空桶
use pi_buckets::{buckets, Buckets};
let empty: Buckets<i32> = buckets![];

// 创建重复元素的桶
let ones = buckets![1; 3]; // [1, 1, 1]

// 从元素列表创建
let values = buckets![10, 20, 30]; // [10, 20, 30]
```

### 位置计算
`Location` 结构用于计算元素位置：

```rust
use pi_buckets::Location;

let loc = Location::of(33);
assert_eq!(loc.bucket_index(), 1); // 桶索引
assert_eq!(loc.entry(), 1);        // 桶内位置
assert_eq!(loc.len(), 64);         // 构造时推导并缓存桶大小
assert_eq!(Location::new(1, 1), loc); // 桶索引和桶内位置
assert_eq!(Location::default().len(), 32);

// 位置转换
assert_eq!(loc.index(0), 33); // 绝对位置
```

## API 迁移与安全要求

- `load`、`load_alloc`、`load_unchecked` 和 `insert` 为 `unsafe`：返回借用或替换操作期间，目标元素不能存在其他引用或并发访问，存储必须保持有效。读取迭代器和切片也会产生别名。
- `take` 要求 `&mut self`，将精确分配转换为拥有所有权的 `Vec`；不再公开原子指针表。
- `Location` 字段私有；使用 `bucket_index()`、`entry()`、`len()`。`of` 检查最大索引，`new(bucket: usize, entry: usize)` 验证桶与桶内位置；两者均在构造时推导并缓存桶长度。`Default` 为 `new(0, 0)`，桶长度为 32。
- `iter`、`slice` 返回 `&T`；可变访问使用 `iter_mut`、`slice_mut`、`segments_mut`，均要求独占借用。
- `BucketIter::with_prefix(&[T], &Buckets<T>, range)` 安全读取已初始化主数组及后续桶；`into_segments()` 返回切片迭代器。
- `BucketIter`、`BucketIterMut`、`BucketSegments` 不再提供 `index()`，不暴露绝对游标位置；`Location::index(capacity)` 保留用于位置转换。内部扫描位置和结束位置均相对于扩展桶起点，不保存前缀长度。
- 旧 `BucketIter::new` 已移除。`unsafe BucketIter::from_raw_prefix(ptr, prefix_len, buckets, range)` 要求前缀已初始化、对齐、生命周期足够且没有冲突访问；容量不等于初始化长度。
- `slice_row(range, capacity)` 仅处理桶部分，要求范围起点不在主数组内部。所有范围必须有序，桶部分的排他终点不超过 `MAX_ENTRIES + 1`。32 位计算避免移位或相加溢出。
- 未分配桶被跳过；已分配桶的所有默认元素均参与迭代。逐元素 `size_hint` 下界为当前段剩余元素，上界为当前段剩余元素加尚未扫描的桶跨度（含空桶）；前缀段也计入剩余元素。连续段迭代的下界为当前段非空时的一，否则为零，上界同为剩余逻辑元素数。未来桶的并发分配不是快照。
- `load_alloc_bucket` 仍是安全的裸指针分配接口，长度由有效 `Location` 推导；解引用必须自行满足边界、生命周期、别名和线程条件，不得释放借用指针。`bucket_alloc` 返回拥有所有权的精确长度分配，调用方负责按对应切片布局释放。
- `Buckets<T>: Sync` 要求 `T: Send + Sync`。

验证覆盖位于 `tests/integration.rs`；通过测试或 Miri 并不证明不存在未定义行为。

## 贡献者

感谢所有为 `pi_buckets` 项目做出贡献的开发者。

## 贡献

欢迎提交问题、拉取请求和改进建议。请确保遵循项目的贡献指南。

## 许可证

本项目采用 MIT 或 Apache-2.0 许可证。请查看 `LICENSE` 文件了解更多信息。
