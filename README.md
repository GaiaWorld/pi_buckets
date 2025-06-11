# pi_buckets - 自动扩展的并发存储桶

[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](https://github.com/yourusername/pi_buckets)
[![Rust](https://img.shields.io/badge/rust-nightly-red.svg)](https://www.rust-lang.org)

`pi_buckets` 是一个为高并发场景设计的无锁、自动扩展的存储桶集合库。它提供了一种独特的动态存储方法，避免了昂贵的重分配操作，同时保持线程安全。

## 主要特性

- **自动扩展的存储桶**：当现有桶填满时自动创建新桶
- **无锁读取**：支持并发读取而无需阻塞
- **线程安全的写入**：安全的并发修改操作
- **固定桶大小**：每个桶都是固定大小的 `Vec`，永不调整大小
- **高效迭代**：以最小开销遍历所有元素
- **最小化分配**：仅在需要时分配存储桶
- **超大容量**：支持最多 `u32::MAX - 32` 个元素

## 设计原理

`Buckets<T>` 结构由多个固定大小的存储桶组成：
- 第一个桶：32 个元素
- 后续每个桶：前一个桶大小的两倍
- 当一个桶填满时，会分配一个新桶
- 桶永远不会调整大小 - 新元素会放入新桶中

这种设计避免了传统向量昂贵的重分配成本，同时保持了 O(1) 的访问时间复杂度。

## 性能特点

存储桶迭代比 `Vec` 迭代慢 1-10 倍，原因包括：
- 切换桶时的原子操作
- 跨桶边界时的缓存失效
- 这种折衷是为了实现无需重分配的自动扩展

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
            arr.insert(&Location::of(i), i);
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

let arr = buckets![1, 2, 4, 8];

// 范围迭代
let mut slice_iter = arr.slice(1..3);
assert_eq!(slice_iter.next(), Some(&mut 2));
assert_eq!(slice_iter.next(), Some(&mut 4));
assert_eq!(slice_iter.next(), None);

// 克隆存储桶
let mut cloned = arr.clone();
cloned.set(&Location::of(0), 10);
assert_eq!(arr[0], 1); // 原始未改变
assert_eq!(cloned[0], 10); // 克隆已修改

// 元素扩展
arr.extend([16, 32, 64].iter().copied());
assert_eq!(arr[4], 16);
assert_eq!(arr[5], 32);
assert_eq!(arr[6], 64);

```

### 宏支持
`buckets!` 宏提供了方便的初始化语法：
```rust
// 创建空桶
let empty = buckets![];

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
assert_eq!(loc.bucket, 1); // 桶索引
assert_eq!(loc.entry, 1);  // 桶内位置
assert_eq!(loc.len, 64);   // 桶大小

// 位置转换
assert_eq!(loc.index(0), 33); // 绝对位置
```

## 贡献者

感谢所有为 `pi_buckets` 项目做出贡献的开发者。

## 贡献

欢迎提交问题、拉取请求和改进建议。请确保遵循项目的贡献指南。

## 许可证

本项目采用 MIT 或 Apache-2.0 许可证。请查看 `LICENSE` 文件了解更多信息。