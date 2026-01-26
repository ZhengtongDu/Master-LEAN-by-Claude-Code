# 第十章：Monad 与函数式编程

## 本章概要

本章介绍 LEAN 中的 Monad 和函数式编程范式。理解 Monad 对于编写实际的 LEAN 程序（而非纯证明）至关重要，也能帮助理解 LEAN 的元编程系统。

---

## 10.1 Functor、Applicative、Monad

### 内容点
- `Functor`：`map` 函数
- `Applicative`：`pure` 和 `seq`
- `Monad`：`bind` 操作
- 三者的层级关系
- Monad 定律

### Toy Case 简介
**Option Functor**：展示 `Option.map` 的使用，理解 Functor 的作用。

---

## 10.2 Option 与错误处理

### 内容点
- `Option` 类型详解
- `some` 和 `none`
- 错误处理模式
- `Option` 的 Monad 实例
- `Except` 类型与带信息的错误

### Toy Case 简介
**安全除法**：实现 `safeDiv : Nat → Nat → Option Nat`，处理除零情况。

---

## 10.3 IO Monad 与副作用

### 内容点
- 为什么需要 IO Monad
- `IO` 类型的本质
- 基本 IO 操作：读写、文件、网络
- `main` 函数
- IO 中的错误处理

### Toy Case 简介
**Hello World 程序**：编写完整的 IO 程序，读取用户输入并输出问候语。

---

## 10.4 StateM 与状态管理

### 内容点
- 状态 Monad `StateM`
- `get`、`set`、`modify`
- 模拟可变状态
- 状态与 IO 的组合
- `ReaderM` 和 `ExceptT`

### Toy Case 简介
**计数器**：使用 `StateM` 实现一个简单的计数器。

---

## 10.5 do 记法详解

### 内容点
- `do` 块的脱糖（desugaring）
- `let` 与 `let mut`
- `if`、`for`、`while` 在 do 块中
- `return` 和提前返回
- `do` 记法的高级用法

### Toy Case 简介
**命令式风格**：用 `do` 记法实现一个带循环和条件的程序。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
