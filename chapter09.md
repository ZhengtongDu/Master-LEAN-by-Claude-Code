# 第九章：结构与类型类

## 本章概要

本章介绍 LEAN 的结构体和类型类系统。类型类是 LEAN 中实现多态和代码复用的重要机制，也是 Mathlib 组织数学结构的基础。

---

## 9.1 结构体（structure）详解

### 内容点
- `structure` 关键字定义
- 字段和默认值
- 继承（extends）
- 匿名构造器语法
- 字段访问和更新

### Toy Case 简介
**定义点结构**：定义一个二维点 `Point` 结构体，包含 x 和 y 坐标字段。

---

## 9.2 类型类（class）机制

### 内容点
- 类型类的概念与动机
- `class` 关键字
- 类型类 vs 结构体
- 方法（method）的定义
- 实例搜索机制

### Toy Case 简介
**定义 Printable 类型类**：定义一个 `Printable` 类型类，包含 `toString` 方法。

---

## 9.3 实例（instance）的定义与推断

### 内容点
- `instance` 关键字
- 实例优先级
- 实例参数
- 实例的自动推断
- 调试实例搜索

### Toy Case 简介
**为自定义类型实现实例**：为 `Point` 实现 `Printable` 和 `BEq` 实例。

---

## 9.4 常用类型类：Inhabited、BEq、Ord、Hashable

### 内容点
- `Inhabited`：默认值
- `BEq`：相等性比较
- `Ord`：排序
- `Hashable`：哈希
- `ToString` 与 `Repr`

### Toy Case 简介
**完整的类型类实现**：为一个自定义数据类型实现完整的常用类型类。

---

## 9.5 代数结构的类型类层次

### 内容点
- 代数结构层次：Semigroup → Monoid → Group
- Mathlib 中的类型类设计
- 加法与乘法版本
- 通过类型类表达数学定律
- 实例的自动继承

### Toy Case 简介
**定义幺半群**：为自然数定义 `Monoid` 实例，展示代数结构的类型类表示。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
