# 第十五章：LEAN 内核原理

## 本章概要

本章深入探讨 LEAN 定理证明器的内核工作原理。理解这些原理有助于更深入地理解 LEAN 的行为，也为高级用户提供调试和优化的知识基础。

---

## 15.1 类型检查算法

### 内容点
- 双向类型检查
- 类型推断与类型综合
- 统一（Unification）算法
- 元变量与延迟求解
- 类型检查的复杂度

### Toy Case 简介
**类型推断追踪**：观察 LEAN 如何推断复杂表达式的类型。

---

## 15.2 归约与转换

### 内容点
- β-归约：函数应用
- δ-归约：定义展开
- ι-归约：递归子计算
- ζ-归约：let 表达式
- 定义相等（Definitional Equality）

### Toy Case 简介
**归约演示**：使用 `#reduce` 观察各种归约的效果。

---

## 15.3 Universe 层级

### 内容点
- Universe 的必要性
- `Type u` 与 `Prop`
- Universe 多态
- Universe 约束求解
- 避免 Universe 问题

### Toy Case 简介
**Universe 探索**：构造需要 Universe 多态的例子。

---

## 15.4 公理系统：propext、funext、Quot

### 内容点
- 命题外延性 `propext`
- 函数外延性 `funext`
- 商类型 `Quot`
- 选择公理 `Classical.choice`
- 公理的一致性

### Toy Case 简介
**函数外延性应用**：使用 `funext` 证明两个函数相等。

---

## 15.5 可信计算基础（TCB）

### 内容点
- 什么是 TCB
- LEAN 的 TCB 组成
- 内核的简洁性
- 独立检查器
- 可信度分析

### Toy Case 简介
**内核探索**：了解 LEAN 内核的规模和结构。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
