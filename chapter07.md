# 第七章：策略式证明（Tactics）

## 本章概要

本章全面介绍 LEAN 4 的策略式证明系统。策略（Tactics）提供了一种交互式的证明方式，通过逐步转换目标来完成证明，是处理复杂证明的主要手段。

---

## 7.1 策略模式入门

### 内容点
- 什么是策略（Tactic）
- `by` 关键字进入策略模式
- 证明状态（Proof State）的理解
- Goals 窗口的使用
- 策略的基本工作流程

### Toy Case 简介
**第一个策略证明**：使用 `by exact` 完成一个简单证明，观察证明状态的变化。

---

## 7.2 基础策略：intro、apply、exact

### 内容点
- `intro`：引入假设
- `apply`：应用引理或假设
- `exact`：直接给出证明项
- `assumption`：自动搜索假设
- `refine`：带占位符的 apply

### Toy Case 简介
**证明蕴含**：使用 `intro` 和 `exact` 证明 `P → P`。

---

## 7.3 逻辑策略：constructor、cases、rcases

### 内容点
- `constructor`：构造合取/存在
- `cases`：情况分析
- `rcases`：递归模式匹配
- `obtain`：从存在量词提取
- `left`、`right`：选择析取分支

### Toy Case 简介
**析取的情况分析**：证明 `P ∨ Q → Q ∨ P`。

---

## 7.4 重写策略：rw、simp、ring

### 内容点
- `rw`：基于等式重写
- `simp`：自动化简化
- `ring`：环论自动证明
- `norm_num`：数值计算
- `field_simp`：分式化简

### Toy Case 简介
**代数化简**：使用 `ring` 证明 `(a + b)^2 = a^2 + 2*a*b + b^2`。

---

## 7.5 自动化策略：decide、trivial、aesop

### 内容点
- `decide`：可判定命题的自动证明
- `trivial`：平凡证明
- `aesop`：高级自动化搜索
- `omega`：线性算术自动证明
- 自动化策略的适用范围

### Toy Case 简介
**自动证明**：使用 `decide` 证明 `2 + 2 = 4`，使用 `omega` 证明算术不等式。

---

## 7.6 组合策略：<;>、·、repeat、first

### 内容点
- `<;>`：对所有目标应用策略
- `·`：聚焦单个目标
- `repeat`：重复应用策略
- `first`：尝试多个策略
- `try`：允许失败的策略
- `all_goals`：对所有目标应用

### Toy Case 简介
**策略组合**：使用 `repeat` 和 `constructor` 一次性完成多个子目标的证明。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
