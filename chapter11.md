# 第十一章：元编程基础

## 本章概要

本章介绍 LEAN 4 的元编程系统。LEAN 4 的元编程能力是其重要特色之一，允许用户扩展语言的语法和功能，编写自定义的策略和命令。

---

## 11.1 LEAN 的元编程架构

### 内容点
- 元编程的概念
- LEAN 4 元编程的层次
- Syntax、Macro、Elab 的关系
- 元编程相关 Monad
- 元编程的应用场景

### Toy Case 简介
**探索语法树**：使用 `#check` 和相关命令查看表达式的内部表示。

---

## 11.2 语法（Syntax）与宏（Macro）

### 内容点
- 语法（Syntax）的定义
- `syntax` 和 `declare_syntax_cat`
- 宏（Macro）的定义
- `macro_rules`
- 卫生宏（Hygienic Macros）

### Toy Case 简介
**定义新符号**：定义一个宏将 `|x|` 展开为 `abs x`。

---

## 11.3 Elaboration 过程

### 内容点
- 什么是 Elaboration
- `TermElabM` Monad
- 类型推断与统一
- 隐式参数的填充
- Elaboration 的调试

### Toy Case 简介
**简单 Elaborator**：编写一个简单的 term elaborator。

---

## 11.4 编写自定义策略

### 内容点
- `TacticM` Monad
- 访问和修改证明状态
- `evalTactic` 调用其他策略
- 组合多个策略
- 策略的错误处理

### Toy Case 简介
**my_assumption 策略**：实现一个简化版的 `assumption` 策略。

---

## 11.5 编写自定义命令

### 内容点
- `CommandElabM` Monad
- 定义新命令
- 与环境的交互
- 添加声明到环境
- 命令的实际应用

### Toy Case 简介
**#hello 命令**：定义一个简单的命令 `#hello` 输出问候信息。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
