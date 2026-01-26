# 第十二章：Mathlib 入门

## 本章概要

本章介绍 Mathlib——LEAN 最重要的数学库。Mathlib 包含了大量形式化的数学知识，学会使用 Mathlib 是进行严肃数学形式化的必备技能。

---

## 12.1 Mathlib 简介与安装

### 内容点
- Mathlib 的历史与规模
- Mathlib 4 的迁移
- 如何添加 Mathlib 依赖
- 获取缓存的编译结果
- Mathlib 的版本管理

### Toy Case 简介
**配置 Mathlib 项目**：创建一个使用 Mathlib 的新项目，验证安装成功。

---

## 12.2 Mathlib 的组织结构

### 内容点
- 目录结构概览
- 主要模块：Algebra、Analysis、Topology、NumberTheory 等
- 命名规范
- 文件组织逻辑
- 如何导航 Mathlib

### Toy Case 简介
**浏览 Mathlib**：使用 VS Code 浏览 Mathlib 源码，找到群论相关定义。

---

## 12.3 查找引理：exact?、apply?、rw?

### 内容点
- `exact?`：查找精确匹配的引理
- `apply?`：查找可应用的引理
- `rw?`：查找可重写的引理
- 其他搜索策略
- 在线文档与搜索工具

### Toy Case 简介
**引理搜索实战**：使用搜索策略找到证明 `a + b = b + a` 的引理。

---

## 12.4 Mathlib 命名规范

### 内容点
- 引理命名规则
- 常见前缀和后缀
- 类型名称约定
- 如何猜测引理名称
- 命名中的缩写

### Toy Case 简介
**名称猜测练习**：给定一个数学事实，猜测它在 Mathlib 中的名称。

---

## 12.5 阅读 Mathlib 源码

### 内容点
- 为什么要阅读源码
- 理解 Mathlib 的证明风格
- 跟踪定义和依赖
- 学习惯用模式
- 为贡献做准备

### Toy Case 简介
**源码阅读**：阅读 `Nat.add_comm` 的证明，理解其结构。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
