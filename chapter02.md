# 第二章：环境搭建与工具链

## 本章概要

本章将指导读者完成 LEAN 4 开发环境的搭建，包括安装 LEAN 和相关工具、配置编辑器、创建项目等，为后续学习打下基础。

---

## 2.1 安装 LEAN 4 和 elan

### 内容点
- elan：LEAN 的版本管理器
- 各平台安装方法（macOS、Linux、Windows）
- 验证安装是否成功
- 管理多个 LEAN 版本

### Toy Case 简介
**安装验证**：运行 `lean --version` 和 `elan show`，确认环境配置正确。

---

## 2.2 配置 VS Code 开发环境

### 内容点
- 安装 VS Code
- 安装 lean4 扩展
- 扩展功能介绍：语法高亮、错误提示、InfoView
- 自定义配置选项

### Toy Case 简介
**InfoView 探索**：在 VS Code 中打开一个 LEAN 文件，观察 InfoView 如何实时显示类型信息和证明状态。

---

## 2.3 创建第一个 LEAN 项目

### 内容点
- 使用 `lake new` 创建项目
- 项目目录结构解析
- `lakefile.lean` 配置文件
- 添加依赖（如 Mathlib）

### Toy Case 简介
**创建并运行项目**：从零创建一个 LEAN 项目，添加一个简单的定理并编译运行。

---

## 2.4 Lake 构建系统详解

### 内容点
- Lake 的设计理念
- 常用 Lake 命令：build、clean、update
- 配置多模块项目
- 自定义构建脚本

### Toy Case 简介
**多模块项目**：创建一个包含多个文件的项目，理解模块间的依赖关系。

---

## 2.5 常用命令与快捷键

### 内容点
- LEAN 命令：`#check`、`#eval`、`#print`、`#reduce`
- VS Code 快捷键大全
- 调试技巧：查看类型、展开定义
- 使用 Unicode 符号输入

### Toy Case 简介
**命令速查**：使用各种 LEAN 命令探索标准库中的定义，如 `#check Nat.add`、`#print Nat`。

---

## 本章小结

（待编写）

## 练习题

（待编写）

## 延伸阅读

（待编写）
