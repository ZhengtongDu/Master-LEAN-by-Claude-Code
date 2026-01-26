# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 项目概述

本项目是一份《LEAN从入门到精通》中文教程，目标读者是具有高等数学背景和基本编程/数据结构知识的研究生。

github仓库：git@github.com:ZhengtongDu/Master-LEAN-by-Claude-Code.git

## 项目结构

- `index.md` - 教程目录和章节索引
- `chapter01.md` ~ `chapter17.md` - 各章节内容
- `appendix-a.md` ~ `appendix-d.md` - 附录内容
- `_sidebar.md` - docsify 侧边栏配置

## 写作规范

- **语言**: 所有文档使用中文撰写，交流可以用英文
- **格式**: 使用 Markdown 格式
- **内容定位**: 要经常写一些toy case的代码，专注于讲解 LEAN 的原理、使用技巧
- **目标**: 帮助读者从入门到精通 LEAN 定理证明器

## Current Task

刚刚修复了第一章内容的小问题，重新整理并添加交互式代码支持

## Task Queue

- [ ] 编写第三章：命题逻辑（And、Or、Not）
- [ ] 编写第四章：LEAN 核心语法
- [ ] 编写第五章：命题与逻辑
- [ ] 编写第六章：项式证明
- [ ] 编写第七章：策略式证明
- [ ] ...（后续章节）

## Completed

- [x] 2025-01-26: 创建项目结构和 docsify 配置
- [x] 2025-01-26: 生成 index.md 教程目录大纲
- [x] 2025-01-26: 细化目录内容，创建 17 个章节和 4 个附录的占位文件
- [x] 2025-01-26: 集成 LEAN 4 交互式代码功能（docsify 插件 + live.lean-lang.org）
- [x] 2025-01-26: 编写第一章：初识 LEAN 与环境搭建
- [x] 2025-01-26: 编写第二章：函数式编程与依赖类型理论基础
- [x] 2025-01-26: 整理第1章和第2章内容，清理格式，添加交互式代码支持
