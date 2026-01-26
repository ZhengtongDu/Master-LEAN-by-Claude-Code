# 附录 C：从其他证明助手迁移

## 本附录概要

本附录为有其他定理证明器经验的读者提供迁移指南，帮助他们快速适应 LEAN 4 的语法和概念。

---

## C.1 从 Coq 到 LEAN

### 概念对照

| Coq | LEAN 4 | 说明 |
|-----|--------|------|
| `Theorem` / `Lemma` | `theorem` / `lemma` | 定理声明 |
| `Definition` | `def` | 函数定义 |
| `Inductive` | `inductive` | 归纳类型 |
| `Record` | `structure` | 结构体 |
| `Class` | `class` | 类型类 |
| `Instance` | `instance` | 实例 |
| `Proof. ... Qed.` | `by ...` | 策略证明 |

### 策略对照

| Coq | LEAN 4 | 说明 |
|-----|--------|------|
| `intros` | `intro` | 引入假设 |
| `apply` | `apply` | 应用引理 |
| `exact` | `exact` | 直接给出项 |
| `rewrite` | `rw` | 重写 |
| `simpl` | `simp` | 化简 |
| `destruct` | `cases` | 情况分析 |
| `induction` | `induction` | 归纳 |
| `reflexivity` | `rfl` | 自反性 |
| `symmetry` | `symm` | 对称性 |
| `transitivity` | `trans` | 传递性 |
| `split` | `constructor` | 构造合取 |
| `left` / `right` | `left` / `right` | 析取选择 |
| `exists` | `use` | 存在见证 |

### 主要差异

1. **语法风格**：LEAN 4 更接近函数式编程语言
2. **策略语法**：LEAN 4 使用 `by` 块，不需要 `Proof. ... Qed.`
3. **项式证明**：LEAN 4 的项式证明更为自然
4. **元编程**：LEAN 4 使用 Lean 自身进行元编程，而非 OCaml/Ltac

### Toy Case 简介
**同一定理的双语版本**：展示一个简单定理在 Coq 和 LEAN 4 中的完整证明对比。

---

## C.2 从 Isabelle 到 LEAN

### 概念对照

| Isabelle | LEAN 4 | 说明 |
|----------|--------|------|
| `theorem` | `theorem` | 定理 |
| `definition` | `def` | 定义 |
| `datatype` | `inductive` | 数据类型 |
| `record` | `structure` | 记录类型 |
| `class` | `class` | 类型类 |
| `instantiation` | `instance` | 实例化 |
| `locale` | `section` + `variable` | 局部上下文 |

### 策略对照

| Isabelle | LEAN 4 | 说明 |
|----------|--------|------|
| `apply` | `apply` | 应用规则 |
| `simp` | `simp` | 自动化简 |
| `auto` | `aesop` | 自动证明 |
| `blast` | `aesop` | 自动搜索 |
| `induction` | `induction` | 归纳证明 |
| `case` | `cases` | 情况分析 |
| `have` | `have` | 辅助声明 |
| `show` | `show` | 声明目标 |

### 主要差异

1. **类型系统**：LEAN 使用依赖类型，Isabelle 使用简单类型
2. **证明风格**：Isabelle 偏好 Isar 结构化证明，LEAN 支持多种风格
3. **自动化**：Isabelle 的 `auto`/`blast` 非常强大，LEAN 的 `aesop` 在发展中
4. **工具链**：Isabelle 是独立的 IDE，LEAN 使用 VS Code

### Toy Case 简介
**Isar 到 LEAN 的翻译**：将一个 Isar 风格的证明翻译为 LEAN 4。

---

## C.3 从 LEAN 3 到 LEAN 4

### 语法变化

| LEAN 3 | LEAN 4 | 说明 |
|--------|--------|------|
| `#check` | `#check` | 相同 |
| `begin ... end` | `by ...` | 策略块 |
| `{ ... }` | `· ...` 或 `{ ... }` | 聚焦目标 |
| `λ x, ...` | `fun x => ...` | Lambda |
| `∀ x, ...` | `∀ x, ...` 或 `(x : T) → ...` | 全称 |
| `assume h` | `intro h` | 引入假设 |
| `show P, from ...` | `show P; exact ...` | 显示目标 |
| `have h : P := ...` | `have h : P := ...` | 相同 |
| `let x := ...` | `let x := ...` | 相同 |
| `calc ... : ... = ... : ...` | `calc ... = ... := ...` | 计算链 |

### 命名变化

| LEAN 3 | LEAN 4 |
|--------|--------|
| `nat` | `Nat` |
| `int` | `Int` |
| `list` | `List` |
| `nat.add_comm` | `Nat.add_comm` |

### 策略变化

| LEAN 3 | LEAN 4 | 说明 |
|--------|--------|------|
| `simp only [...]` | `simp only [...]` | 相同 |
| `rw ...` | `rw [...]` | 需要方括号 |
| `ext` | `ext` / `funext` | 外延性 |
| `split` | `constructor` | 构造合取 |
| `rcases ... with ⟨...⟩` | `rcases ... with ⟨...⟩` | 基本相同 |
| `library_search` | `exact?` | 引理搜索 |

### 自动迁移工具

- **mathport**：用于将 LEAN 3 代码自动转换为 LEAN 4
- 注意：自动转换的代码通常需要手动调整

### Toy Case 简介
**代码迁移示例**：将一段 LEAN 3 代码完整迁移到 LEAN 4。

---

## 通用建议

1. **从官方教程开始**：每个系统都有其特色，直接阅读目标系统的官方教程
2. **理解核心差异**：关注类型系统和证明风格的根本差异
3. **循序渐进**：先掌握基本语法，再学习高级特性
4. **利用社区资源**：加入相关的讨论社区寻求帮助

---

## 延伸阅读

- [Coq 官方网站](https://coq.inria.fr/)
- [Isabelle 官方网站](https://isabelle.in.tum.de/)
- [LEAN 3 到 LEAN 4 迁移指南](https://leanprover-community.github.io/mathlib4_docs/)
