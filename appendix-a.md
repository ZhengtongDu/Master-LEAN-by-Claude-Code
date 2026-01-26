# 附录 A：常用策略速查表

## 本附录概要

本附录提供 LEAN 4 中常用策略的快速参考，按功能分类整理，方便读者在编写证明时快速查阅。

---

## 基础策略

| 策略 | 说明 | 示例 |
|------|------|------|
| `intro h` | 引入假设或参数 | 将 `∀ x, P x` 变为 `P x` |
| `exact e` | 直接提供证明项 | `exact h` |
| `apply f` | 应用函数或引理 | `apply Nat.add_comm` |
| `assumption` | 自动从假设中寻找 | - |
| `trivial` | 证明平凡命题 | - |

---

## 逻辑策略

| 策略 | 说明 | 示例 |
|------|------|------|
| `constructor` | 构造合取或存在 | 将 `P ∧ Q` 分为两个目标 |
| `left` / `right` | 选择析取分支 | `left` 证明 `P ∨ Q` 的左边 |
| `cases h` | 对假设进行情况分析 | - |
| `rcases h with ⟨a, b⟩` | 递归模式匹配 | - |
| `obtain ⟨x, hx⟩ := h` | 从存在量词提取 | - |
| `use x` | 提供存在量词的见证 | - |
| `exfalso` | 转为证明 `False` | - |
| `by_contra h` | 反证法 | - |

---

## 重写与化简

| 策略 | 说明 | 示例 |
|------|------|------|
| `rw [h]` | 使用 h 重写目标 | - |
| `rw [← h]` | 反向重写 | - |
| `simp` | 自动化简 | - |
| `simp [h]` | 使用额外引理化简 | - |
| `simp only [h]` | 仅使用指定引理 | - |
| `norm_num` | 数值计算 | `norm_num` 证明 `2 + 2 = 4` |
| `ring` | 环论自动证明 | `ring` 证明 `(a+b)^2 = a^2+2*a*b+b^2` |
| `field_simp` | 分式化简 | - |

---

## 归纳与递归

| 策略 | 说明 | 示例 |
|------|------|------|
| `induction n` | 对 n 进行归纳 | - |
| `induction n with ...` | 指定归纳变量名 | - |
| `cases n` | 情况分析（不带归纳假设） | - |

---

## 自动化策略

| 策略 | 说明 | 示例 |
|------|------|------|
| `decide` | 可判定命题自动证明 | - |
| `omega` | 线性算术自动证明 | - |
| `aesop` | 高级自动化搜索 | - |
| `linarith` | 线性算术（需 Mathlib） | - |
| `nlinarith` | 非线性算术（需 Mathlib） | - |

---

## 搜索策略（需 Mathlib）

| 策略 | 说明 |
|------|------|
| `exact?` | 搜索精确匹配的引理 |
| `apply?` | 搜索可应用的引理 |
| `rw?` | 搜索可重写的引理 |

---

## 组合策略

| 语法 | 说明 |
|------|------|
| `t1 <;> t2` | 对 t1 产生的所有目标应用 t2 |
| `· t` | 聚焦当前目标 |
| `repeat t` | 重复应用 t 直到失败 |
| `first \| t1 \| t2` | 尝试 t1，失败则尝试 t2 |
| `try t` | 尝试 t，失败也继续 |
| `all_goals t` | 对所有目标应用 t |

---

## 辅助策略

| 策略 | 说明 |
|------|------|
| `have h : P := ...` | 引入辅助命题 |
| `let x := ...` | 引入辅助定义 |
| `show P` | 明确当前目标 |
| `suffices h : P` | 转为证明充分条件 |
| `calc` | 计算式证明 |
| `conv => ...` | 精确控制重写位置 |

---

## 延伸阅读

- [LEAN 4 官方策略文档](https://leanprover.github.io/lean4/doc/tactics.html)
- [Mathlib 策略文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic.html)
