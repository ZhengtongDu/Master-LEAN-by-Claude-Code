# 附录 B：Mathlib 常用引理索引

## 本附录概要

本附录整理 Mathlib 中最常用的引理和定义，按数学领域分类，帮助读者快速定位所需的引理。

---

## 自然数 (Nat)

### 基本运算
| 引理 | 陈述 |
|------|------|
| `Nat.add_comm` | `a + b = b + a` |
| `Nat.add_assoc` | `(a + b) + c = a + (b + c)` |
| `Nat.mul_comm` | `a * b = b * a` |
| `Nat.mul_assoc` | `(a * b) * c = a * (b * c)` |
| `Nat.add_zero` | `a + 0 = a` |
| `Nat.zero_add` | `0 + a = a` |
| `Nat.mul_one` | `a * 1 = a` |
| `Nat.one_mul` | `1 * a = a` |

### 序关系
| 引理 | 陈述 |
|------|------|
| `Nat.le_refl` | `a ≤ a` |
| `Nat.lt_succ_self` | `a < a + 1` |
| `Nat.zero_le` | `0 ≤ a` |

---

## 整数 (Int)

| 引理 | 陈述 |
|------|------|
| `Int.add_comm` | `a + b = b + a` |
| `Int.neg_neg` | `-(-a) = a` |
| `Int.add_neg_cancel` | `a + (-a) = 0` |

---

## 列表 (List)

| 引理 | 陈述 |
|------|------|
| `List.length_append` | `(xs ++ ys).length = xs.length + ys.length` |
| `List.reverse_reverse` | `xs.reverse.reverse = xs` |
| `List.map_append` | `(xs ++ ys).map f = xs.map f ++ ys.map f` |
| `List.filter_append` | `(xs ++ ys).filter p = xs.filter p ++ ys.filter p` |

---

## 逻辑

| 引理 | 陈述 |
|------|------|
| `And.intro` | `P → Q → P ∧ Q` |
| `And.left` | `P ∧ Q → P` |
| `And.right` | `P ∧ Q → Q` |
| `Or.inl` | `P → P ∨ Q` |
| `Or.inr` | `Q → P ∨ Q` |
| `not_not` | `¬¬P ↔ P` (经典逻辑) |
| `em` | `P ∨ ¬P` (排中律) |

---

## 相等性

| 引理 | 陈述 |
|------|------|
| `Eq.refl` | `a = a` |
| `Eq.symm` | `a = b → b = a` |
| `Eq.trans` | `a = b → b = c → a = c` |
| `congrArg` | `a = b → f a = f b` |

---

## 群论（需 Mathlib）

| 引理 | 陈述 |
|------|------|
| `mul_one` | `a * 1 = a` |
| `one_mul` | `1 * a = a` |
| `mul_inv_cancel` | `a * a⁻¹ = 1` |
| `inv_mul_cancel` | `a⁻¹ * a = 1` |
| `mul_assoc` | `(a * b) * c = a * (b * c)` |

---

## 环论（需 Mathlib）

| 引理 | 陈述 |
|------|------|
| `add_mul` | `(a + b) * c = a * c + b * c` |
| `mul_add` | `a * (b + c) = a * b + a * c` |
| `mul_zero` | `a * 0 = 0` |
| `zero_mul` | `0 * a = 0` |
| `neg_mul` | `(-a) * b = -(a * b)` |

---

## 实数分析（需 Mathlib）

### 极限
| 引理 | 陈述 |
|------|------|
| `tendsto_const` | 常数列收敛到自身 |
| `Tendsto.add` | 极限的加法 |
| `Tendsto.mul` | 极限的乘法 |

### 连续性
| 引理 | 陈述 |
|------|------|
| `Continuous.comp` | 连续函数的复合连续 |
| `continuous_id` | 恒等函数连续 |
| `continuous_const` | 常函数连续 |

### 微分
| 引理 | 陈述 |
|------|------|
| `HasDerivAt.add` | 导数的加法法则 |
| `HasDerivAt.mul` | 导数的乘法法则 |
| `HasDerivAt.comp` | 链式法则 |

---

## 如何查找引理

1. **使用搜索策略**：`exact?`、`apply?`、`rw?`
2. **猜测名称**：遵循 Mathlib 命名规范
3. **在线文档**：[Mathlib 4 文档](https://leanprover-community.github.io/mathlib4_docs/)
4. **VS Code 自动补全**：输入部分名称后查看建议

---

## 延伸阅读

- [Mathlib 命名规范](https://leanprover-community.github.io/contribute/naming.html)
- [Mathlib 概览](https://leanprover-community.github.io/mathlib-overview.html)
