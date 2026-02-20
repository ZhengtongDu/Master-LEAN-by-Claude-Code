# 第九章：证明自动化 (Proof Automation)

> **本章目标**：
> 1. **深入 simp**：理解 `simp` 的引理集机制与 `@[simp]` 标注，掌握 `simp only` 的精确控制。
> 2. **算术自动化**：使用 `omega` 处理线性算术，使用 `norm_num` 处理数值计算。
> 3. **自动搜索**：了解 `aesop` 的策略搜索机制，让 Lean 自动完成逻辑证明。
> 4. **可判定性**：理解 `decide` 的工作原理与适用范围。
> 5. **引理搜索**：使用 `exact?`、`apply?`、`rw?` 让 Lean 帮你找到合适的引理。

在前面的章节中，我们手动使用 `intro`、`apply`、`rw` 等策略一步步构造证明。这对于理解证明的本质非常重要，但在实际开发中，许多证明步骤是机械性的、可以自动完成的。

本章将系统介绍 Lean 4 提供的**证明自动化工具**。掌握这些工具后，你将能够：
- 用一行代码完成原本需要十几步的证明
- 让 Lean 帮你搜索合适的引理
- 专注于证明的核心创意部分，把机械工作交给机器

---

## 9.1 simp 详解：引理集与 @[simp] 标注

> **simp（化简策略）**：`simp` 是 Lean 中最常用的自动化策略。它维护一个**引理集（Simp Set）**，反复将目标中匹配的表达式替换为更简单的形式，直到无法继续化简。标记了 `@[simp]` 属性的引理会自动加入默认引理集。

### 9.1.1 simp 的基本用法

`simp` 会自动应用标准库中大量标记了 `@[simp]` 的引理来化简目标。

```lean
-- simp 自动处理常见的算术化简
example (n : Nat) : n + 0 = n := by simp
example (n : Nat) : 0 + n = n := by simp
example (n : Nat) : n * 1 = n := by simp
example (b : Bool) : !(!b) = b := by simp

-- simp 也能处理列表操作
example : [1, 2, 3].length = 3 := by simp
example : [1, 2] ++ [3, 4] = [1, 2, 3, 4] := by simp
```

### 9.1.2 simp only：精确控制

> **simp only**：当 `simp` 使用的引理集太大导致化简结果不可预测时，`simp only [引理列表]` 允许你精确指定使用哪些引理。这在正式的数学证明中更受推荐，因为它使证明更稳定、更可维护。

```lean
-- simp only 只使用指定的引理
example (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

-- 可以同时指定多条引理
example (a b : Nat) : a + 0 + (b + 0) = a + b := by
  simp only [Nat.add_zero]
```

### 9.1.3 @[simp] 标注：扩展引理集

你可以用 `@[simp]` 属性标记自己的引理，使其自动被 `simp` 使用。

```lean
/-- double: 计算 n 的两倍
    输入: n — 自然数
    输出: n + n -/
def double (n : Nat) : Nat := n + n

/-- double 的展开引理：标记为 @[simp] 后，simp 会自动展开 double -/
@[simp] theorem double_eq (n : Nat) : double n = n + n := rfl

-- 现在 simp 可以自动处理 double
example (n : Nat) : double n = n + n := by simp
example (n : Nat) : double n + 0 = n + n := by simp
```

### 9.1.4 simp 的变体

| 变体 | 说明 |
| --- | --- |
| `simp` | 使用默认引理集化简目标 |
| `simp only [h1, h2]` | 只使用指定引理 |
| `simp [h]` | 默认引理集 + 额外引理 h |
| `simp at h` | 化简假设 h 而非目标 |
| `simp at *` | 化简所有假设和目标 |
| `simp_all` | 更激进的化简，同时处理假设和目标的交互 |
| `dsimp` | 只进行定义展开（definitional simp），不使用引理 |

### Toy Case：用 simp 简化列表证明

```lean
/-- myAppend: 自定义列表连接
    输入: xs ys — 两个列表
    输出: 连接后的列表 -/
def myAppend : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

@[simp] theorem myAppend_nil (ys : List α) : myAppend [] ys = ys := rfl
@[simp] theorem myAppend_cons (x : α) (xs ys : List α) :
    myAppend (x :: xs) ys = x :: myAppend xs ys := rfl

-- 有了 @[simp] 标注，simp 可以自动展开 myAppend
example : myAppend [1, 2] [3] = [1, 2, 3] := by simp [myAppend]
```

---

## 9.2 omega 与算术推理

> **omega**：`omega` 是处理**线性算术**的完备决策过程（Presburger Arithmetic）。它可以自动证明涉及自然数（`Nat`）和整数（`Int`）的加减法、比较、整除等线性关系。不需要额外导入，是 Lean 4 内置策略。

### 9.2.1 omega 的能力范围

`omega` 可以处理以下类型的命题：
- 线性等式与不等式（涉及 `+`、`-`、`*常数`、`<`、`≤`、`≥`、`>`）
- 多个假设的组合推理
- 自然数的特殊性质（如 `n - m` 在 `Nat` 中的截断行为）

```lean
-- 基本线性算术
example (n : Nat) : n + 1 > n := by omega
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
example (n : Nat) : 2 * n + 1 > n := by omega

-- 多假设组合推理
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by omega
example (n : Nat) (h : n > 0) : n ≥ 1 := by omega

-- Nat 减法的截断行为
example (n : Nat) : n - n = 0 := by omega
example (a b : Nat) (h : a ≥ b) : a - b + b = a := by omega
```

### 9.2.2 omega vs norm_num

> **norm_num**：专门处理**具体数值表达式**的策略。它可以验证涉及具体数字的等式、不等式，以及一些数论性质（如素数判定）。需要 `import Mathlib.Tactic`。

两者的区别：

| 特性 | omega | norm_num |
| --- | --- | --- |
| 处理变量 | 可以 | 不可以（仅具体数值） |
| 乘法 | 仅常数倍（如 `2*n`） | 任意数值乘法 |
| 需要导入 | 不需要 | 需要 Mathlib |
| 整除/素数 | 不支持 | 支持 |

```lean
import Mathlib.Tactic

-- omega 擅长：含变量的线性推理
example (n m : Nat) (h : n < m) : n + 1 ≤ m := by omega

-- norm_num 擅长：具体数值计算
example : (7 : Nat) * 13 = 91 := by norm_num
example : Nat.Prime 17 := by norm_num
example : (3 : Int) - 7 = -4 := by norm_num
```

---

## 9.3 aesop：自动策略搜索

> **aesop（Automated Extensible Search for Obvious Proofs）**：`aesop` 是一个通用的自动证明搜索策略。它通过组合 `intro`、`apply`、`cases`、`exact` 等基础策略，自动搜索证明路径。特别擅长处理逻辑命题和简单的结构性证明。

### 9.3.1 基本用法

```lean
-- aesop 自动完成逻辑证明
example (P Q : Prop) : P ∧ Q → Q ∧ P := by aesop
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by aesop
example (P : Prop) : P → P := by aesop

-- aesop 处理存在量词
example : ∃ n : Nat, n + 1 = 3 := by aesop
```

### 9.3.2 aesop 的搜索机制

`aesop` 的工作方式类似于 Prolog 的搜索：

1. **安全规则（Safe Rules）**：总是正确的变换（如 `intro`、拆解 `∧`），优先应用。
2. **不安全规则（Unsafe Rules）**：可能导致死胡同的变换（如 `apply` 某个假设），需要回溯。
3. **规范化规则（Norm Rules）**：化简步骤（如 `simp`），在每一步后自动应用。

### 9.3.3 自定义 aesop 规则

你可以用 `@[aesop]` 属性将自己的引理注册为 aesop 规则。

```lean
-- 将引理标记为 aesop 的安全规则
@[aesop safe [constructors, cases]]
inductive MyColor where
  | red | green | blue

-- aesop 现在可以自动处理 MyColor 的分类讨论
```

---

## 9.4 decide 与可判定命题

> **decide**：对于**可判定（Decidable）**的命题，`decide` 通过穷举计算来判定真假。一个命题是可判定的，意味着存在一个算法可以在有限步内确定它是真还是假。

### 9.4.1 什么是可判定命题？

在 Lean 中，`Decidable P` 是一个类型类，表示命题 `P` 可以通过计算来判定。常见的可判定命题包括：
- 具体数值的等式和不等式（如 `2 + 2 = 4`）
- 布尔表达式
- 有限集合上的命题

```lean
-- decide 处理具体数值
example : 2 + 2 = 4 := by decide
example : ¬ (3 = 5) := by decide
example : 10 % 3 = 1 := by decide

-- decide 处理布尔逻辑
example : (true && false) = false := by decide
example : (true || false) = true := by decide
```

### 9.4.2 decide 的局限性

`decide` 的计算是穷举式的，因此：
- 对于大数值可能非常慢（如 `decide` 证明 `2^100 > 0` 会超时）
- 不能处理含有自由变量的命题（如 `∀ n, n + 0 = n`）
- 不能处理不可判定的命题

```lean
-- 这些 decide 可以处理
example : (10 : Nat) < 20 := by decide

-- 这些 decide 不能处理（含变量）
-- example (n : Nat) : n + 0 = n := by decide  -- 报错！
-- 应该用 simp 或 omega
example (n : Nat) : n + 0 = n := by simp
```

### 9.4.3 decide vs omega vs norm_num vs simp

| 策略 | 适用场景 | 能处理变量？ | 速度 |
| --- | --- | --- | --- |
| `decide` | 可判定的有限命题 | 否 | 穷举，可能慢 |
| `omega` | 线性算术 | 是 | 快 |
| `norm_num` | 数值计算、数论 | 否 | 快 |
| `simp` | 通用化简 | 是 | 取决于引理集 |

---

## 9.5 exact?、apply?、rw?：引理搜索工具

> **引理搜索工具**：当你不知道该用哪条引理时，Lean 提供了一组"问号策略"来帮你搜索。`exact?` 搜索能直接关闭目标的引理，`apply?` 搜索能推进目标的引理，`rw?` 搜索能重写目标的引理。这些工具是学习 Lean 和探索 Mathlib 的利器。

### 9.5.1 exact?：精确搜索

`exact?` 会在当前环境中搜索一个能直接证明目标的项（引理或假设的组合）。

```lean
-- 当你不知道该用什么引理时
example (n : Nat) : n + 0 = n := by
  exact?
  -- Lean 会建议：exact Nat.add_zero n
  -- 或者：exact rfl（如果定义上相等）

-- exact? 也会搜索假设
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  exact?
  -- 建议：exact hpq hp
```

### 9.5.2 apply?：逆向搜索

`apply?` 搜索能将当前目标转化为更简单子目标的引理。

```lean
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by
  apply?
  -- 建议：apply Nat.le_succ_of_le
  -- 然后目标变为 a ≤ b，正好是 h
```

### 9.5.3 rw?：重写搜索

`rw?` 搜索能对目标进行重写的引理。

```lean
example (a b : Nat) : a + b = b + a := by
  rw?
  -- 建议：rw [Nat.add_comm]
```

### 9.5.4 使用技巧

1. **先试自动化**：遇到目标时，先试 `simp`、`omega`、`aesop`。
2. **搜索引理**：如果自动化失败，用 `exact?` 或 `apply?` 搜索。
3. **逐步推进**：用搜索到的引理替换 `exact?`/`apply?`，使证明更稳定。
4. **性能注意**：搜索可能需要几秒钟，在大型项目中可能更慢。

```lean
-- 实际工作流示例
example (n : Nat) : 0 + n = n := by
  -- 第一步：试 simp
  -- simp  -- 可以，但我们想知道具体用了什么引理
  -- 第二步：用 exact? 搜索
  -- exact?  -- 建议 exact Nat.zero_add n
  -- 第三步：用搜索结果替换
  exact Nat.zero_add n
```

---

## 9.6 实战：用自动化简化证明

让我们通过几个实战例子，体会自动化工具如何大幅简化证明过程。

### 9.6.1 手动 vs 自动：逻辑证明

```lean
-- 手动证明：德摩根定律
/-- deMorgan_manual: 德摩根定律的手动证明
    输入: P Q — 任意命题
    输出: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q 的证明 -/
theorem deMorgan_manual (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hp; exact h (Or.inl hp)
    · intro hq; exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ h
    cases h with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq

-- 自动证明：一行搞定
theorem deMorgan_auto (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  aesop
```

### 9.6.2 手动 vs 自动：算术证明

```lean
-- 手动证明：需要多步重写
example (a b c : Nat) (h1 : a = b + 1) (h2 : b = c + 2) : a = c + 3 := by
  rw [h1, h2]  -- 替换 a 和 b
  omega         -- 处理剩余算术

-- 更复杂的例子：omega 一步到位
example (n m : Nat) (h1 : n > 0) (h2 : m > n) (h3 : m < 100) : n < 100 := by
  omega
```

### 9.6.3 组合使用自动化工具

在实际证明中，最有效的方式是组合使用多种自动化工具。

```lean
/-- sum_le: 如果 a ≤ b 且 c ≤ d，则 a + c ≤ b + d
    输入: a b c d — 自然数，h1 : a ≤ b，h2 : c ≤ d
    输出: a + c ≤ b + d 的证明 -/
theorem sum_le (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) :
    a + c ≤ b + d := by
  omega  -- omega 可以直接从 h1 和 h2 推导出结论

-- 列表相关的证明：simp 大显身手
example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  simp [List.length_append]

-- 逻辑 + 算术的混合证明
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  omega
```

### 9.6.4 自动化策略选择指南

面对一个证明目标时，推荐按以下顺序尝试：

1. **`rfl`**：目标两边定义上相等？
2. **`simp`**：能否通过化简引理解决？
3. **`omega`**：是线性算术问题？
4. **`norm_num`**：是具体数值计算？
5. **`decide`**：是可判定的有限命题？
6. **`aesop`**：是纯逻辑推理？
7. **`exact?` / `apply?`**：不知道用什么引理？

```lean
-- 综合示例：证明一个稍复杂的命题
example (n : Nat) (h : n > 5) : n > 3 ∧ n ≥ 1 := by
  constructor  -- 拆分 ∧
  · omega      -- 线性算术
  · omega      -- 线性算术

-- 更简洁的写法
example (n : Nat) (h : n > 5) : n > 3 ∧ n ≥ 1 := by
  constructor <;> omega  -- 对所有子目标都用 omega
```

---

## 本章小结

1. **simp 是瑞士军刀**：通过 `@[simp]` 引理集自动化简，`simp only` 提供精确控制。在正式证明中优先使用 `simp only`。
2. **omega 处理算术**：线性算术的完备决策过程，能自动处理含变量的加减法和比较。不需要导入，开箱即用。
3. **aesop 搜索证明**：自动组合基础策略搜索证明路径，特别擅长逻辑命题。
4. **decide 穷举判定**：对可判定命题通过计算验证，适合具体的有限命题。
5. **问号策略是学习利器**：`exact?`、`apply?`、`rw?` 帮你发现合适的引理，是探索标准库和 Mathlib 的最佳工具。

---

## 练习题

1. **simp 练习**：定义函数 `triple (n : Nat) := 3 * n`，添加 `@[simp]` 引理，然后用 `simp` 证明 `triple n + triple m = 3 * (n + m)`。

2. **omega 练习**：证明以下命题：
   - `∀ n : Nat, n ≤ 2 * n`
   - `∀ a b : Nat, a < b → a + 1 ≤ b`
   - `∀ n : Nat, n > 0 → n - 1 + 1 = n`

3. **引理搜索**：使用 `exact?` 找到证明以下命题的引理：
   - `∀ (xs : List Nat), [].length = 0`
   - `∀ (n : Nat), n ≤ n`

4. **自动化对比**：对于命题 `(P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R)`，分别用手动策略和 `aesop` 完成证明，比较代码长度。

5. **综合实战**：证明 `∀ n : Nat, n * (n + 1) % 2 = 0`（提示：对 `n` 进行分类讨论，然后用 `omega` 或 `decide` 处理每种情况）。

---

