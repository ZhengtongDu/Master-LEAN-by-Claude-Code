# 第四章：量词与相等性 (Quantifiers and Equality)

> **本章目标**：
> 1. 理解 Lean 中命题作为类型的核心：`∀` 是函数，`∃` 是配对。
> 2. 掌握 `intro`、`apply`、`use`、`rcases`、`have` 等处理量词的核心策略。
> 3. 理解相等性 `=` 的本质与 `rfl` 的工作原理。
> 4. 掌握重写策略 `rw` 与化简策略 `simp`。
> 5. 学会使用计算性证明工具：`norm_num`、`omega`、`decide`。
> 6. **实战**：将自然语言命题转化为精确的 Lean 表达式并完成证明。

在前面的章节中，我们处理的是像 $P \to Q$ 这样的命题逻辑结构。但在数学和计算机科学中，我们更关心对象的**性质**和对象间的**关系**：

- **命题逻辑**：如果下雨，地就会湿。（原子命题之间的关系）
- **谓词逻辑**：对于任意整数 $x$，如果 $x$ 是偶数，那么 $x^2$ 也是偶数。（深入对象内部结构）

为了表达后者，我们需要引入**谓词 (Predicates)** 和**量词 (Quantifiers)**。

---

## 4.1 谓词 (Predicates)

在 Lean 中，谓词就是一个函数，它接受某些参数，并返回一个 `Prop`（命题）。

> **谓词 (Predicate)**：一个从值到命题的函数。一元谓词 `α → Prop` 表示对象的性质，二元谓词 `α → α → Prop` 表示对象间的关系。

### 4.1.1 定义谓词

假设我们有一个类型 `α`：

- **一元谓词**：`α → Prop`。表示对象的性质（Property）。
  - 例如：`IsPrime : Nat → Prop`
- **二元谓词**：`α → α → Prop`。表示对象间的关系（Relation）。
  - 例如：`LessThan : Nat → Nat → Prop`

### Toy Case: 自定义性质

让我们定义一个简单的性质："是一个大数"（大于 10）。

```lean
import Mathlib.Tactic -- 引入常用策略库

/-- IsLarge: 判断一个自然数是否"大"（大于 10）
    输入: n — 自然数
    输出: Prop — 命题（n > 10 是否成立） -/
def IsLarge (n : Nat) : Prop := n > 10

-- 使用 #check 查看类型
#check IsLarge      -- IsLarge : Nat → Prop
#check IsLarge 15   -- IsLarge 15 : Prop（这是一个命题，尚未证明真假）
#check IsLarge 5    -- IsLarge 5 : Prop（这也是一个命题，虽然它是假的）

-- 证明具体的命题
example : IsLarge 15 := by
  -- 展开 IsLarge 的定义，目标变为 15 > 10
  dsimp [IsLarge]
  -- 自然数算术中的不等式，自动求解
  simp
```

---

## 4.2 全称量词 (Universal Quantifier, `∀`)

全称量词 `∀`（输入 `\forall`）对应英语中的 "For all"、"Every"。

### 4.2.1 核心原理：`∀` 就是函数

> **∀ 即函数**：在 Lean（以及所有依赖类型理论）中，**全称量词本质上就是函数类型**（Dependent Function Type / Pi Type）。命题 `∀ x : Nat, P x` 的证明，就是一个接受具体数字 `n` 并返回 `P n` 证明的**函数**。

这就是为什么我们使用 `intro`（引入函数参数）和 `apply`（函数调用）来处理它。

### 4.2.2 引入 `∀` (Introduction)

**场景**：当证明目标 (Goal) 是 `∀ x, P x` 时。
**策略**：使用 `intro x`。这相当于说："让我们假设有一个任意的 `x`，不论它是谁。"

#### Toy Case: 恒等函数性质

证明：对于任意类型 `α` 和任意元素 `x`，恒等函数应用在 `x` 上等于 `x`。

```lean
/-- my_id: 恒等函数
    输入: x — 任意类型 α 的值
    输出: x 本身 -/
def my_id {α : Type} (x : α) : α := x

-- 目标：∀ {α : Type}, ∀ x : α, my_id x = x
example : ∀ {α : Type}, ∀ x : α, my_id x = x := by
  -- 1. 引入类型 α（虽然它是隐式的，但为了逻辑清晰我们显式引入）
  intro α
  -- 2. 引入任意元素 x
  intro x
  -- 3. 现在目标变成了证明 my_id x = x
  dsimp [my_id]  -- 展开 my_id 的定义
  -- 4. x = x 总是成立的（自反性）
  rfl
```

### 4.2.3 消除 `∀` (Elimination)

**场景**：当你已知一个全称假设 `h : ∀ x, P x`，且你想证明关于某个特定值 `v` 的性质 `P v` 时。
**策略**：使用 `apply h` 或 `specialize h v`。

> **消除 ∀ 的两种方式**：
> - `apply h`：当目标恰好是 `P v` 的形式时，直接应用 `h`，Lean 会自动匹配 `v`。
> - `specialize h v`：将假设 `h` 从 `∀ x, P x` 特化为 `P v`，修改假设本身。

#### Toy Case: 传递性证明

```lean
-- 如果所有自然数都满足 P，那么 0 也满足 P
example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  -- h 是一个"函数"：给它任何 Nat，它都能返回 P 的证明
  -- 我们把 0 "喂"给它
  apply h
  -- 也可以写成：exact h 0

-- 使用 specialize 特化假设
example (P : Nat → Prop) (h : ∀ n, P n) : P 42 := by
  -- 将 h 从 ∀ n, P n 特化为 P 42
  specialize h 42
  -- 现在 h : P 42，正好是我们的目标
  exact h
```

---

## 4.3 存在量词 (Existential Quantifier, `∃`)

存在量词 `∃`（输入 `\exists`）对应英语中的 "There exists"、"Some"。

### 4.3.1 核心原理：`∃` 就是配对

> **∃ 即配对**：在 Lean 中，`∃ x : α, P x` 的证明是一个**配对 (Pair)**：一个具体的值 `a : α`（称为"见证者" witness）加上一个 `P a` 的证明。这在类型论中对应**依赖对类型 (Sigma Type)**。

### 4.3.2 引入 `∃` (Introduction)

**场景**：当证明目标是 `∃ x, P x` 时。
**策略**：使用 `use v`，提供一个具体的见证者 `v`，然后证明 `P v`。

#### Toy Case: 找到一个偶数

```lean
/-- IsEven: 判断一个自然数是否为偶数
    输入: n — 自然数
    输出: Prop — 存在 k 使得 n = 2 * k -/
def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

-- 证明：存在一个偶数（比如 4）
example : ∃ n, IsEven n := by
  -- 1. 提供见证者：n = 4
  use 4
  -- 2. 现在需要证明 IsEven 4，即 ∃ k, 4 = 2 * k
  dsimp [IsEven]
  -- 3. 提供 k = 2
  use 2
  -- 4. 4 = 2 * 2 由计算自动验证
```

### 4.3.3 消除 `∃` (Elimination)

**场景**：当你有一个假设 `h : ∃ x, P x`，想要取出那个存在的元素和它的性质时。
**策略**：使用 `rcases h with ⟨w, hw⟩`（或 `obtain ⟨w, hw⟩ := h`）。

> **rcases 解构**：`rcases` 是 Lean 中最强大的模式匹配策略之一。对于存在量词，`rcases h with ⟨w, hw⟩` 会取出见证者 `w` 和性质 `hw`。尖括号 `⟨⟩` 输入 `\<` 和 `\>`。

#### Toy Case: 偶数的性质传递

```lean
-- 如果 n 是偶数，那么 n + n 也是偶数
example (n : Nat) (h : IsEven n) : IsEven (n + n) := by
  -- 1. 从 h 中取出见证者 k 和性质 hk : n = 2 * k
  rcases h with ⟨k, hk⟩
  -- 2. 现在需要证明 ∃ m, n + n = 2 * m
  dsimp [IsEven]
  -- 3. 提供见证者 m = n（因为 n + n = 2 * n）
  use n
  -- 4. omega 可以处理线性算术
  omega
```

---

## 4.4 相等性 (`=`) 与 `rfl`

相等性是数学中最基本的关系。在 Lean 中，`=` 是一个归纳类型，而 `rfl`（reflexivity，自反性）是它唯一的构造器。

### 4.4.1 核心原理：相等性的定义

> **相等性 (Equality)**：在 Lean 中，`a = b` 是一个命题（`Prop`）。它的唯一构造器是 `Eq.refl a : a = a`，简写为 `rfl`。这意味着要证明 `a = b`，Lean 需要能够通过**计算归约**（definitional equality）确认 `a` 和 `b` 是"相同的"。

```lean
-- rfl 可以证明定义上相等的表达式
example : 2 + 3 = 5 := by rfl    -- Lean 计算 2+3 得到 5，与右边相同
example : "hello".length = 5 := by rfl

-- 也可以用 term mode 直接写
example : 2 + 3 = 5 := rfl

-- #check 查看 rfl 的类型
#check @rfl  -- @rfl : ∀ {α : Sort u} (a : α), a = a
```

### 4.4.2 对称性与传递性

相等性满足三个基本性质：自反性（`rfl`）、对称性（`Eq.symm`）、传递性（`Eq.trans`）。

```lean
-- 对称性：如果 a = b，那么 b = a
example (a b : Nat) (h : a = b) : b = a := by
  -- exact h.symm  -- term mode 写法
  exact Eq.symm h

-- 传递性：如果 a = b 且 b = c，那么 a = c
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  exact Eq.trans h1 h2
  -- 也可以写成：exact h1.trans h2
```

---

## 4.5 重写策略：`rw` 与 `simp`

当 `rfl` 无法直接证明相等性时（因为两边不是定义上相等的），我们需要**重写 (rewrite)** 策略来变换目标。

### 4.5.1 `rw`：精确重写

> **rw 策略**：`rw [h]` 使用等式 `h : a = b` 将目标中所有的 `a` 替换为 `b`。`rw [← h]` 则反向替换（将 `b` 替换为 `a`）。箭头 `←` 输入 `\l` 或 `\<-`。

```lean
-- 基本重写
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  -- 用 h1 将目标中的 a 替换为 b
  rw [h1]
  -- 目标变为 b = c，正好是 h2
  exact h2

-- 反向重写
example (a b : Nat) (h : a = b) : b = a := by
  -- 用 h 反向重写：将目标中的 b 替换为 a
  rw [h]
  -- 目标变为 a = a，rfl 自动关闭
```

#### Toy Case: 用 rw 证明算术等式

```lean
/-- double: 计算 n 的两倍
    输入: n — 自然数
    输出: n + n — 自然数 -/
def double (n : Nat) : Nat := n + n

-- 证明 double 3 = 6
example : double 3 = 6 := by
  -- 展开 double 的定义
  rw [double]
  -- 目标变为 3 + 3 = 6，由计算自动验证

-- 连续重写：rw 可以接受一个列表
example (a b c : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = 0) : a = 0 := by
  rw [h1, h2, h3]  -- 依次替换 a→b→c→0
```

### 4.5.2 `simp`：自动化简

> **simp 策略**：`simp` 是 Lean 中最常用的自动化策略之一。它使用一组预定义的化简引理（标记了 `@[simp]` 的引理）反复重写目标，直到无法继续化简。可以用 `simp [h1, h2]` 额外提供引理。

```lean
-- simp 可以自动处理很多算术化简
example (n : Nat) : n + 0 = n := by simp
example (n : Nat) : 0 + n = n := by simp
example (n m : Nat) : n + m = m + n := by omega  -- 交换律需要 omega

-- simp 配合自定义引理
example (n : Nat) : double n = n + n := by
  simp [double]  -- 展开 double 的定义即可

-- simp only：限制只使用指定的引理（更可控）
example (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]  -- 只用 Nat.add_zero 这一条引理
```

---

## 4.6 计算性证明：`norm_num`、`omega`、`decide`

Lean 提供了多个强大的自动化策略，专门处理不同类型的计算性证明。

### 4.6.1 `norm_num`：数值规范化

> **norm_num**：专门处理**数值表达式**的策略。它可以自动验证涉及具体数字的等式、不等式，以及一些数论性质（如素数判定）。需要 `import Mathlib.Tactic`。

```lean
import Mathlib.Tactic

-- 数值等式
example : (3 : Nat) * 7 = 21 := by norm_num
example : (100 : Int) - 250 = -150 := by norm_num

-- 数值不等式
example : (17 : Nat) ≤ 42 := by norm_num
example : (3 : Nat) < 5 := by norm_num

-- 整除性
example : 3 ∣ 12 := by norm_num
```

### 4.6.2 `omega`：线性算术

> **omega**：处理**线性算术**（自然数和整数上的加减法、比较）的完备决策过程。它可以自动证明所有线性算术中的真命题，不需要额外导入。

```lean
-- 线性等式与不等式
example (n : Nat) : n + 1 > n := by omega
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
example (n : Nat) : 2 * n + 1 > n := by omega

-- omega 可以处理多个假设的组合推理
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by omega
example (n : Nat) (h : n > 0) : n ≥ 1 := by omega
```

### 4.6.3 `decide`：可判定命题

> **decide**：对于**可判定 (Decidable)** 的命题，`decide` 通过穷举计算来判定真假。适用于有限域上的命题，如布尔表达式、有限集合的成员关系等。

```lean
-- 布尔判定
example : 2 + 2 = 4 := by decide
example : ¬ (3 = 5) := by decide

-- 比较运算
example : 10 % 3 = 1 := by decide
```

### 4.6.4 如何选择？

| 策略 | 适用场景 | 特点 |
| --- | --- | --- |
| `rfl` | 定义上相等的表达式 | 最快，零开销 |
| `norm_num` | 具体数值计算 | 处理乘除、素数等 |
| `omega` | 线性算术（加减比较） | 完备决策，处理变量 |
| `decide` | 可判定的有限命题 | 穷举计算，可能较慢 |
| `simp` | 通用化简 | 灵活但不一定完备 |

---

## 4.7 进阶技巧：量词组合与否定

在实际数学中，量词经常与否定、蕴含等逻辑连接词组合出现。本节介绍处理这些复杂结构的策略。

### 4.7.1 量词的否定：`push_neg`

> **push_neg**：将否定符号 `¬` 推入量词内部。根据经典逻辑：`¬ (∀ x, P x)` 等价于 `∃ x, ¬ P x`，`¬ (∃ x, P x)` 等价于 `∀ x, ¬ P x`。需要 `import Mathlib.Tactic`。

```lean
import Mathlib.Tactic

-- push_neg 将 ¬∀ 转化为 ∃¬
example (P : Nat → Prop) : ¬ (∀ n, P n) → ∃ n, ¬ P n := by
  intro h
  -- h : ¬ (∀ n, P n)
  push_neg at h
  -- h : ∃ n, ¬ P n（否定被推入量词内部）
  exact h

-- push_neg 也可以作用于目标
example : ¬ (∀ n : Nat, n > 100) := by
  push_neg
  -- 目标变为 ∃ n, n ≤ 100
  use 0
  -- 0 ≤ 100 由 omega 自动验证
  omega
```

### 4.7.2 量词的嵌套

当多个量词嵌套时，`intro` 和 `rcases` 可以一次处理多层。

```lean
-- ∀ 嵌套：一次引入多个变量
example (P : Nat → Nat → Prop) (h : ∀ m n, P m n) : P 3 7 := by
  exact h 3 7  -- 直接将两个参数"喂"给 h

-- ∃ 嵌套：一次解构多层
example (P : Nat → Nat → Prop) (h : ∃ m, ∃ n, P m n) : ∃ n, ∃ m, P m n := by
  -- 一次性取出 m, n 和性质 hp
  rcases h with ⟨m, n, hp⟩
  -- 重新组装，交换顺序
  exact ⟨n, m, hp⟩
```

### 4.7.3 `∃` 与 `∀` 的交互

一个重要的逻辑事实：`(∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y)`，但反向通常不成立。

```lean
-- 正向：如果存在一个 x 对所有 y 都满足 P，那么对每个 y 都能找到满足 P 的 x
example (P : Nat → Nat → Prop) :
    (∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y) := by
  intro h
  -- 取出那个"万能的" x
  rcases h with ⟨x, hx⟩
  -- 对任意 y，用同一个 x 即可
  intro y
  use x
  exact hx y
```

---

## 4.8 实战：自然数性质证明

让我们综合运用本章学到的所有工具，完成几个有趣的证明。

### 4.8.1 形式化自然语言

将自然语言翻译为 Lean 表达式是形式化数学的核心技能。

| 自然语言 | Lean 表达式 |
| --- | --- |
| 所有自然数都大于等于 0 | `∀ n : Nat, n ≥ 0` |
| 存在一个偶数 | `∃ n : Nat, IsEven n` |
| 没有最大的自然数 | `∀ n : Nat, ∃ m : Nat, m > n` |
| 如果 n 是偶数，那么 n+2 也是偶数 | `∀ n, IsEven n → IsEven (n + 2)` |

```lean
-- 没有最大的自然数
example : ∀ n : Nat, ∃ m : Nat, m > n := by
  intro n
  -- 对任意 n，取 m = n + 1 即可
  use n + 1
  omega

-- 如果 n 是偶数，那么 n + 2 也是偶数
example : ∀ n, IsEven n → IsEven (n + 2) := by
  intro n h
  -- 取出 h 中的见证者 k，使得 n = 2 * k
  rcases h with ⟨k, hk⟩
  -- 需要找到 m 使得 n + 2 = 2 * m
  dsimp [IsEven]
  use k + 1
  -- n + 2 = 2 * k + 2 = 2 * (k + 1)
  omega
```

### 4.8.2 理发师悖论

这是一个经典的逻辑悖论：一个理发师声称"我只给不给自己理发的人理发"。我们可以证明这样的理发师不存在。

```lean
/-- 理发师悖论：不存在一个人，他给所有且仅给不给自己理发的人理发。
    这是 Russell 悖论的通俗版本。 -/
example (Person : Type) (shaves : Person → Person → Prop) :
    ¬ ∃ barber : Person, ∀ p : Person, shaves barber p ↔ ¬ shaves p p := by
  -- 假设这样的理发师存在
  intro ⟨barber, h⟩
  -- 考虑理发师是否给自己理发
  -- 取出 h 对 barber 自身的特化
  have h_self := h barber
  -- h_self : shaves barber barber ↔ ¬ shaves barber barber
  -- 取出双向蕴含的两个方向
  rcases h_self with ⟨h1, h2⟩
  -- h1 : shaves barber barber → ¬ shaves barber barber
  -- h2 : ¬ shaves barber barber → shaves barber barber
  -- 分类讨论：理发师是否给自己理发
  by_cases hb : shaves barber barber
  · -- 假设理发师给自己理发 (hb)
    -- 根据 h1，这意味着他必须不给自己理发
    have not_hb := h1 hb
    contradiction -- hb 和 not_hb 矛盾
  · -- 假设理发师不给自己理发 (hb)
    -- 根据 h2，这意味着他必须给自己理发
    have yes_hb := h2 hb
    contradiction
```

---

## 常用策略速查表 (Cheat Sheet)

### 证明目标 (Goal) 相关

| 目标 (Goal) | 策略 (Tactic) | 说明 |
| --- | --- | --- |
| `∀ x, P x` | `intro x` | 假设 x 是任意元素，开始证明 |
| `∃ x, P x` | `use v` | 声明 v 是那个存在的元素，然后证明 P v |
| `a = b` | `rfl` | 当 a 和 b 定义上相等时 |
| `a = b` | `rw [h]` | 用等式 h 重写目标 |
| 任意目标 | `simp` | 自动化简 |
| 数值等式/不等式 | `norm_num` | 具体数值计算 |
| 线性算术 | `omega` | 加减法、比较的自动推理 |
| 可判定命题 | `decide` | 穷举计算 |

### 假设 (Hypothesis) 相关

| 假设 (Hypothesis) | 策略 (Tactic) | 说明 |
| --- | --- | --- |
| `h : ∀ x, P x` | `apply h` / `specialize h v` | 将全称命题应用到特定值 v 上 |
| `h : ∃ x, P x` | `rcases h with ⟨v, hv⟩` | 取出见证者 v 和性质 hv |
| `h : ∃ x, P x ∧ Q x` | `rcases h with ⟨v, hp, hq⟩` | 一次性取出元素和两个性质 |
| `h : ¬ (∀ x, ...)` | `push_neg at h` | 将否定推入量词内部 |
| `h : a = b` | `rw [h]` | 用 h 重写目标中的 a 为 b |
| `h : a = b` | `rw [← h]` | 用 h 反向重写目标中的 b 为 a |

---

## 本章小结

本章介绍了谓词逻辑和相等性的核心概念：

1. **谓词**是从值到命题的函数（`α → Prop`），用于描述对象的性质和关系。
2. **全称量词** `∀` 本质上是依赖函数类型，用 `intro` 引入，用 `apply`/`specialize` 消除。
3. **存在量词** `∃` 本质上是依赖对类型，用 `use` 引入见证者，用 `rcases` 解构。
4. **相等性** `=` 的基础是 `rfl`（自反性），配合 `rw` 进行精确重写。
5. **simp** 提供自动化简，**norm_num**/**omega**/**decide** 分别处理数值计算、线性算术和可判定命题。

下一章我们将学习项式证明（Term-mode Proof），直接构造证明项而非使用策略。

---

## 练习 (Exercises)

1. **形式化练习**：定义谓词 `IsSubset (A B : Set Nat)`（A 是 B 的子集），使用 `∀` 量词。
   - *提示*：如果 n 在 A 中，那么 n 也在 B 中。

2. **证明练习**：证明 `(∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y)`。

3. **逻辑思考**：为什么上一题的反向 `(∀ y, ∃ x, P x y) → (∃ x, ∀ y, P x y)` 通常不成立？试着举一个反例（例如关于自然数的大小关系）。

4. **重写练习**：给定 `h1 : a = b + 1` 和 `h2 : b = 3`，用 `rw` 证明 `a = 4`。

5. **自动化练习**：分别用 `norm_num`、`omega`、`decide` 证明以下命题，体会它们的适用范围：
   - `7 * 13 = 91`
   - `∀ n : Nat, n + 0 = n`
   - `(10 : Nat) % 3 = 1`

6. **Mathlib 探索**：尝试在代码中键入 `\angle` 然后按 Tab，看看能打出什么符号？尝试 `\nat`。

---
