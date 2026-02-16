# 第五章：命题与逻辑 (Propositions and Logic)

## 本章概要

> **本章目标**：
> 1. **理解 Prop 宇宙**：为什么逻辑命题在 LEAN 中是特殊的"公民"。
> 2. **掌握逻辑连接词**：像操作数据结构一样操作 `And`、`Or`、`Not` 和 `Implies`。
> 3. **征服量词**：理解全称量词 `∀` 是函数，存在量词 `∃` 是配对（Pair）。
> 4. **相等性与重写**：深入理解 `Eq` 类型，学会使用 `rw` 和 `calc` 进行推理。
> 5. **经典逻辑**：在构造性逻辑的基础上，何时以及如何使用排中律。

欢迎来到 LEAN 的核心地带。在前几章中，我们处理了自然数、列表等数据结构。在这一章，我们将跨越 **"数据"与"逻辑"** 的界限。
你将经历计算机科学中最美妙的时刻之一：**Curry-Howard 同构（Curry-Howard Correspondence）**。你将发现，**命题（Proposition）仅仅是一种特殊的类型（Type），而证明（Proof）仅仅是该类型的程序（Program）。**
如果你能编写一个函数，你就能证明一个定理。

---

## 5.1 命题类型 Prop：代码即证明

> **证明无关性 (Proof Irrelevance)**：对于数据 `Nat`，`1` 和 `2` 是完全不同的。但对于命题 `2 + 2 = 4`，我们并不关心你是通过手指计数证明的，还是通过皮亚诺公理证明的。只要证明存在，它们在逻辑上就是等价的。LEAN 编译器在生成可执行代码时，会**擦除**所有 `Prop` 层级的内容。

在 Python 或 Java 中，布尔值 `True` 和 `False` 只是运行时的数据。但在 LEAN 中，命题是 **类型**。

### 5.1.1 类型的层级 (Sorts)
LEAN 的世界由一系列的“宇宙”组成：

- **Type 0 (或 Type)**：包含数据的类型，如 `Nat`, `List Int`, `String`。我们关心它们的内容。
- **Prop (或 Sort 0)**：包含逻辑命题的类型，如 `2 + 2 = 4`, `1 = 0`, `Prime 17`。

### 5.1.2 Toy Case：最简单的真命题
`True` 是一个类型，代表“逻辑真”。要证明它，我们需要构造一个 `True` 类型的实例。

```lean
-- 定义：simple_true 是一个类型为 True 的项
theorem simple_true : True :=
  True.intro  -- True.intro 是 True 类型唯一的构造函数（Canonical Proof）

-- 策略模式（Tactic Mode）版本
-- 这种写法更像是在“解题”
example : True := by
  -- trivial 策略会自动搜索像 True.intro 这样的简单构造器
  trivial

```

---

## 5.2 逻辑连接词：像拼图一样组合命题
逻辑连接词本质上是类型的组合子。如果你习惯了函数式编程，这部分会非常直观。

### 5.2.1 蕴含 (Implies, $\to$)：证明就是函数

> **蕴含即函数**：`P → Q` 仅仅是一个**函数类型**。输入是一个 `P` 成立的证据，输出是一个 `Q` 成立的证据。

```lean
variable (P Q R : Prop)

-- 这里的 p, q 是假设（Hypothesis），也就是函数的参数
-- 我们要利用 p 和 q 构造出 R
example (p : P) (q : P → Q) (r : Q → R) : R :=
  -- 函数式写法：将 p 喂给 q 得到 Q，再将结果喂给 r 得到 R
  r (q p)

-- 策略模式写法
example : (P → Q) → (Q → R) → (P → R) := by
  intro h1  -- 假设 P → Q，命名为 h1
  intro h2  -- 假设 Q → R，命名为 h2
  intro p   -- 假设 P，命名为 p
  -- 此时目标是证明 R
  apply h2  -- 为了证明 R，利用 h2，我们需要证明 Q
  apply h1  -- 为了证明 Q，利用 h1，我们需要证明 P
  exact p   -- 我们手里正好有 P 的证明 p

```

### 5.2.2 合取 (And, $\land$)：积类型 (Product)
`P ∧ Q` 就像一个包含两个字段的结构体 `struct { left: P, right: Q }`。

- **构造 (intro)**：如果你有 `hp : P` 和 `hq : Q`，你可以用 `And.intro hp hq` (或简写为 `⟨hp, hq⟩`) 构造出 `P ∧ Q`。
- **解构 (elim)**：如果你有 `h : P ∧ Q`，你可以用 `h.left` 拿到 `P`，用 `h.right` 拿到 `Q`。

```lean
example (hp : P) (hq : Q) : P ∧ Q := by
  constructor -- 告诉 LEAN 我们要构造一个结构体
  exact hp    -- 第一个字段填入 hp
  exact hq    -- 第二个字段填入 hq

-- 证明交换律：P ∧ Q → Q ∧ P
example (h : P ∧ Q) : Q ∧ P := by
  -- 使用匿名构造器 ⟨ ⟩
  have hp : P := h.left
  have hq : Q := h.right
  exact ⟨hq, hp⟩

```

### 5.2.3 析取 (Or, $\lor$)：和类型 (Sum)
`P ∨ Q` 就像一个枚举（Enum）或联合体（Union），它有两个构造器：`Or.inl` (左边为真) 和 `Or.inr` (右边为真)。

- **构造**：使用 `apply Or.inl` 或 `apply Or.inr` 选择一方。
- **解构**：必须处理两种情况（Case Analysis）。

```lean
-- 证明交换律：P ∨ Q → Q ∨ P
example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>       -- 情况 1：h 是由左边 (P) 构造的
    apply Or.inr    -- 我们选择构造目标右边的 P
    exact hp
  | inr hq =>       -- 情况 2：h 是由右边 (Q) 构造的
    apply Or.inl    -- 我们选择构造目标左边的 Q
    exact hq

```

### 5.2.4 否定 (Not, $\neg$)：通往虚无的函数

> **¬P 即 P → False**：在 LEAN 中，`¬P` 定义为 `P → False`。要证明 `¬P`，你需要构造一个函数，这个函数接受一个"假设 P 成立的证明"，然后推导出 `False`（矛盾）。

**Toy Case：德摩根定律 (De Morgan's Law)**

我们要证明 `¬(P ∨ Q) ↔ ¬P ∧ ¬Q`。这包含两个方向，我们演示其中一个方向。

```lean
/-- not_or_implies_and_not: 德摩根定律（一个方向）
    描述: 如果 (P 或 Q) 是假的，那么 (P 是假的) 且 (Q 是假的)
    输入: P Q — 任意命题
    输出: ¬P ∧ ¬Q 的证明 -/
theorem not_or_implies_and_not : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h          -- 假设 h : ¬(P ∨ Q)。记住，这意味着 (P ∨ Q) → False
  constructor      -- 拆分目标 ¬P ∧ ¬Q 为两个子目标

  -- 子目标 1: 证明 ¬P
  . intro hp       -- 假设 P 成立 (为了导出矛盾)
    -- 我们需要一个 False。能不能利用 h？
    -- h 需要一个 (P ∨ Q)。我们有 P，当然可以构造 (P ∨ Q)
    have h_or : P ∨ Q := Or.inl hp
    exact h h_or   -- 调用函数 h(h_or) 得到 False

  -- 子目标 2: 证明 ¬Q
  . intro hq       -- 假设 Q 成立
    apply h        -- 为了得到 False，应用 h，现在需要证明 P ∨ Q
    apply Or.inr   -- 选择右边
    exact hq

```

---

## 5.3 全称量词与存在量词
量词是“依赖类型（Dependent Types）”真正大显身手的地方。

### 5.3.1 全称量词 ($\forall$)：依赖函数

> **∀ 即依赖函数**：`∀ x : α, P x` 是一个函数。如果你给这个函数一个具体的 `a : α`，它会返回一个证明 `P a`。口诀：`intro` 一个变量，就像定义函数的参数。

```lean
-- 证明传递性：如果对于任意 x，P x 蕴含 Q x，且 Q x 蕴含 R x...
-- 那么对于任意 x，P x 蕴含 R x。
example (α : Type) (P Q R : α → Prop)
        (h1 : ∀ x, P x → Q x)
        (h2 : ∀ x, Q x → R x) :
        ∀ x, P x → R x := by
  intro y       -- 给定任意一个具体的 y (类型为 α)
  intro hpy     -- 假设 P y 成立
  
  -- 我们想得到 R y。
  -- 我们可以使用 h2。但是 h2 是全称量词。
  -- 我们可以把 y "喂" 给 h2，得到具体的蕴含式：Q y → R y
  have h2y := h2 y
  
  -- 同样的，把 y "喂" 给 h1，得到：P y → Q y
  have h1y := h1 y
  
  -- 现在就是简单的蕴含逻辑了
  apply h2y     -- 目标变成 Q y
  apply h1y     -- 目标变成 P y
  exact hpy     -- 我们有 P y

```

### 5.3.2 存在量词 ($\exists$)：依赖配对

> **∃ 即依赖配对**：`∃ x : α, P x` 是一个"神秘盒子"。盒子外面写着"里面有一个 α，且它满足 P"。要打开盒子，我们需要使用 `cases` 或 `rcases`。

**Toy Case：存在偶数**

```lean
/-- is_even: 判断自然数是否为偶数
    输入: n — 自然数
    输出: 存在 k 使得 n = 2 * k -/
def is_even (n : Nat) : Prop := ∃ k, n = 2 * k

-- 1. 证明存在性 (构造盒子)
example : is_even 4 := by
  -- 展开定义
  rw [is_even]
  -- 我们需要提供一个具体的 k，使得 4 = 2 * k
  -- 我们声称这个 k 是 2
  use 2
  -- LEAN 剩下要验证 4 = 2 * 2
  rfl

-- 2. 使用存在性 (打开盒子)
example (n : Nat) (h : is_even n) : is_even (n * n) := by
  -- 我们知道 n 是偶数，但这不意味着 n 就是 2 或 4。
  -- 我们只知道存在某个 k。让我们把 k "拿" 出来。
  rcases h with ⟨k, hk⟩ 
  -- 现在我们在上下文中有了：
  -- k : Nat
  -- hk : n = 2 * k
  
  rw [is_even]
  -- 为了证明 n * n 是偶数，我们需要一个新的 witness
  -- 既然 n = 2k，那么 n*n = 4k^2 = 2 * (2k^2)
  -- 所以我们的 witness 应该是 2 * k * k
  use 2 * k * k
  
  -- 下面是简单的代数推导
  rw [hk]       -- 把 n 替换为 2 * k
  ring          -- ring 策略可以自动处理环上的代数运算（加乘）

```

---

## 5.4 相等性与重写：推理的引擎
在 LEAN 中，`=` (`Eq`) 是最常用的关系。

### 5.4.1 定义相等 vs 命题相等

> **定义相等 vs 命题相等**：**定义相等**（如 `1 + 1 = 2`）是计算出来的，不需要证明，使用 `rfl` 即可解决。**命题相等**（如 `x + 0 = x`）不是计算出来的（对于未知的 x），需要利用公理或定理证明。

### 5.4.2 强大的 `rw` (Rewrite)
`rw` 是最常用的策略之一。它利用 `a = b` 的证明，将目标中的 `a` 替换为 `b`。

- `rw [lemma]`: 将 lemma 的左边替换为右边。
- `rw [← lemma]`: 将 lemma 的右边替换为左边（左箭头表示方向）。
- `rw [lemma] at h`: 在假设 `h` 中进行替换，而不是在目标中。

### Toy Case：使用 `calc` 进行链式证明
当证明步骤较多时，使用 `calc` 块可以写出非常易读的证明，类似于我们在纸上写推导过程。

```lean
variable (a b c : Nat)

-- 证明结合律的一个特例
example : (a + b) + c = a + (c + b) := by
  calc
    (a + b) + c = a + (b + c) := by rw [Nat.add_assoc] -- 加法结合律
    _           = a + (c + b) := by rw [Nat.add_comm b c] -- 仅交换 b 和 c

```

---

## 5.5 经典逻辑与构造逻辑
LEAN 默认是 **构造性 (Constructive)** 的。这意味着：

- **排中律 (Law of Excluded Middle, LEM)**：`P ∨ ¬P` 不是默认公理。
- **双重否定消除**：`¬¬P → P` 不是默认公理。

构造主义要求：如果你声称 `P ∨ Q` 成立，你必须明确指出到底是 P 成立还是 Q 成立。这对于从证明中提取算法非常重要。

### 5.5.1 开启经典模式
但在纯数学领域，我们经常需要反证法（Proof by Contradiction）。我们可以引入 `Classical` 库。

**Toy Case：经典逻辑下的证明**

证明：如果你不是不快乐，那你就是快乐的。（在构造逻辑中这不一定成立，但在经典逻辑中成立）。

```lean
open Classical -- 打开经典逻辑的大门

variable (Happy : Prop)

example : ¬(¬Happy) → Happy := by
  intro h -- 假设 "不是不快乐"
  
  -- 使用 by_contra (反证法策略)
  -- 假设结论 Happy 不成立，推出矛盾
  by_contra h_not_happy
  
  -- 现在我们有 h : ¬¬Happy 和 h_not_happy : ¬Happy
  -- 这直接矛盾
  exact h h_not_happy

```
*注意：by_contra 是经典逻辑的标志。在底层，它使用了排中律 em : ∀ P, P ∨ ¬P。*

---

## 本章小结

1. **Prop 即 Type**：逻辑命题是类型，证明是该类型的项。
2. **构造/解构**：
  - And (`∧`): `constructor` / `h.left`, `h.right`
  - Or (`∨`): `apply Or.inl` / `cases h`
  - Exists (`∃`): `use x` / `rcases h with ⟨x, hx⟩`
3. **函数即蕴含**：`intro` 引入假设，`apply` 应用定理。
4. **相等性**：`rfl` 处理定义相等，`rw` 处理重写。

掌握了这些工具，你已经具备了形式化绝大多数基础数学命题的能力。在下一章，我们将把目光转向 **归纳法 (Induction)**，这是证明自然数和递归结构属性的终极武器。

## 练习题

1. **逻辑体操**：证明 `(P → Q → R) ↔ (P ∧ Q → R)`。（提示：这是 Curry 化与反 Curry 化）。
2. **分配律**：证明 `P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)`。
3. **量词练习**：定义“奇数”，并证明两个奇数之和是偶数。（提示：你需要 `use` 一个构造出的值）。

