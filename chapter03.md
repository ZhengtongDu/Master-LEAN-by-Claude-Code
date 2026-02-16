# 第三章：命题逻辑 (Propositional Logic)

> **本章目标**：
> 1. **深度理解**：从类型论角度理解逻辑连接词（And 是乘积，Or 是求和，Implication 是函数）。
> 2. **熟练掌握**：逻辑与（And）、逻辑或（Or）、逻辑非（Not）、当且仅当（Iff）的引入（Introduction）与消除（Elimination）规则。
> 3. **进阶技巧**：掌握 rcases 模式匹配、by_cases 排中律分拆等实战策略。
> 4. **思维转换**：区分构造主义逻辑（默认）与经典逻辑（需开启），理解为什么 ¬¬P→P 在默认情况下无法证明。

在 Lean 中，命题（Proposition）是类型为 `Prop` 的对象。证明一个命题 $p$，在计算机科学看来，本质上就是编写一个程序（Term），其类型（Type）恰好是 $p$。这就是著名的 **Curry-Howard 同构**。

---

## 3.1 逻辑与（And）：积类型 (Product Types)

> **逻辑与 (And, ∧)**：在类型论中对应**积类型**（Product Type），类似于编程语言中的 `Pair<P, Q>` 或结构体。要证明 $p \land q$，你需要同时持有 $p$ 的实例和 $q$ 的实例。

### 3.1.1 构造（Introduction）：如何证明 P ∧ Q
当目标是 `p ∧ q` 时，我们需要提供两个证据。

```lean
variable (p q r : Prop)

-- 【策略模式】：使用 constructor 将目标一分为二
example (hp : p) (hq : q) : p ∧ q := by
  constructor -- 目标分裂： 1. ⊢ p   2. ⊢ q
  · exact hp  -- 解决第一个分支
  · exact hq  -- 解决第二个分支

-- 【项模式】：直接构造结构体 And.intro
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

-- 【项模式简写】：使用匿名构造子 ⟨ ⟩ (输入法: \< \>)
-- 这是最高效的写法，推荐熟练掌握
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

```

### 3.1.2 解构（Elimination）：如何使用 P ∧ Q
当你拥有假设 `h : p ∧ q` 时，你可以从中提取 `p` 和 `q`。

```lean
-- Toy Case: 证明 And 的交换律
example (h : p ∧ q) : q ∧ p := by
  -- 方法一：结构体访问（适合简单情况）
  -- h.left 获取 p，h.right 获取 q
  exact ⟨h.right, h.left⟩

-- 方法二：cases 模式匹配（适合复杂逻辑）
example (h : p ∧ q) : q ∧ p := by
  cases h with
  | intro hp hq => -- 将 h 拆解为 hp:p 和 hq:q
    constructor
    · exact hq
    · exact hp

-- 方法三：rcases (Recursive Cases) 深度解构（实战推荐）
-- rcases 支持类似正则表达式的模式，一次性拆解
example (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  rcases h with ⟨hp, hq, hr⟩ -- 一步到位，直接拿到 hp, hq, hr
  exact ⟨⟨hp, hq⟩, hr⟩

```

---

## 3.2 逻辑或（Or）：和类型 (Sum Types)

> **逻辑或 (Or, ∨)**：在类型论中对应**和类型**（Sum Type），类似于编程语言中的 `Enum` 或 `Union`。要证明 $p \lor q$，你只需要提供其中**任意一个**的证据。

### 3.2.1 构造（Introduction）：左注入与右注入
我们必须明确告诉 Lean，我们想通过哪一边来证明 `Or`。

```lean
-- 证明：如果拥有 p，那么 p ∨ q 成立
example (hp : p) : p ∨ q := by
  left      -- 告诉 Lean 我们选择证明左边。目标变为 ⊢ p
  exact hp

-- 【项模式】：Or.inl (Left) 和 Or.inr (Right)
example (hq : q) : p ∨ q := Or.inr hq

```

### 3.2.2 解构（Elimination）：分类讨论
当你拥有假设 `h : p ∨ q` 时，你不知道具体是哪一个成立。因此，你必须证明：**无论哪种情况，结论都成立**。

```lean
-- Toy Case: 证明 Or 的交换律
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => -- 分支 1：假设 h 是由 p 构造的 (h 变为 hp)
    right     -- 目标是 q ∨ p，我们有 p，所以选右边
    exact hp
  | inr hq => -- 分支 2：假设 h 是由 q 构造的
    left      -- 目标是 q ∨ p，我们有 q，所以选左边
    exact hq

```

---

## 3.3 逻辑非（Not）与假命题（False）

> **逻辑非 (Not, ¬)**：在 Lean（以及所有构造主义逻辑）中，$\neg p$ 不是一个基本操作符，而是一个**定义**：¬p 等价于 p → False。这意味着：要证明"非 p"，你需要构造一个函数，这个函数接收一个"p 的证据"，然后输出一个"谬误（False）"。

### 3.3.1 证明逻辑非

```lean
-- Toy Case: 逆否命题的一个方向 (p → q) → (¬q → ¬p)
example (h : p → q) : ¬q → ¬p := by
  -- 目标是 ¬q → ¬p，即 ¬q → (p → False)
  intro hnq  -- 假设 ¬q
  intro hp   -- 假设 p (为了推导出 False)
  
  -- 现在我们需要构造一个 False
  -- 我们有 h : p → q 和 hp : p，所以 h hp 得到 q
  have hq : q := h hp
  
  -- 我们有 hnq : ¬q (即 q → False) 和 hq : q
  -- 所以 hnq hq 得到 False
  apply hnq  -- 目标变为 q
  exact hq

```

### 3.3.2 爆炸原理 (Ex Falso)

> **爆炸原理 (Ex Falso)**：`False` 是一个没有任何构造子的类型。如果你在上下文中拥有了一个 `False` 类型的项，你可以证明任何东西。

```lean
-- 只要有 False，世界都可以毁灭（证明任意目标）
example (h : False) : 2 + 2 = 5 := by
  exact h.elim -- False.elim: False 没有构造子，直接消除证明任意目标

```

### 3.3.3 经典逻辑：反证法
注意区别：

- **否定引入 (Introduction of Negation)**: 证明 `¬p`。方法是假设 `p` 推出 `False`。这是构造性的。
- **反证法 (Proof by Contradiction)**: 证明 `p`。方法是假设 `¬p` 推出 `False`。这是经典的（需要排中律）。

Lean 默认不支持反证法证明原子命题。如果你一定要用，需要使用 `by_contra`。

```lean
open Classical -- 开启经典逻辑模式

example (h : ¬¬p) : p := by
  by_contra hnp -- 假设结论 p 不成立 (得到 hnp : ¬p)
  -- 目标变为 False
  apply h   -- h : ¬p → False
  exact hnp -- 完美匹配

```

---

## 3.4 当且仅当（Iff）与重写

> **当且仅当 (Iff, ↔)**：`p ↔ q` 定义为 `(p → q) ∧ (q → p)`。它本质上是一个 And 结构体，包含两个方向的蕴含。

### 3.4.1 构造与解构

```lean
-- 证明：p ↔ p
example : p ↔ p := by
  constructor
  · intro h; exact h -- 去向：p → p
  · intro h; exact h -- 回向：p → p
  -- 或者直接用 rfl (Reflexivity)

```

### 3.4.2 强大的 `rw` (Rewrite)
如果这一章你只记住一个策略，那应该是 `rw`。如果已知 `h : p ↔ q`，`rw [h]` 可以将目标中的 `p` 替换为 `q`。

```lean
variable (a b c : Prop)

-- Toy Case: Iff 的传递性
example (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c := by
  rw [h1] -- 将目标中的 a 替换为 b。目标变为 b ↔ c
  rw [h2] -- 将目标中的 b 替换为 c。目标变为 c ↔ c
  rfl     -- 自反性得证

```
**进阶技巧**：

- `rw [←h]`: 从右向左替换（把 q 换成 a）。
- `rw [h] at h1`: 在假设 `h1` 中进行替换，而不是在目标中。

---

## 3.5 经典逻辑 vs 构造逻辑：深度辨析

> **排中律 (Law of Excluded Middle, LEM)**：在构造逻辑中，$p \lor \neg p$ 不是公理，因为我们并不总是知道任意命题是真还是假。在日常数学中，我们习惯使用排中律。在 Lean 中使用它通常通过 `Classical.em` 或策略 `by_cases`。

Lean 极其严谨。在构造逻辑中，我们关心的是**证据**。

- 证明 $p \lor q$，必须明确拿出 $p$ 或者 $q$ 其中一个。
- 因此，$p \lor \neg p$（排中律）不是公理，因为我们并不总是知道任意命题是真还是假。

### 实战神器：`by_cases`
这是处理排中律最舒服的方式。

```lean
open Classical

variable (p : Prop)

-- 证明：(p → q) ∨ (q → p)
-- 这是一个典型的经典逻辑命题，构造逻辑无法证明
example : (p → q) ∨ (q → p) := by
  by_cases h : p -- 引入排中律：讨论 p 是真还是假
  
  -- Case 1: 假设 p 为真 (h : p)
  · right      -- 选择右边 q → p
    intro _    -- 假设 q
    exact h    -- 返回 p (利用 h)
    
  -- Case 2: 假设 p 为假 (h : ¬p)
  · left       -- 选择左边 p → q
    intro hp   -- 假设 p
    -- 此时我们有 h: ¬p 和 hp: p，矛盾！
    exact (h hp).elim -- 爆炸原理

```

---

## 3.6 实战：命题逻辑证明练习
这里的练习涵盖了本章的核心难点。

### 练习 1：Curry 化与反 Curry 化
这是函数式编程的核心概念在逻辑中的投影。
`p → q → r` 等价于 `p ∧ q → r`。

```lean
/-- curry_equivalence: Curry 化等价性
    描述: (p ∧ q → r) 与 (p → q → r) 等价
    输入: p q r — 任意命题
    输出: 双向蕴含的证明 -/
theorem curry_equivalence : (p ∧ q → r) ↔ (p → q → r) := by
  constructor
  · -- 方向 1: (p ∧ q → r) → (p → q → r)
    intro h     -- h : p ∧ q → r
    intro hp    -- hp : p
    intro hq    -- hq : q
    apply h     -- 目标变为 p ∧ q
    exact ⟨hp, hq⟩ -- 构造 And
    
  · -- 方向 2: (p → q → r) → (p ∧ q → r)
    intro h     -- h : p → q → r
    intro hand  -- hand : p ∧ q
    rcases hand with ⟨hp, hq⟩ -- 快速解构
    -- h 需要两个参数，按顺序给它
    apply h
    · exact hp
    · exact hq

```

### 练习 2：德摩根定律（困难方向）
证明 `¬(p ∧ q) → ¬p ∨ ¬q`。
**提示**：这个方向需要经典逻辑（排中律）。因为如果是构造性的，仅仅知道“p 和 q 不能同时为真”，并不能直接告诉我们“p 是假的”还是“q 是假的”。

```lean
open Classical

/-- de_morgan_hard: 德摩根定律（困难方向）
    描述: ¬(p ∧ q) 蕴含 ¬p ∨ ¬q
    输入: p q — 任意命题
    输出: 需要经典逻辑（排中律）的证明 -/
theorem de_morgan_hard (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h -- h : ¬(p ∧ q)
  -- 此时我们卡住了，因为无法从 ¬(p ∧ q) 构造出 ¬p 或 ¬q
  -- 使用 by_cases 对 p 进行分类讨论
  by_cases hp : p
  
  · -- Case 1: p 为真
    right -- 既然 p 是真的，那肯定是 q 出了问题，我们选右边 ¬q
    intro hq -- 假设 q 为真
    apply h  -- h 说 p 和 q 不能同时为真
    exact ⟨hp, hq⟩ -- 但我们要把它们凑在一起，引发矛盾
    
  · -- Case 2: p 为假
    left -- 既然 p 已经是假的了，直接选左边 ¬p
    exact hp

```

---

## 本章小结

1. **And (∧)**: 用 `⟨ ⟩` 构造，用 `rcases` 解构。
2. **Or (∨)**: 用 `left/right` 构造，用 `cases` 分类讨论。
3. **Not (¬)**: 理解为 `→ False`，通过推导矛盾来证明。
4. **Classical**: 遇到推不下去的逻辑题（特别是涉及否定之否定、德摩根律逆向），记得 `open Classical` 并尝试 `by_cases`。

### 下一步
准备好进入 **第四章：量词逻辑 (Quantifiers)** 吗？在那里我们将把逻辑从简单的命题扩展到更广阔的数学世界，学习处理“对任意 $x$” ($\forall x$) 和“存在 $x$” ($\exists x$)。
