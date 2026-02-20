# 第五章：项式证明 (Term-mode Proof)

> **本章目标**：
> 1. **理解 Curry-Howard 同构**：命题就是类型，证明就是程序——掌握项式证明的核心思想。
> 2. **掌握 Lambda 构造**：使用 `fun` 直接构造蕴含（→）的证明项。
> 3. **学会匿名构造器**：使用 `⟨...⟩` 构造"与"（∧）和"存在"（∃）的证明。
> 4. **结构化证明**：使用 `have`、`let`、`show` 分步组织复杂证明。
> 5. **混合使用**：掌握项式证明与策略式证明的最佳组合方式。

在前几章中，我们大量使用了 **策略模式（Tactic Mode）**，即在 `by ...` 代码块中通过 `intro`, `apply`, `rw` 等指令来指挥 Lean 寻找证明。这对初学者非常友好，因为它像是在玩一个"消除目标"的游戏。
然而，Lean 的底层真面目是 **项式证明（Term-mode Proof）**。在 Lean 基于的 **依赖类型理论（Dependent Type Theory）** 中，**命题就是类型，证明就是程序**。

- **策略模式**：你告诉 Lean "怎么做"（How），Lean 帮你构造出底层的证明项。
- **项式证明**：你直接写出"是什么"（What），即直接构造出那个证明对象。

掌握项式证明不仅能让你写出更简洁（有时只有一行）的代码，更能让你通过"程序员"的视角彻底理解逻辑推导的本质。

---

## 5.1 直接构造证明项：证明即函数

### 5.1.1 核心概念：Curry-Howard 同构

> **Curry-Howard 同构**：逻辑与编程之间存在深刻的对应关系——命题对应类型，证明对应程序，蕴含对应函数类型，推理规则对应函数应用。在 Lean 中，证明一个定理本质上就是编写一个满足对应类型的程序。

在计算机科学中，有一个著名的发现叫 **Curry-Howard 同构（Curry-Howard Isomorphism）**。它揭示了逻辑与编程之间的惊人对应关系：

| 逻辑概念 (Logic) | 编程概念 (Programming) | 直观理解 |
| --- | --- | --- |
| 命题 (Proposition) P | 类型 (Type) P | 问题的描述 |
| 证明 (Proof) p | 项/值 (Term/Value) p : P | 问题的解 |
| 蕴含 P→Q | 函数类型 P → Q | 一个将 P 转化为 Q 的转换器 |
| 肯定前件 (Modus Ponens) | 函数应用 f a | 将转换器作用于输入数据 |
| 全称量词 ∀x,P(x) | 依赖函数类型 (Pi Type) | 能够处理任意输入的通用函数 |

**结论**：在 Lean 中，证明一个定理 `theorem T : P := ...`，本质上就是编写一个类型为 `P` 的函数或值。

### 5.1.2 Toy Case：恒等函数与逻辑自洽
让我们从最简单的逻辑命题 $P \to P$ 开始。
这表示：“如果 P 成立，那么 P 成立”。
在编程中，这对应于一个函数：**它接收一个类型为 P 的参数，并返回一个类型为 P 的值**。

```lean
-- 定义 P 为一个命题类型
variable (P : Prop)

/--
  名称: identity_proof（自我蕴含）
  描述: 对于任意命题 P，P → P
  输入: h : P（命题 P 的证明）
  输出: P 的证明

  项式证明思路：
  我们需要构造一个函数 `f`，使得 `f` 的类型是 `P → P`。
  这意味着 `f` 接受一个参数 `h` (h 的类型是 P)，并返回一个类型为 P 的东西。
  最简单的办法就是直接返回 `h` 自身。
-/
theorem identity_proof : P → P :=
  fun (h : P) => h

-- 语法糖版本
-- Lean 可以自动推断 h 的类型，所以可以简写
theorem identity_proof_short : P → P :=
  fun h => h

-- 甚至可以使用 Unicode lambda 符号 (输入 \fun 或 \lambda)
theorem identity_proof_unicode : P → P :=
  λ h => h

```
**代码详解：**

- `fun ... => ...`：这是定义 **匿名函数（Lambda Expression）** 的标准语法。
- `h`：在策略模式中，它是 `intro h` 引入的假设；在项式证明中，它就是函数的**形式参数**。
- `=> h`：这是函数的**返回值**。因为 `h` 的类型是 `P`，所以返回 `h` 就满足了 `P → P` 的类型要求。

### 5.1.3 进阶 Toy Case：丢弃参数 (Const Function)
现在看一个稍微复杂一点的：$P \to Q \to P$。
这表示：“如果 P 成立，那么（如果 Q 成立，则 P 成立）”。

```lean
variable (Q : Prop)

/--
  名称: ignore_q（第一蕴含公理）
  描述: 对于任意命题 P 和 Q，P → Q → P
  输入: hp : P, hq : Q
  输出: P 的证明

  证明思路：
  1. 我们需要构造一个函数，接受参数 `hp : P`。
  2. 这个函数返回另一个函数，类型为 `Q → P`。
  3. 内部函数接受参数 `hq : Q`。
  4. 最终需要返回一个类型为 `P` 的值。我们手头正好有 `hp`。
-/
theorem ignore_q : P → Q → P :=
  fun (hp : P) =>     -- 第一层函数，拿到 P 的证据
    fun (hq : Q) =>   -- 第二层函数，拿到 Q 的证据
      hp              -- 返回 P 的证据，忽略 hq

-- 简写形式：多个参数可以写在同一个 fun 后面
theorem ignore_q_compact : P → Q → P :=
  fun hp hq => hp

```
**深度思考**：
这也解释了为什么逻辑蕴含是**右结合**的。`P → Q → P` 实际上是 `P → (Q → P)`。
如果你是程序员，你会发现这不就是 `const` 函数吗？`const x y = x`。是的，逻辑公理就是这么朴实无华。

---

## 5.2 函数应用与组合：逻辑推导的引擎

### 5.2.1 函数应用 (Function Application)

> **Modus Ponens（肯定前件律）**：如果已知 P → Q 成立，且已知 P 成立，那么 Q 成立。在项式证明中，这对应于函数应用——将函数 `f : P → Q` 作用于参数 `h : P`，得到 `f h : Q`。

在逻辑中，最著名的推理规则是 **肯定前件律 (Modus Ponens)**：
如果已知 P→Q 成立，且已知 P 成立，那么 Q 成立。在项式证明中，这不仅仅是“规则”，这是**函数调用**。

- $f : P \to Q$ 是一个函数。
- $h : P$ 是一个参数。
- $f(h)$ 或简写为 `f h`，其类型就是 $Q$。

### 5.2.2 Toy Case：证明传递性 (Transitivity)
我们来证明 $(P \to Q) \to (Q \to R) \to (P \to R)$。

```lean
variable (R : Prop)

/--
  名称: trans_proof（蕴含传递性）
  描述: (P → Q) → (Q → R) → (P → R)
  输入:
    hpq : P → Q  (即：拥有一个能把 P 变成 Q 的函数)
    hqr : Q → R  (即：拥有一个能把 Q 变成 R 的函数)
    hp  : P      (即：拥有一个原始材料 P)
  输出: R 的证明
-/
theorem trans_proof : (P → Q) → (Q → R) → (P → R) :=
  fun (hpq : P → Q) (hqr : Q → R) (hp : P) =>
    -- 我们的目标是构造出 R。
    -- 1. 手头有 hp : P。
    -- 2. 可以喂给 hpq，得到 (hpq hp) : Q。
    -- 3. 手头现在有了 Q，可以喂给 hqr，得到 (hqr (hpq hp)) : R。
    hqr (hpq hp)

-- 使用函数组合算子 (Function Composition)
-- 符号 `∘` 可以输入 \circ
theorem trans_proof_compose : (P → Q) → (Q → R) → (P → R) :=
  fun hpq hqr => hqr ∘ hpq

```
**初学者提示**：
阅读项式证明时，从内向外读：
`hqr (hpq hp)`

1. `(hpq hp)`：利用 $P \to Q$ 和 $P$ 得到 $Q$。
2. `hqr (...)`：利用 $Q \to R$ 和 $Q$ 得到 $R$。
这就是逻辑推导链！

### 5.2.3 练习：交换律的变体
尝试证明：$(P \to Q \to R) \to (Q \to P \to R)$。

```lean
/--
  名称: flip_args（参数交换）
  描述: 交换前两个假设的顺序，在编程中称为 "Argument Flip"
  输入: h : P → Q → R, hq : Q, hp : P
  输出: R 的证明
-/
theorem flip_args : (P → Q → R) → (Q → P → R) :=
  fun (h : P → Q → R) =>  -- 拿到那个复杂的函数 h
  fun (hq : Q) =>         -- 拿到参数 Q
  fun (hp : P) =>         -- 拿到参数 P
    -- 现在的目标是 R。
    -- 我们看看手里的 h，它需要先吃 P，再吃 Q，才能吐出 R。
    -- 所以我们按顺序喂给它：
    h hp hq

```

---

## 5.3 匿名构造器：处理"与"和"存在"

> **匿名构造器 ⟨...⟩**：Lean 提供的通用构造语法，可根据上下文自动推断要构造的类型。用 `⟨a, b⟩` 构造"与"（∧）的证明，用 `⟨witness, proof⟩` 构造"存在"（∃）的证明，无需显式写出构造函数名。

之前的例子都只涉及蕴含（函数）。对于 `And` ($\land$)、`Or` ($\lor$) 和 `Exists` ($\exists$)，我们需要了解 Lean 的 **归纳类型（Inductive Types）** 构造方式。
Lean 提供了一个通用的 **匿名构造器语法 ⟨...⟩**（输入 `\<` 和 `\>`），它可以根据上下文自动推断你要构造什么类型的对象。

### 5.3.1 构造 "与" (And Introduction)
要证明 $P \land Q$，我们需要同时提供 $P$ 的证明和 $Q$ 的证明。
在策略模式中，我们用 `constructor`。在项式证明中，我们直接打包。

```lean
/--
  名称: and_comm_term（与的交换律）
  描述: P ∧ Q → Q ∧ P
  输入: h : P ∧ Q（P 与 Q 同时成立的证明）
  输出: Q ∧ P 的证明
-/
theorem and_comm_term : P ∧ Q → Q ∧ P :=
  fun (h : P ∧ Q) =>
    -- h 是一个配对 (pair)。
    -- h.left 是 P 的证明，h.right 是 Q 的证明。
    -- 我们要返回一个 Q ∧ P，可以使用 ⟨Q_proof, P_proof⟩。
    ⟨h.right, h.left⟩

```

### 5.3.2 构造 "存在" (Exists Introduction)
命题 $\exists x : \alpha, p(x)$ 本质上也是一个配对（Dependent Pair）：

1. 一个具体的数值 $w$ (Witness)。
2. 一个证明该数值满足性质的证据 $h$。

```lean
/--
  名称: 存在偶数示例
  描述: 证明存在一个自然数是偶数
  输入: 无
  输出: ∃ n : Nat, n % 2 = 0 的证明
-/
example : ∃ n : Nat, n % 2 = 0 :=
  -- 我们选择 n = 4 作为证人(witness)
  -- 然后我们需要证明 4 % 2 = 0。
  -- ⟨数值, 证明⟩
  ⟨4, rfl⟩ 
  -- rfl 表示自反性，因为 4%2 计算结果就是 0，0=0 是显然的。

```

### 5.3.3 构造 "或" (Or Introduction)
`Or` 类型有点不同，它不是配对，而是选择（Sum Type）。要证明 $P \lor Q$，我们需要证明 $P$**或者** 证明 $Q$。
Lean 使用构造函数 `Or.inl` (left) 和 `Or.inr` (right)。

```lean
/--
  名称: or_intro_left（或的左引入）
  描述: P → P ∨ Q
  输入: hp : P
  输出: P ∨ Q 的证明
-/
theorem or_intro_left : P → P ∨ Q :=
  fun (hp : P) => Or.inl hp

/--
  名称: or_intro_right（或的右引入）
  描述: Q → P ∨ Q
  输入: hq : Q
  输出: P ∨ Q 的证明
-/
theorem or_intro_right : Q → P ∨ Q :=
  fun (hq : Q) => Or.inr hq

```

---

## 5.4 结构化证明：have, let, show
当证明变得复杂时，一行写完所有的 lambda 表达式会变得极其难读（就像写一行 200 个字符的 Python 代码）。Lean 提供了结构化关键字来帮助我们分步思考。

### 5.4.1 `have`：引入中间结论
`have` 允许你定义一个局部的引理。这相当于在证明过程中打一个“存盘点”。
**语法**：`have 名字 : 类型 := 证明项; 后续代码`

### Toy Case：复杂的逻辑组合
我们要证明：$(P \to Q) \land (Q \to R) \to (P \to R)$。

```lean
/--
  名称: logic_chain（逻辑链）
  描述: (P → Q) ∧ (Q → R) → (P → R)
  输入: h : (P → Q) ∧ (Q → R), hp : P
  输出: R 的证明
-/
theorem logic_chain : (P → Q) ∧ (Q → R) → (P → R) :=
  fun (h : (P → Q) ∧ (Q → R)) =>
  fun (hp : P) =>
    -- 1. 拆解假设 h，让代码更清晰
    have hpq : P → Q := h.left
    have hqr : Q → R := h.right
    
    -- 2. 利用 hpq 得到 Q
    have hq : Q := hpq hp
    
    -- 3. 利用 hqr 得到 R
    have hr : R := hqr hq
    
    -- 4. 返回最终结果
    hr

```
**对比**：如果不使用 `have`，代码是 `fun h hp => h.right (h.left hp)`。虽然短，但在逻辑非常深的时候，`have` 这种**给中间变量命名**的习惯非常重要。

### 5.4.2 `show`：明确目标
`show` 关键字用于告诉 Lean（以及阅读代码的人）：“我现在要构造的是这个类型的项”。

```lean
/--
  名称: clearly_stated（明确目标示例）
  描述: P ∧ Q → P
  输入: h : P ∧ Q
  输出: P 的证明
-/
theorem clearly_stated : P ∧ Q → P :=
  fun h =>
    show P from h.left

```
这在处理复杂的类型推断，或者你想重申当前目标时非常有用。

### 5.4.3 `let` 与模式匹配解构
`let` 通常用于定义数据，但在解构复杂对象时比 `have` 更灵活。我们可以使用 `let ⟨...⟩ := ...` 来拆解构造。

```lean
/--
  名称: destructuring_example（解构示例）
  描述: P ∧ Q → Q ∧ P，使用 let 模式匹配解构
  输入: h : P ∧ Q
  输出: Q ∧ P 的证明
-/
theorem destructuring_example : P ∧ Q → Q ∧ P :=
  fun h =>
    -- 直接把 h 拆成 hp 和 hq
    let ⟨hp, hq⟩ := h
    -- 现在可以直接使用 hp 和 hq
    ⟨hq, hp⟩

```
这种写法比 `h.left` 和 `h.right` 更优雅，特别是当嵌套层级很深的时候。

---

## 5.5 混合证明与最佳实践
在实际开发中，极端的策略模式和极端的项式证明都有缺点。

- **纯策略**：代码冗长，难以维护，看不出逻辑流。
- **纯项式**：对于复杂的重写（Rewriting）和运算，手写证明项简直是折磨。

**最佳实践是混合使用**。

### 5.5.1 在项中使用策略 (`by`)
你可以在任何期望出现“项”的地方，插入一个 `by ...` 代码块。

```lean
example (p q : Prop) : p ∨ q → q ∨ p :=
  fun h =>
    match h with
    | Or.inl hp => by apply Or.inr; exact hp -- 这一分支用策略写
    | Or.inr hq => Or.inl hq                 -- 这一分支用项写

```

### 5.5.2 在策略中使用项 (`exact`)
在策略模式中，如果你已经一眼看出了答案，直接用 `exact` 提供证明项是最快的。

```lean
example (p q : Prop) : p ∧ q → p := by
  intro h
  -- 不需要写 cases h, 不需要 apply And.left
  -- 直接给出精确的项
  exact h.left

```

### 5.5.3 何时选择项式证明？

1. **简单逻辑**：如 `fun h => h` 或 `fun h => h.left`。
2. **结构操作**：如 `⟨h1, h2⟩`。
3. **高阶函数**：当你在处理传递性、交换律等组合逻辑时，项式证明往往比 `intro; apply; apply` 更直观。

---

## 本章小结

1. **证明即程序**：通过 Curry-Howard 同构，我们理解了命题就是类型、证明就是程序的核心思想，使用 `fun` 构造蕴含的证明，通过函数应用执行逻辑推导。
2. **匿名构造器**：使用 `⟨...⟩` 这一通用语法来构造"与"（∧）和"存在"（∃）的证明，使用 `Or.inl` / `Or.inr` 构造"或"（∨）的证明。
3. **结构化关键字**：使用 `have` 引入中间结论、`let` 解构复杂对象、`show` 明确当前目标，使复杂证明像写命令式代码一样清晰。
4. **混合证明**：在实际开发中，项式证明与策略式证明各有所长，最佳实践是根据场景灵活混合使用。

此时，你已经具备了"双语"能力（策略语言和项语言）。在接下来的章节中，我们将探索 Lean 中最强大的功能之一：**归纳类型与归纳证明**。

---

## 练习题

1. **Currying (柯里化)**：
请用项式证明（不使用 `by`）完成以下定理：
`theorem curry_proof : (P ∧ Q → R) → (P → Q → R) := sorry`
2. **Uncurrying (反柯里化)**：
`theorem uncurry_proof : (P → Q → R) → (P ∧ Q → R) := sorry`
3. **逻辑等价**：
`iff_def` 定义为 `(P → Q) ∧ (Q → P)`。请证明：
`theorem iff_refl : P ↔ P := sorry`*(提示：回顾 5.1.2 的 identity_proof)*
