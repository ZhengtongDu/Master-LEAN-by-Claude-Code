# 第六章：策略式证明（Tactics）

> **本章目标**：
> 1. **理解策略模式**：掌握 `by` 关键字开启的交互式证明方式，学会阅读 Infoview 中的证明状态。
> 2. **基础三板斧**：熟练使用 `intro`、`apply`、`exact` 完成基础逻辑推演。
> 3. **逻辑策略**：掌握 `constructor`、`cases`、`rcases` 处理 And/Or/Exists。
> 4. **重写与化简**：使用 `rw`、`simp`、`ring` 进行等式变换与自动化简。
> 5. **组合与结构化**：使用 `·` 和 `<;>` 保持证明代码的整洁可读。

---

## 6.1 策略模式入门

### 6.1.1 什么是策略（Tactic）？

> **策略 (Tactic)**：策略是一个元程序（Meta-program），它接收当前的证明状态（Proof State），对其进行变换，生成新的证明状态或完成证明。与项模式（Term Mode）手动构造证明项不同，策略模式通过一系列指令逐步推进证明。

- **Term Mode**: 你手动拼装乐高积木。
- **Tactic Mode**: 你对机器人发指令：“把红色的积木放在蓝色的上面”，机器人帮你拼装。

### 6.1.2 进入策略模式：`by`

关键字 `by` 是通往策略世界的传送门。一旦输入 `by`，Lean 的编译器就会暂停期待一个"值"，转而期待一系列"指令"。

### 6.1.3 核心：阅读 Infoview（证明状态）

在 VS Code 中，将光标放在 `by` 块内是至关重要的。右侧的 Infoview 会显示当前的 **Tactic State**，它包含两部分：

1. **Local Context (上下文)**: 你当前拥有的牌（假设、变量）。符号为 `x : Nat`, `h : P`。
2. **Goal (目标)**: 你当前需要打出的牌（待证命题）。符号为 `⊢ P`（Turnstile 符号）。

### Toy Case 1：初次体验

我们来证明一个简单的等式 $1 + n = n + 1$。

```lean
/-- 名称: 加法交换律示例
    输入: n : Nat（自然数）
    输出: 1 + n = n + 1 的证明 -/
-- 这是一个命题，类型是 Prop
-- 在项模式下，我们需要写：Eq.symm (Nat.add_comm n 1)
example (n : Nat) : 1 + n = n + 1 := by
  -- [Step 1] 光标在此处时，Infoview 显示：
  -- n : Nat
  -- ⊢ 1 + n = n + 1
  
  -- 我们的策略是：利用加法交换律。
  -- 这是一个重写（rewrite）操作。
  rw [Nat.add_comm] 
  
  -- [Step 2] 执行后，Infoview 显示：
  -- No goals
  -- 这意味着证明已完成。

```

---

## 6.2 基础策略：intro, apply, exact

> **intro/apply/exact 三板斧**：`intro` 将目标中的前提引入上下文（"假设 P 成立"），`apply` 对目标进行逆向推理（"要证 Q，只需证 P"），`exact` 用精确匹配的假设或引理关闭当前目标。三者配合可完成绝大多数基础逻辑推演。

这是策略模式的"三板斧"，通过它们可以完成绝大多数基础逻辑推演。

### 6.2.1 `intro`：拆解全称量词与蕴含

当目标（Goal）的形式是 `P → Q` 或 `∀ x, P x` 时，我们需要将前提移动到上下文中。

- **原理**：为了证明“如果 P 则 Q”，我们先“假设 P 成立”，然后在该假设下证明 Q。

### 6.2.2 `exact`：精确匹配

这是证明的终结者。当你手中的某张牌（假设或引理）与目标**完全一致**时，使用 `exact`。

- **注意**：它必须精确匹配（定义上的相等是可以的）。

### 6.2.3 `apply`：逆向推理

这是最常用的策略之一。

- **场景**：目标是 $Q$，你有一个引理 $h: P \to Q$。
- **操作**：`apply h`。
- **结果**：Lean 会说：“好吧，既然你有 $P \to Q$，为了证明 $Q$，你现在只需要证明 $P$ 即可。” 目标从 $Q$ 变成了 $P$。

### Toy Case 2：三段论推理

证明：如果 $P \to Q$ 且 $Q \to R$，那么 $P \to R$。

```lean
variable (P Q R : Prop)

/-- 名称: 三段论推理
    输入: P Q R : Prop（三个命题）
    输出: (P → Q) → (Q → R) → (P → R) 的证明 -/
example : (P → Q) → (Q → R) → (P → R) := by
  -- 初始目标：⊢ (P → Q) → (Q → R) → P → R
  
  -- 1. 引入所有前提
  -- 我们可以给假设起有意义的名字：h_pq (P推Q), h_qr (Q推R), h_p (P成立)
  intro h_pq h_qr h_p
  
  -- 状态检查：
  -- h_pq : P → Q
  -- h_qr : Q → R
  -- h_p : P
  -- ⊢ R
  
  -- 2. 逆向思考：我们需要证明 R。
  -- 我们手里有 h_qr : Q → R。如果我们能通过它，目标就变成了 Q。
  apply h_qr
  
  -- 当前目标：⊢ Q
  
  -- 3. 继续逆向：为了证明 Q，利用 h_pq : P → Q。
  apply h_pq
  
  -- 当前目标：⊢ P
  
  -- 4. 终结：我们需要证明 P，而 h_p 正好就是 P。
  exact h_p

```
新手提示：如果不知道用哪个假设，可以尝试 assumption 策略，它会自动在 Context 中寻找能直接 exact 的假设。

---

## 6.3 逻辑策略：constructor, cases, rcases

> **constructor/cases/rcases**：`constructor` 将复合目标（如 `P ∧ Q`）拆分为多个子目标；`cases` 对假设进行模式匹配，分情况讨论；`rcases` 是 `cases` 的递归增强版，支持嵌套模式一次性拆解复杂结构。处理逻辑连接词时，关键在于区分"作为目标"和"作为假设"两种场景。

逻辑连接词（And, Or, Exists）在"作为目标"和"作为假设"时的处理方式截然不同。这是一个常见的痛点。

### 逻辑操作速查表

| 连接词 | 作为目标 (Goal) ⊢ ... | 作为假设 (Context) h : ... |
| --- | --- | --- |
| And (∧) | constructor (拆分为两个子目标) | cases h (拆分为两个假设) |
| Or (∨) | left 或 right (选择证明一边) | cases h (分情况讨论) |
| Exists (∃) | use x (提供证据) | cases h (提取值和性质) |
| True / False | trivial (True) / exfalso (利用False爆炸) | cases h (False 推出一切) |

### 6.3.1 `constructor` 与 `cases`

- **constructor**：尝试应用当前类型的主构造函数。对于 $\land$，就是生成两个子目标。
- **cases**：对假设进行模式匹配。

### 6.3.2 `rcases` / `rintro`：强力模式匹配

标准的 `cases` 在处理嵌套结构（如 $P \land Q \land R$）时会产生非常深的缩进。`rcases` (Recursive Cases) 允许我们使用模式字符串一次性拆解。

- 语法：`rcases h with ⟨h1, h2⟩` （尖括号输入法：`\<``\>`）

### Toy Case 3：逻辑综合演练

证明：$(P \lor Q) \land R \to (P \land R) \lor (Q \land R)$。

```lean
/-- 名称: 分配律（Or 对 And 的分配）
    输入: P Q R : Prop（三个命题）
    输出: (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) 的证明 -/
example : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) := by
  -- 推荐使用 rintro 直接引入并拆解
  -- ⟨h_or, h_r⟩ 对应 (P ∨ Q) 和 R
  intro h
  rcases h with ⟨h_or, h_r⟩
  
  -- 状态：
  -- h_or : P ∨ Q
  -- h_r : R
  -- ⊢ (P ∧ R) ∨ (Q ∧ R)
  
  -- h_or 是一个“或”假设，必须分情况讨论
  cases h_or with
  | inl h_p => 
    -- [分支 1] 假设 P 成立
    -- 目标：⊢ (P ∧ R) ∨ (Q ∧ R)
    left -- 选择证明左边
    constructor -- 拆解 And 目标
    · exact h_p -- 证明 P
    · exact h_r -- 证明 R
    
  | inr h_q =>
    -- [分支 2] 假设 Q 成立
    -- 目标：⊢ (P ∧ R) ∨ (Q ∧ R)
    right -- 选择证明右边
    constructor
    · exact h_q
    · exact h_r

```

---

## 6.4 重写策略：rw, simp, ring

> **rw/simp/ring**：`rw`（rewrite）是精确的手术刀，按指定引理对目标或假设进行定向替换；`simp`（simplify）是自动化简器，利用标记为 `@[simp]` 的引理库将目标化简到最简形式；`ring` 专门处理环论代数式（含 `+`、`-`、`*`），自动完成结合律、分配律等变换。

数学证明不仅仅是逻辑推演，更多时候是等式变换。

### 6.4.1 `rw` (rewrite)：手术刀式的重写

- `rw [lemma]`：在目标中寻找 `lemma` 的左边（LHS），替换为右边（RHS）。
- `rw [← lemma]`：从右向左替换（`\l` 输入左箭头）。
- `rw [lemma] at h`：在假设 `h` 中进行替换，而不是在目标中。

### 6.4.2 `simp` (simplify)：扫地机器人

`simp` 是 Lean 的杀手级功能。它不仅进行重写，还会使用一个巨大的标准库引理集（tagged with `@[simp]`）来自动简化目标。

- **区别**：`rw` 只有你叫它动它才动；`simp` 会尝试把目标化简到最简形式。

### 6.4.3 `ring`：环论自动机

对于涉及 $+ - * $ 的代数式，不要手动 `rw` 结合律或分配律，直接用 `ring`。

### Toy Case 4：代数变换

```lean
import Mathlib.Tactic.Ring -- 必须导入

/-- 名称: 完全平方公式
    输入: a b : Nat（两个自然数）
    输出: (a + b)^2 = a^2 + 2*a*b + b^2 的证明 -/
example (a b : Nat) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  -- 如果用 rw，你需要：
  -- rw [pow_two]
  -- rw [add_mul]
  -- rw [mul_add] ... (非常痛苦)
  
  ring -- 一键完成！

```

---

## 6.5 自动化策略：decide, aesop, omega

Lean 4 引入了极强的自动化策略，尤其适合计算机科学背景的用户。

### 6.5.1 `decide`：可判定性

如果一个命题是"可计算的"（computable），Lean 可以直接运行代码来验证它。

```lean
/-- 名称: decide 示例
    输入: 无
    输出: 20 * 5 = 100 的证明 -/
example : 20 * 5 = 100 := by decide

```

### 6.5.2 `omega`：整数算术求解器

这是处理自然数（Nat）和整数（Int）线性不等式的最强工具。它实现了 Presburger 算术。

- **场景**：索引计算、数组边界检查、循环不变量。

### Toy Case 5：复杂不等式

```lean
/-- 名称: omega 不等式推导
    输入: n m : Nat, h1 : n > 0, h2 : m > n
    输出: m ≥ 2 的证明 -/
example (n m : Nat) (h1 : n > 0) (h2 : m > n) : m ≥ 2 := by
  -- 手动证明需要利用不等式的传递性 n ≥ 1, m ≥ n + 1 等
  omega -- 自动推导

```

### 6.5.3 `aesop`：自动化证明搜索

`aesop` (Automated Extensible Search for Obvious Proofs) 类似于 Prolog 的搜索。它会尝试应用各种 `intro`, `cases`, `apply` 组合。

```lean
/-- 名称: aesop 逻辑交换
    输入: P Q : Prop
    输出: P ∧ Q → Q ∧ P 的证明 -/
example : P ∧ Q → Q ∧ P := by aesop -- 自动完成逻辑交换

```

---

## 6.6 组合策略与结构化：<;>, ·

为了保持代码整洁，我们需要结构化工具。

### 6.6.1 `·` (Bullet Point)

当证明产生多个分支时（如 `cases` 或 `constructor`），使用 `·` 来隔离作用域。

- **好处**：防止分支 A 的变量污染分支 B，如果分支 A 没有证完，Lean 会报错，保证你专注于当前目标。

### 6.6.2 `<;>` (Combinator)

分号操作符。`tac1 <;> tac2` 表示："先执行 `tac1`，然后对 `tac1` 产生的所有**每一个**子目标都执行 `tac2`"。

### Toy Case 6：优雅的结构化证明

证明：对于任意 $x$，如果 $x=0$ 或 $x=1$，那么 $x*(x-1)=0$。

```lean
/-- 名称: 结构化证明示例
    输入: x : Nat, h : x = 0 ∨ x = 1
    输出: x * (x - 1) = 0 的证明 -/
example (x : Nat) (h : x = 0 ∨ x = 1) : x * (x - 1) = 0 := by
  cases h with -- 产生两个分支
  | inl h0 => -- 分支 1：x = 0
    rw [h0]
    -- 目标：0 * (0 - 1) = 0
    simp -- 0 乘任何数得 0
    
  | inr h1 => -- 分支 2：x = 1
    rw [h1]
    -- 目标：1 * (1 - 1) = 0
    simp -- 1-1=0, 1*0=0

```

使用 `<;>` 优化：

```lean
/-- 名称: 组合策略优化版
    输入: x : Nat, h : x = 0 ∨ x = 1
    输出: x * (x - 1) = 0 的证明（使用 <;> 组合） -/
example (x : Nat) (h : x = 0 ∨ x = 1) : x * (x - 1) = 0 := by
  cases h <;> rename_i h_val -- 对每个分支，重命名假设为 h_val
  -- 此时有两个目标，但可以并行处理
  <;> rw [h_val] -- 在所有分支中，都把 x 替换成具体的值
  <;> simp       -- 在所有分支中，都进行化简

```

---

## 本章小结

1. **心智模型**：策略模式是操作 Proof State 的状态机。始终关注 Infoview。
2. **基础操作**：`intro` (进), `apply` (退), `exact` (准)。
3. **逻辑处理**：分清 Goal 和 Hypothesis。Goal 用 `constructor/left/right`，Hypothesis 用 `cases`。
4. **计算与重写**：`rw` 是手术刀，`simp` 是清洁工，`ring` 和 `omega` 是重型机械。
5. **代码风格**：使用 `·` 和 `rcases` 保持证明的可读性。

---

## 练习题

1. **逻辑双加**：使用策略模式证明德摩根定律的一个方向：`¬(P ∨ Q) → ¬P ∧ ¬Q`。（提示：`¬P` 实际上是 `P → False`）。
2. **代数狂热**：定义函数 `f x = 2*x + 1`，使用 `rw` 和 `ring` 证明 `f (a + b) = f a + 2*b`。
3. **初识归纳**：尝试使用 `induction n` 策略证明 `0 + n = n`（虽然 `simp` 可以解决，试着手动用策略做）。
