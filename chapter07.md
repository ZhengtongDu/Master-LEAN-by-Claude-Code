# 第七章：归纳与递归 (Induction and Recursion)

> **本章目标**：
> 1. **从零构建世界**：掌握 `inductive` 关键字定义自然数、列表、树等数据结构。
> 2. **归纳证明**：通过数学归纳法的推广形式（结构归纳法）证明程序的正确性。
> 3. **征服无限**：理解良基递归（Well-Founded Recursion），确保递归函数终止。
> 4. **互递归与嵌套**：处理互相调用的函数和嵌套归纳类型。

---

## 7.1 归纳类型的定义
在 Lean 中，`inductive` 关键字不仅仅是用来定义“枚举”或“结构体”的，它是定义**数据本质**的唯一方式。

### 7.1.1 剖析 `inductive`
一个归纳类型由一组**构造子 (Constructors)** 定义。这些构造子给出了生成该类型值的**所有**可能方式。

```lean
-- 这是一个最基本的枚举类型
inductive Weekday where
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  -- ... 其他省略

```

> **封闭世界假设 (Closed World Assumption)**：当你定义 `Weekday` 时，Lean 实际上生成了一条公理：*除了这几个构造子，没有任何其他方式可以生成 Weekday*。这就是为什么我们可以通过"分情况讨论"（Pattern Matching）来处理它——因为情况是有限且确定的。

### 7.1.2 参数 (Parameters) vs 索引 (Indices)

这是初学者最容易混淆的概念。

- **参数 (Parameters)**：在整个类型定义中保持不变的变量。例如 `List α` 中的 `α`。
- **索引 (Indices)**：在不同的构造子中可以发生变化的类型参数。这通常用于定义依赖类型（Dependent Types）或逻辑谓词。

**Toy Case：定义定长向量 (Vectors)**
这里 `α` 是参数（所有元素类型相同），而 `n : Nat` 是索引（不同长度的向量是不同的类型）。

```lean
-- 定义：Vector α n 表示长度为 n 的列表
inductive Vector (α : Type) : Nat → Type where
  | nil  : Vector α 0                             -- 长度为 0 的空向量
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1) -- 在长度为 n 的向量前加一个元素，变成长度 n+1

-- 使用示例
def v1 : Vector String 1 := Vector.cons "Lean" Vector.nil
-- 下面这行代码会报错，因为类型系统知道长度不匹配
-- def v_error : Vector String 2 := Vector.cons "Lean" Vector.nil 

```

### 7.1.3 递归数据结构：二叉树
让我们定义一个泛型二叉树，并编写一个函数来“镜像”反转它。

```lean
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node (left : BinTree α) (val : α) (right : BinTree α) : BinTree α
deriving Repr -- 让 Lean 能够打印这个结构

open BinTree -- 打开命名空间，方便直接使用 leaf 和 node

/-- size: 计算树中节点的数量
  输入: t — 二叉树
  输出: 节点数量（Nat）
-/
def size {α : Type} : BinTree α → Nat
  | leaf => 0
  | node l _ r => 1 + size l + size r

/-- mirror: 镜像反转一棵树
  输入: t — 二叉树
  输出: 左右子树互换后的二叉树
-/
def mirror {α : Type} : BinTree α → BinTree α
  | leaf => leaf
  | node l v r => node (mirror r) v (mirror l) -- 递归调用

-- 测试代码
def t1 := node (node leaf 1 leaf) 2 (node leaf 3 leaf)
#eval size t1   -- 输出: 3
#eval mirror t1 -- 输出: node (node leaf 3 leaf) 2 (node leaf 1 leaf)

```

---

## 7.2 自然数归纳法
自然数 `Nat` 是理解归纳法的基石。在 Lean 中，`Nat` 定义如下：

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

```

### 7.2.1 归纳原理

> **归纳原理 (Induction Principle)**：当我们证明关于自然数 `n` 的命题 `P(n)` 时，Lean 提供的 `induction` 策略实际上是在应用以下逻辑：如果 `P(0)` 成立，且对任意 `k`，`P(k)` 能推出 `P(k+1)`，则 `P(n)` 对所有自然数成立。

$$
(P(0) \land \forall k, P(k) \to P(k+1)) \implies \forall n, P(n)
$$

### Toy Case：高斯求和公式
我们要证明：$0 + 1 + ... + (n-1) = \frac{n(n-1)}{2}$。
为了避免自然数除法的麻烦，我们证明变形公式：`2 * sum_to n = n * (n - 1)`。

```lean
/-- sum_to: 计算 0 到 n-1 的自然数之和
  输入: n — 自然数上界
  输出: 0 + 1 + ... + (n-1) 的和
-/
def sum_to : Nat → Nat
  | 0 => 0
  | n + 1 => n + sum_to n

/-- sum_formula: 高斯求和公式
  输入: n — 自然数
  输出: 2 * sum_to n = n * (n - 1) 的证明
-/
theorem sum_formula (n : Nat) : 2 * sum_to n = n * (n - 1) := by
  -- 使用归纳法，将 n 分为 zero 和 succ n' 两种情况
  induction n with
  | zero =>
    -- 基础情况：n = 0
    -- 目标：2 * sum_to 0 = 0 * (0 - 1)
    -- 计算：2 * 0 = 0，0 * 0 = 0
    rfl 
  | succ n ih =>
    -- 归纳步骤：n = succ n (即 n + 1)
    -- 归纳假设 (ih): 2 * sum_to n = n * (n - 1)
    -- 目标：2 * sum_to (n + 1) = (n + 1) * n
    
    -- 1. 展开 sum_to 的定义: sum_to (n+1) => n + sum_to n
    dsimp [sum_to]
    
    -- 2. 利用乘法分配律展开左边: 2 * (n + sum_to n) => 2 * n + 2 * sum_to n
    rw [Nat.mul_add]
    
    -- 3. 关键步骤：使用归纳假设 ih 替换 2 * sum_to n
    rw [ih]
    
    -- 此时目标变为: 2 * n + n * (n - 1) = (n + 1) * n
    -- 剩下的就是纯代数运算了。
    -- omega 策略可以自动处理自然数上的线性算术
    omega

```

> **新手提示**：`dsimp` 用于简化定义，`rw` 用于重写等式。归纳证明的核心就在于如何构造出可以使用 `ih`（归纳假设）的形状。

---

## 7.3 结构归纳法

归纳法不仅限于数字。对于任何归纳定义的数据结构（列表、树、逻辑表达式），我们都可以使用结构归纳法。

### 7.3.1 什么是结构归纳？

> **结构归纳法 (Structural Induction)**：如果要证明属性 P 对某棵树成立，只需证明它对叶子成立，且假设它对左右子树成立从而推导出它对当前节点成立。更一般地，对于任何归纳类型，只需对每个构造子证明：假设所有递归子项满足 P，则当前项也满足 P。

### Toy Case：列表反转的性质
这是一个经典的入门难题。我们要证明 `reverse (xs ++ ys) = reverse ys ++ reverse xs`。
直接证明会卡住，我们需要先证明一个引理。

```lean
variable {α : Type}

-- 定义连接和反转（标准库已有，我们重新定义以展示原理）
/-- app: 连接两个列表
  输入: xs, ys — 两个列表
  输出: xs 和 ys 连接后的列表
-/
def app : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys

/-- rev: 反转列表
  输入: xs — 列表
  输出: 元素顺序反转后的列表
-/
def rev : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

/-- app_assoc: 列表连接的结合律
  输入: xs, ys, zs — 三个列表
  输出: (xs ++ ys) ++ zs = xs ++ (ys ++ zs) 的证明
-/
theorem app_assoc (xs ys zs : List α) : app (app xs ys) zs = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => 
    dsimp [app]
    rw [ih]

/-- rev_app: 反转分配律
  输入: xs, ys — 两个列表
  输出: rev (xs ++ ys) = rev ys ++ rev xs 的证明
-/
theorem rev_app (xs ys : List α) : rev (app xs ys) = app (rev ys) (rev xs) := by
  induction xs with
  | nil =>
    -- 基础情况：xs = []
    -- rev ([] ++ ys) = rev ys
    -- rev ys ++ rev [] = rev ys ++ [] = rev ys
    simp [app, rev] 
  | cons x xs ih =>
    -- 归纳步骤：xs = x :: xs
    -- 目标：rev ((x :: xs) ++ ys) = rev ys ++ rev (x :: xs)
    
    -- 1. 展开左边定义
    dsimp [app, rev]
    -- 左边变为：app (rev (app xs ys)) [x]
    
    -- 2. 使用归纳假设 ih
    rw [ih]
    -- 左边变为：app (app (rev ys) (rev xs)) [x]
    
    -- 3. 展开右边定义
    -- 右边是：app (rev ys) (app (rev xs) [x])
    
    -- 4. 观察发现，左边是 (A ++ B) ++ C，右边是 A ++ (B ++ C)
    -- 这正是结合律！
    rw [app_assoc]

```

> **关键点**：`simp` 策略非常强大，它会自动应用已知的恒等式（如 `x ++ [] = x`）。但在学习阶段，手动 `rw` 有助于理解每一步发生了什么。

---

## 7.4 良基递归 (Well-Founded Recursion)

> **良基递归 (Well-Founded Recursion)**：当递归调用的参数不是输入的直接子结构时，需要提供一个"度量值"（Measure），证明该度量在每次递归中严格递减，从而保证函数终止。Lean 通过 `termination_by` 和 `decreasing_by` 支持这种递归模式。

到目前为止，我们写的函数都是**结构递归**：每次递归调用都剥离了一层构造子（如 `n` 变 `n-1`，列表 `head::tail` 变 `tail`）。Lean 可以自动判定这种递归是终止的。
但是，如果我们写的函数参数变化不那么明显呢？

### 7.4.1 `termination_by` 和 `decreasing_by`
如果我们定义一个对数函数 `log2 n`，递归调用是 `log2 (n / 2)`。`n / 2` 并不是 `n` 的直接子结构。此时 Lean 会报错，因为它无法确信程序会停止。
我们需要告诉 Lean：有一个“度量值”（Measure），在每次递归中都在减小。

### Toy Case：欧几里得除法
我们要实现 `div x y` (即 x / y)，逻辑是不断的 `x - y`。

```lean
/-- 这种写法会报错，因为 Lean 看不出 x - y 比 x 小 -/
-- def bad_div (x y : Nat) : Nat :=
--   if h : 0 < y ∧ y ≤ x then
--     1 + bad_div (x - y) y
--   else
--     0

/-- my_div: 使用良基递归实现的整数除法
  输入: x — 被除数, y — 除数
  输出: x / y 的商（Nat）
-/
def my_div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    1 + my_div (x - y) y
  else
    0
termination_by x -- 告诉 Lean：终止的依据是第一个参数 x 的大小
decreasing_by
  -- 这里我们需要证明：在递归调用的条件下，(x - y) < x
  simp_wf -- 简化 Well-Founded 目标
  -- 此时上下文中我们要证明 x - y < x
  -- 已知条件 h: 0 < y ∧ y ≤ x
  apply Nat.sub_lt
  · exact h.2.trans_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) h.1) -- 证明 x > 0 (稍微有点绕，只要证明 x >= y > 0)
    -- 或者更简单的：如果 y <= x 且 0 < y，则 x > 0
    apply Nat.lt_of_lt_of_le h.1 h.2 
  · exact h.1 -- 证明 y > 0

```

> **深入理解**：
> 1. **termination_by**：你指定一个映射，把函数的参数映射到一个已知是良基（即没有无限递减链）的集合，通常是自然数 `Nat`。
> 2. **decreasing_by**：这是一个战术块（Tactic Block），你需要在这里证明新的参数值确实比旧的小。

---

## 7.5 互递归与嵌套递归
现实世界的数据结构往往更加纠缠。

### 7.5.1 互递归 (Mutual Recursion)

当两个函数互相调用时，我们需要用 `mutual ... end` 块将它们包围起来。

**Toy Case：简单表达式求值器**
假设我们要定义一个算术表达式，它可以是数字，也可以是两个表达式的和。更有趣的是，我们允许表达式中包含一个“语句列表”，而语句中又包含表达式。

```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ_odd (n : Nat) : Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | succ_even (n : Nat) : Even n → Odd (n + 1)
end

```
*(注：上面的例子是归纳谓词的互递归。下面看函数的互递归)*

```lean
mutual
  /-- is_even: 判断自然数是否为偶数
    输入: n — 自然数
    输出: Bool
  -/
  def is_even : Nat → Bool
    | 0 => true
    | n + 1 => is_odd n

  /-- is_odd: 判断自然数是否为奇数
    输入: n — 自然数
    输出: Bool
  -/
  def is_odd : Nat → Bool
    | 0 => false
    | n + 1 => is_even n
end

#eval is_even 10 -- true

```

### 7.5.2 嵌套归纳 (Nested Induction)
当归纳类型出现在构造子的参数中时（例如 Rose Tree，多叉树），情况会变得复杂。

```lean
inductive RoseTree (α : Type) where
  | node : α → List (RoseTree α) → RoseTree α

-- 计算多叉树的所有节点数
mutual
  /-- count_nodes: 计算多叉树的节点数
    输入: t — 多叉树
    输出: 节点数量（Nat）
  -/
  def count_nodes : RoseTree α → Nat
    | RoseTree.node _ children => 1 + count_list children
    
  /-- count_list: 计算多叉树列表中的总节点数
    输入: ts — 多叉树列表
    输出: 所有树的节点数之和（Nat）
  -/
  def count_list : List (RoseTree α) → Nat
    | [] => 0
    | t :: ts => count_nodes t + count_list ts
end

```

> **难点提示**：对于嵌套归纳类型，Lean 自动生成的递归原理（`rec`）往往非常难用。通常建议编写自定义的递归函数（如上所示），或者使用库中提供的更高级的归纳引理。

---

## 本章小结

1. **定义即公理**：`inductive` 定义不仅仅创建了数据结构，还创建了该结构的一致性规则（构造子）和处理规则（递归子）。
2. **归纳即递归**：在 Lean 中，证明（Proof）也是程序。数学归纳法本质上就是依附于自然数结构的递归函数。
3. **终止性至关重要**：Lean 必须保证所有函数终止以维持逻辑的一致性。对于复杂的递归逻辑，`termination_by` 是你与编译器对话的桥梁。

---

## 练习题

1. **斐波那契数列**：
定义 `fib : Nat → Nat`。尝试使用两种方式：
a) 简单的二重递归（可能会很慢）。
b) 尾递归优化版本（使用辅助函数积累结果）。
c) 证明两种定义等价（选做，难度较高）。
2. **树的遍历**：
定义二叉树的前序遍历 `preorder : BinTree α → List α`。
证明：`length (preorder t) = size t`。
3. **自定义归纳原理**：
定义一个类型 `inductive MyNat | zero | add2 (n : MyNat)` （这只生成偶数）。尝试为它编写一个递归函数。
