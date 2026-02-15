# 第2章：函数式编程与依赖类型理论基础

在第一章配置好环境后，我们现在正式进入 LEAN 的内核。

LEAN 不仅仅是一个用来验证数学定理的工具，它首先是一门**图灵完备的函数式编程语言**。这与你可能熟悉的 Python 或 C++ 有本质区别。在 LEAN 中，计算和证明是统一的：**证明即程序，命题即类型**（Propositions as Types）。

本章的目标是让你像习惯写 Python 一样习惯写 LEAN 代码，这是后续进行定理证明的必要基本功。

---

## 2.1 基础交互：求值与类型检查

打开 VS Code，创建一个新文件 `Chapter02.lean`。

### 2.1.1 两个核心命令

在 LEAN 的日常工作中，我们90%的时间在与这两个命令打交道：

1. `#eval` (Evaluate): 计算一个表达式的值。这相当于 Python 的 REPL 或 Jupyter Notebook 的单元格执行。
2. `#check` (Type Check): 询问一个表达式的**类型**。这是理解 LEAN "强类型"特性的关键。

### Toy Case: 基础数据类型概览

```lean
-- 1. 自然数 (Nat): 非负整数，这是数学证明中最常用的类型
#eval 1 + 1        -- 输出: 2
#check 1           -- 输出: 1 : Nat
#eval 5 - 10       -- 输出: 0 (注意：Nat 不能表示负数，下溢会归零)

-- 2. 整数 (Int): 需要显式处理符号
#check -5          -- 输出: -5 : Int
#eval (-5 : Int) + 2 -- 输出: -3

-- 3. 浮点数 (Float): 用于数值计算，但在纯数学证明中较少使用
#check 3.14        -- 输出: 3.14 : Float

-- 4. 布尔值 (Bool): true 或 false
#check true && false -- 输出: Bool

-- 5. 字符串 (String)
#eval "Hello" ++ " " ++ "World" -- 输出: "Hello World"
```

> **注意**: LEAN 重载了算术运算符。`+` 既可以用于 `Nat` 也可以用于 `Int`，但在同一个表达式中混用不同类型通常需要显式转换（cast）。

---

## 2.2 定义函数：从 `def` 到 Lambda

### 2.2.1 标准定义

使用 `def` 关键字定义函数。LEAN 要求显式声明参数类型，但返回类型通常可以由系统推断（虽然显式写出是好习惯）。

```lean
/-- f: 计算 x² + 3
    输入: x — 自然数
    输出: x * x + 3 — 自然数 -/
def f (x : Nat) : Nat :=
  x * x + 3

#eval f 5  -- 输出: 28
```

### 2.2.2 局部变量 (`let`)

在复杂的数学定义中，我们经常需要中间变量。使用 `let` 关键字：

```lean
/-- expensive_computation: 演示 let 局部变量的用法
    输入: x — 自然数
    输出: (x+10)² + (x+10) — 自然数
    过程: 先算 y = x+10，再算 z = y²，最后返回 z + y -/
def expensive_computation (x : Nat) : Nat :=
  let y := x + 10
  let z := y * y
  z + y

#eval expensive_computation 2 -- 计算过程: y=12, z=144, 结果=156
```

### 2.2.3 匿名函数 (Lambda 表达式)

在函数式编程中，函数是一等公民，可以作为参数传递，也可以作为返回值。我们经常需要定义没有名字的函数。

LEAN 提供了 `fun` 关键字，或者数学符号 `λ` (输入 `\la`)。

```lean
-- 写法 1: 使用 fun
#check fun x => x + 1

-- 写法 2: 使用 λ (更加数学化)
#check λ x => x + 1

-- 它们都是: Nat → Nat
```

### Toy Case: 高阶函数体验

让我们定义一个接受函数作为参数的函数。比如，将函数 $g$ 应用两次：$g(g(x))$。

```lean
/-- apply_twice: 将函数 g 对 x 连续应用两次，即计算 g(g(x))
    输入: g — 一个 Nat → Nat 的函数; x — 自然数
    输出: g(g(x)) — 自然数 -/
def apply_twice (g : Nat → Nat) (x : Nat) : Nat :=
  g (g x)

-- 使用匿名函数
#eval apply_twice (λ n => n * 2) 10
-- 计算过程: 10 * 2 = 20 -> 20 * 2 = 40
-- 输出: 40
```

---

## 2.3 柯里化 (Currying) 的深层逻辑

对于刚接触函数式编程的同学，柯里化是最容易困惑的概念。

在 LEAN 中，**所有函数本质上都只接受一个参数**。

当你看到 `Nat → Nat → Nat` 时，它实际上是 `Nat → (Nat → Nat)`。

### 图解柯里化

```lean
/-- add: 计算两个自然数之和
    输入: x, y — 自然数
    输出: x + y — 自然数 -/
def add (x : Nat) (y : Nat) : Nat := x + y

-- 1. 完整调用
#eval add 2 3      -- 5

-- 2. 部分应用 (Partial Application)
def add_two : Nat → Nat := add 2

-- add_two 现在是一个"等待"接收第二个参数的函数
#eval add_two 10   -- 12
```

> **核心观点**: 柯里化使得我们可以固定函数的某些参数，从而通过旧函数生成新函数。这在定理证明中非常有用，比如当我们证明性质 `∀ x, P x` 时，固定具体的 `x₀` 后，剩下的就是一个关于 `x₀` 的具体命题。

---

## 2.4 递归与模式匹配

LEAN 不是通过 `if ... then ... else` 来控制逻辑（虽然它支持），而是主要依赖**模式匹配 (Pattern Matching)**。同时，LEAN 中的循环通常通过**递归**实现。

### Toy Case: 阶乘与斐波那契数列

```lean
/-- factorial: 计算自然数的阶乘 n!
    输入: Nat — 自然数 n
    输出: Nat — n! (0!=1, (n+1)!=(n+1)×n!) -/
def factorial : Nat → Nat
  | 0 => 1              -- 基准情况 (Base Case)
  | n + 1 => (n + 1) * factorial n  -- 递归步骤

#eval factorial 5  -- 120

/-- fib: 计算第 n 个斐波那契数
    输入: Nat — 自然数 n
    输出: Nat — F(n)，其中 F(0)=0, F(1)=1, F(n+2)=F(n+1)+F(n) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval fib 7  -- 13
```

> **关键限制**: LEAN 是一个全函数 (Total Function) 语言。这意味着所有函数必须在有限步骤内终止。LEAN 必须能够证明你的递归会停机（例如参数在不断变小）。如果你写了一个死循环，LEAN 会在编译时报错，而不是运行时卡死。

---

## 2.5 类型理论核心：依赖类型、Universe 与 Prop

这是区分程序员与数学家的分水岭。请仔细阅读本节。

### 2.5.1 什么是依赖类型？

**依赖类型（Dependent Type）**：类型可以由值来参数化，即类型的定义中可以包含具体的值。

在普通类型系统（如 Java、Python）中，类型和值是两个独立的世界：
- 类型：`Int`, `String`, `List<Int>`
- 值：`42`, `"hello"`, `[1,2,3]`
- 类型不能"看到"值

而在依赖类型系统（如 LEAN）中，类型可以包含值作为参数：

```lean
-- 普通列表：类型不知道长度
def list1 : List Nat := [1, 2, 3]       -- List Nat
def list2 : List Nat := [1, 2, 3, 4, 5] -- List Nat（同样的类型）

-- 依赖类型的向量：长度编码在类型中
-- Vector α n 表示"长度为 n 的 α 类型向量"
-- Vector Nat 3 和 Vector Nat 5 是不同的类型！
```

这里 `n` 是一个**值**（自然数），但它出现在**类型** `Vector α n` 中。这就是"类型依赖于值"。

**依赖函数类型（Π 类型）**：函数的返回类型可以依赖于输入值。

```lean
-- 普通函数：返回类型固定
/-- double: 将自然数翻倍
    输入: Nat — 自然数 n
    输出: Nat — n × 2 -/
def double : Nat → Nat := fun n => n * 2

-- 依赖函数：返回类型依赖于输入值
-- 输入 n，返回一个长度为 n 的全零向量
-- zeros 3 的类型是 Vector Nat 3
-- zeros 5 的类型是 Vector Nat 5
-- 返回类型随输入值变化！
def zeros : (n : Nat) → Vector Nat n := fun n => Vector.replicate n 0
```

### 2.5.2 为什么 LEAN 需要依赖类型？

LEAN 作为定理证明器，需要在类型系统中表达数学命题。而数学命题天然就是依赖类型：

**1. 命题依赖于值**

```lean
-- 命题 "n 是偶数" 依赖于具体的 n
def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- Even 2 和 Even 3 是不同的命题（类型）
example : Even 2 := ⟨1, rfl⟩  -- 可以证明
-- example : Even 3 := ?      -- 无法证明
```

**2. 全称量词需要依赖函数类型**

```lean
-- "对所有自然数 n，n + 0 = n"
-- 这实际上是一个依赖函数类型：(n : Nat) → (n + 0 = n)
-- 返回类型 "n + 0 = n" 依赖于输入 n
theorem add_zero : ∀ (n : Nat), n + 0 = n := fun n => rfl
```

**3. 存在量词需要依赖对类型**

```lean
-- "存在自然数 n 使得 n > 5"
-- 这是一个依赖对：第二个分量的类型 "n > 5" 依赖于第一个分量 n 的值
example : ∃ n : Nat, n > 5 := ⟨6, by omega⟩
```

> **核心观点**：没有依赖类型，我们无法在类型系统中表达 $\forall x, P(x)$ 或 $\exists x, P(x)$ 这样的基本逻辑结构。依赖类型是将数学逻辑嵌入类型系统的关键。

### 2.5.3 类型层级 (The Type Hierarchy)

在常见的编程语言（如 Java）中，`1` 是 `int`，但 `int` 是什么？通常是关键字。

但在 LEAN 中，`Nat` (类型) 本身也是一个**项 (Term)**，它也有类型！

### 2.5.4 类型层级 (The Type Hierarchy)

```lean
#check 1        -- 1 : Nat
#check Nat      -- Nat : Type
#check Type     -- Type : Type 1
#check Type 1   -- Type 1 : Type 2
```

我们得到了一个无限的阶梯：
$$ \text{Term} : \text{Type}_0 : \text{Type}_1 : \text{Type}_2 : \dots $$

这被称为 **Sorts** 或 **Universes**。这样做是为了避免类似于"罗素悖论"的集合论问题。

### 2.5.5 Prop：命题的特权阶级

LEAN 有一个特殊的类型叫做 `Prop` (即 `Sort 0`)。它是所有逻辑命题的类型。

- `Nat`, `List Int` 属于 `Type` (数据的世界)。
- `1 + 1 = 2`, `x > 0` 属于 `Prop` (逻辑的世界)。

```lean
def p1 : Prop := 2 + 2 = 4
def p2 : Prop := 2 + 2 = 5

#check p1  -- p1 : Prop
```

**重要概念**: `p2` 虽然是假的，但它依然是一个合法的 `Prop`。正如 "Grammar is correct" 是一句合法的英语，尽管这句话本身的内容可能是假的。

---

## 2.6 隐式参数 (Implicit Arguments)

在数学中，我们说"对于任意集合 A，恒等函数 id 将 A 中的元素映射到自身"。我们不会每次调用 id 时都喊一遍"对于集合 Nat..."。

LEAN 使用花括号 `{}` 来表示这些可以让编译器自动推断的参数。

```lean
-- 显式参数版本
/-- id_explicit: 恒等函数（显式版本），原样返回输入值
    输入: α — 类型（需手动传入）; x — α 类型的值
    输出: x 本身 — α 类型 -/
def id_explicit (α : Type) (x : α) : α := x
#check id_explicit Nat 5  -- 必须手动传入 Nat

-- 隐式参数版本
/-- id_implicit: 恒等函数（隐式版本），原样返回输入值
    输入: {α} — 类型（LEAN 自动推断）; x — α 类型的值
    输出: x 本身 — α 类型 -/
def id_implicit {α : Type} (x : α) : α := x
#check id_implicit 5      -- LEAN 自动推断出 α 是 Nat
#check id_implicit "Hi"   -- LEAN 自动推断出 α 是 String
```

---

## 2.7 复合类型 (Product & Sum Types)

LEAN 提供了丰富的类型构造器。最基础的是笛卡尔积（Prod）和求和（Sum）。

### 笛卡尔积 (Prod)

对应数学中的 $A \times B$。在 LEAN 中写作 `A × B` (输入 `\times`)。

```lean
def point2D : Nat × Nat := (1, 2)

#check point2D       -- 输出: Nat × Nat
#eval point2D.1      -- 输出: 1 (获取第一个分量)
#eval point2D.2      -- 输出: 2 (获取第二个分量)
```

### 和类型 (Sum)

对应"或"的概念，或者是编程中的 `Union` / `Variant`。写作 `A ⊕ B` (输入 `\oplus`)。

```lean
-- Sum.inl 表示左边的值，Sum.inr 表示右边的值
def v1 : Nat ⊕ String := Sum.inl 10
def v2 : Nat ⊕ String := Sum.inr "Error"

#check v1  -- 输出: Nat ⊕ String
```

---

## 2.8 结构体 (Structures)

当我们需要将多个数据打包时（比如一个二维点，或者一个群的定义），使用 `structure`。

```lean
structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr -- 让 LEAN 知道如何打印这个结构体

def origin : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
def p1 : Point3D := { x := 1.5, y := 2.0, z := -1.0 }

-- 访问字段
#eval p1.x  -- 1.5
```

---

## 2.9 Toy Case: 打造一个迷你逻辑计算器

为了巩固本章知识，我们不使用 LEAN 内置的 `Bool`，而是通过定义函数来模拟简单的布尔逻辑运算。这将展示如何使用模式匹配 (Pattern Matching)。

```lean
-- 1. 定义逻辑非 (NOT)
-- 我们利用 pattern matching 来对输入的布尔值进行分类讨论
def my_not (b : Bool) : Bool :=
  match b with
  | true  => false
  | false => true

-- 测试
#eval my_not true   -- false
#eval my_not false  -- true

-- 2. 定义逻辑与 (AND)
-- 这里展示了多参数的模式匹配
def my_and (b1 : Bool) (b2 : Bool) : Bool :=
  match b1, b2 with
  | true, true => true
  | _, _       => false  -- 下划线 _ 表示"其他任意情况"

-- 测试
#eval my_and true true   -- true
#eval my_and true false  -- false

-- 3. 结合使用：实现 NAND (与非门)
def my_nand (b1 : Bool) (b2 : Bool) : Bool :=
  my_not (my_and b1 b2)

#eval my_nand true true  -- false
```

---

## 2.10 实战演练：向量运算

让我们综合运用上面的知识，定义一个简单的二维向量加法。

```lean
structure Vector2D where
  x : Int
  y : Int
deriving Repr

/-- vec_add: 二维向量加法，对应分量相加
    输入: v1, v2 — 二维整数向量
    输出: (v1.x + v2.x, v1.y + v2.y) — 二维整数向量 -/
def vec_add (v1 : Vector2D) (v2 : Vector2D) : Vector2D :=
  { x := v1.x + v2.x,
    y := v1.y + v2.y }

/-- scalar_mul: 标量乘法，将向量的每个分量乘以标量 c
    输入: c — 整数标量; v — 二维整数向量
    输出: (c * v.x, c * v.y) — 二维整数向量 -/
def scalar_mul (c : Int) (v : Vector2D) : Vector2D :=
  { x := c * v.x,
    y := c * v.y }

-- 测试
def v_a : Vector2D := { x := 1, y := 2 }
def v_b : Vector2D := { x := 3, y := 4 }

#eval vec_add v_a v_b        -- { x := 4, y := 6 }
#eval scalar_mul 10 v_a      -- { x := 10, y := 20 }
```

---

## 2.11 本章总结

1. **交互**: `#eval` 计算，`#check` 查类型。
2. **定义**: `def` 定义函数，`let` 定义局部变量。
3. **函数式特性**: 函数是一等公民，支持柯里化 (`Nat → Nat → Nat`) 和匿名函数 (`λ x => ...`)。
4. **递归**: 使用模式匹配 (`match ... with` 或 `|`) 处理递归逻辑。
5. **类型宇宙**: 理解 `Term : Type : Type 1` 的层级，以及特殊的 `Prop`。
6. **工程化**: 使用 `{}` 隐藏可推断参数，使用 `structure` 组织数据。

---

## 课后挑战

1. **求和函数**: 定义一个递归函数 `sum_upto (n : Nat) : Nat`，计算 $0 + 1 + \dots + n$。

2. **自定义列表**: 尝试定义一个简单的函数，计算 LEAN 内置 `List Nat` 中所有元素的和。（提示：List 的模式匹配有 `[]` 和 `head :: tail` 两种情况）。

3. **类型侦探**: 使用 `#check` 探索 `List (Nat → Nat)` 的类型。这是一个"函数的列表"！尝试构造一个包含两个函数的列表。

<details>
<summary>点击查看参考答案</summary>

```lean
-- 1. 求和函数
/-- sum_upto: 计算 0 + 1 + ... + n
    输入: Nat — 自然数 n
    输出: Nat — 前 n 个自然数之和 -/
def sum_upto : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sum_upto n

#eval sum_upto 10  -- 55

-- 2. 列表求和
/-- list_sum: 计算列表中所有自然数之和
    输入: List Nat — 自然数列表
    输出: Nat — 列表元素之和（空列表返回 0） -/
def list_sum : List Nat → Nat
  | [] => 0
  | head :: tail => head + list_sum tail

#eval list_sum [1, 2, 3, 4, 5]  -- 15

-- 3. 函数列表
def func_list : List (Nat → Nat) := [
  (λ x => x + 1),
  (λ x => x * 2)
]

#check func_list  -- List (Nat → Nat)
```

</details>

下一章，我们将学习命题逻辑中的 `And`（与）、`Or`（或）与 `Not`（非），并学习如何在 LEAN 中处理它们。
