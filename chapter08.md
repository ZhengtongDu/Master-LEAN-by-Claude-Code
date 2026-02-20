# 第八章：结构与类型类 (Structures and Type Classes)

> **本章目标**：
> 1. **结构体定义**：掌握 `structure` 关键字定义复合数据类型，理解构造、投影与函数式更新。
> 2. **类型类机制**：理解 `class` 与 `instance` 的工作原理，掌握特设多态（Ad-hoc Polymorphism）。
> 3. **实例搜索**：理解 Lean 编译器如何自动搜索和注入类型类实例。
> 4. **常用类型类**：掌握 `Inhabited`、`BEq`、`ToString`、`Repr` 等标准库类型类。
> 5. **代数结构预览**：了解 Mathlib 如何用类型类层次组织数学结构。

---

## 8.1 结构体（Structure）详解

> **结构体 (Structure)**：结构体是一种复合数据类型，通过 `structure` 关键字定义，将多个命名字段打包为一个整体。Lean 自动为其生成构造函数和投影函数，并支持函数式更新与继承。

### 8.1.1 定义结构体

在 Lean 中，`structure` 关键字用于定义一个包含多个命名字段（Field）的复合类型。这类似于 C 语言的 `struct` 或 Python 的 `class`（仅含数据部分）。

#### Toy Case: 二维点 (`Point`)
我们定义一个表示二维平面坐标点的结构体。

```lean
/-- 定义一个名为 Point 的结构体。
    它包含两个字段：x 和 y，类型均为 Float。-/
structure Point where
  x : Float
  y : Float
  deriving Repr -- 自动派生 Repr 实例，以便 #eval 能打印它

/-- 动机讲解：
    如果没有 structure，我们可能需要用 (Float × Float) 的元组来表示点。
    但是元组的元素没有名字（只有 .1, .2），代码可读性极差。
    structure 赋予了数据语义化的名称。-/

```

### 8.1.2 构造与投影

定义结构体后，Lean 会自动生成以下内容：

1. **构造函数 (Constructor)**：默认为 `Point.mk`。
2. **投影函数 (Projections)**：即字段访问器 `Point.x` 和 `Point.y`。

```lean
/-- p1: 使用标准构造语法创建点
    输入: 无
    输出: Point -/
-- 使用花括号 {} 和 := 赋值。这种方式最清晰，字段顺序不限。
def p1 : Point := { x := 1.0, y := 2.0 }

/-- p2: 使用匿名构造器创建点
    输入: 无
    输出: Point -/
-- 使用 ⟨ ⟩ (注意不是小于号，输入方式为 \langle \rangle)。
-- 这种方式依赖上下文推断类型，且必须严格遵守字段定义顺序。
def p2 : Point := ⟨3.0, 4.0⟩

/-- p3: 使用底层 mk 构造函数创建点
    输入: 无
    输出: Point -/
-- 直接调用自动生成的 mk 函数。不推荐在日常代码中使用。
def p3 : Point := Point.mk 5.0 6.0

-- 字段访问 (投影)
#eval p1.x      -- 输出: 1.000000
#eval Point.y p2 -- 函数式写法：Point.y 实际上是一个函数 Point → Float

```

### 8.1.3 函数式更新 (Functional Update)

Lean 是**纯函数式语言**，数据是**不可变（Immutable）**的。这意味着你不能像在 C++ 或 Python 中那样 `p1.x = 10`。
如果你想“修改”一个结构体，实际上是创建一个**新的**结构体，复制旧结构体的大部分字段，仅改变你指定的字段。Lean 提供了 `with` 语法糖来简化这一过程。

```lean
/-- moveRight: 将点的 x 坐标向右移动
    输入: p — 原始点, shift — 移动距离
    输出: Point — 新的点 -/
def moveRight (p : Point) (shift : Float) : Point :=
  { p with x := p.x + shift }

/-- pOld: 测试用的原始点 -/
def pOld := { x := 1.0, y := 1.0 } : Point
/-- pNew: 将 pOld 向右移动 10 个单位后的新点 -/
def pNew := moveRight pOld 10.0

#eval pNew -- { x := 11.0, y := 1.0 }
#eval pOld -- { x := 1.0,  y := 1.0 } (原数据保持不变)

```

### 8.1.4 继承 (Extends)

结构体支持继承。子结构体将拥有父结构体的所有字段，并可以添加新字段。

```lean
/-- Point3D 继承自 Point，并增加 z 轴 -/
structure Point3D extends Point where
  z : Float
  deriving Repr

/-- p3d: 三维点示例 -/
def p3d : Point3D := { x := 1.0, y := 2.0, z := 3.0 }

-- 访问父类字段
#eval p3d.x  -- 直接访问，Lean 会自动处理投影
#eval p3d.toPoint -- 也可以显式转换为父类型

```

---

## 8.2 类型类（Class）机制

> **类型类 (Type Class)**：类型类是 Lean 实现特设多态（Ad-hoc Polymorphism）的核心机制。通过 `class` 定义行为协议，再通过 `instance` 为具体类型提供实现，编译器会自动搜索并注入匹配的实例。

### 8.2.1 什么是类型类？

**问题**：假设我们要写一个函数 `sum`，既能计算两个自然数的和，也能计算两个 `Point` 的和（向量加法）。
在 Python 中，这叫“鸭子类型”；在 Java 中，这叫“接口实现”；在 Lean 中，这叫**类型类（Type Class）**。

- **Structure** 定义了数据长什么样（Shape）。
- **Class** 定义了数据能做什么（Behavior）。
`class` 关键字在 Lean 中的底层实现其实就是一个 `structure`，唯一的区别在于：**Lean 的类型推断系统（Elaborator）会自动搜索 class 的实例**。

### 8.2.2 定义一个类型类

#### Toy Case: 自定义 `Addable`
我们定义一个简单的类型类，要求实现该类的类型必须支持“加法”操作。

```lean
/-- 定义一个类型类 Addable。
    α 是一个类型参数（比如 Nat, Point 等）。
    这个类要求提供一个函数 add，接收两个 α，返回一个 α。-/
class Addable (α : Type) where
  add : α → α → α

/-- myAdd: 通用加法函数
    输入: 两个相同类型 α 的值（要求 α 实现 Addable）
    输出: α -/
-- [Addable α] 是核心：它告诉 Lean "在这个上下文中，必须有一个能为 α 提供 Addable 行为的实例"
def myAdd {α : Type} [Addable α] (x y : α) : α :=
  Addable.add x y

```

---

## 8.3 实例（Instance）的定义与推断

> **实例搜索 (Instance Synthesis)**：当函数签名中包含类型类约束（如 `[Addable α]`）时，Lean 编译器会自动在当前环境中搜索匹配的 `instance` 定义并注入，无需手动传递。这是类型类多态的自动化核心。

定义了 `class`（协议）后，我们需要使用 `instance`（实例）将具体的数据类型与协议连接起来。

### 8.3.1 为 Point 实现 Addable

```lean
/-- Addable Point 实例: 定义 Point 的逐分量加法 -/
instance : Addable Point where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

/-- Addable Nat 实例: 将自然数加法注册为 Addable -/
instance : Addable Nat where
  add n m := n + m

-- 测试多态性
def pt1 : Point := ⟨1.0, 1.0⟩
def pt2 : Point := ⟨2.0, 3.0⟩

#eval myAdd pt1 pt2  -- 输出: { x := 3.000000, y := 4.000000 }
#eval myAdd 5 10     -- 输出: 15

```

### 8.3.2 实例搜索的工作原理 (Instance Synthesis)

当你调用 `myAdd pt1 pt2` 时，Lean 编译器会进行如下推理：

1. **类型推断**：编译器发现 `pt1` 和 `pt2` 的类型是 `Point`，所以 `myAdd` 中的 `α` 是 `Point`。
2. **约束检查**：`myAdd` 的签名要求存在一个 `[Addable Point]` 类型的参数。这是一个**隐式参数**。
3. **实例搜索**：编译器查找当前环境中所有标记为 `instance` 的定义，寻找类型匹配 `Addable Point` 的那个。
4. **注入**：找到我们在 8.3.1 中定义的实例，将其自动填入函数调用中。
如果 Lean 找不到对应的实例，就会报错：`failed to synthesize instance 'Addable String'`（如果你试图对字符串调用 `myAdd` 且未定义实例）。

---

## 8.4 常用类型类：Inhabited、BEq、ToString

> **Inhabited / BEq / ToString**：Lean 标准库提供的常用类型类。`Inhabited` 为类型提供默认值，`BEq` 定义布尔相等性运算符 `==`，`ToString` 支持字符串插值显示。自定义类型应尽量实现这些类型类，也可通过 `deriving` 自动派生。

Lean 标准库提供了许多极其重要的类型类，所有的自定义类型最好都考虑实现它们。

### 8.4.1 Inhabited (默认值)

Lean 讨厌"未定义行为"。许多函数（如从数组中取值 `Array.get!`）要求：万一索引越界了，你得返回一个“默认值”。这个默认值由 `Inhabited` 类提供。

```lean
/-- Inhabited Point 实例: 以原点 (0, 0) 作为默认值 -/
instance : Inhabited Point where
  default := { x := 0.0, y := 0.0 } -- 定义原点为默认值

#eval (default : Point) -- 现在我们可以直接获取一个默认的点

```

### 8.4.2 BEq (布尔相等性)

在 Lean 中，命题相等（$a = b$）和布尔相等（$a == b$）是不同的。`BEq` 类型类用于定义 `==` 运算符。

```lean
/-- BEq Point 实例: 逐字段比较两个点是否相等 -/
instance : BEq Point where
  beq a b := (a.x == b.x) && (a.y == b.y)

#eval {x:=1.0, y:=2.0} == {x:=1.0, y:=2.0} -- true

```

### 8.4.3 ToString 与 Repr

- `ToString`：用于 `s!"Value: {x}"` 这种用户友好的字符串插值。
- `Repr`：用于 `#eval` 命令，主要供开发者调试使用。

### 8.4.4 Deriving (自动派生)

手写上面这些实例很枯燥。Lean 允许我们通过 `deriving` 关键字自动生成标准实例。

```lean
/-- User: 用户信息结构体，演示 deriving 自动派生 -/
structure User where
  id : Nat
  name : String
  email : String
  deriving Repr, BEq, Inhabited, CanEqual -- 甚至可以派生 DecidableEq

-- 一行代码，User 现在可以被打印、被比较、拥有默认值。

```

---

## 8.5 代数结构的类型类层次 (Mathlib 预览)

这是 Lean 与其他编程语言最大的不同点。在 Mathlib 中，**数学结构也是通过类型类定义的**。

### 8.5.1 结构层次

数学结构通常是层层递进的：

1. **Semigroup (半群)**: 有结合律的运算。
2. **Monoid (幺半群)**: 半群 + 单位元 (Identity)。
3. **Group (群)**: 幺半群 + 逆元 (Inverse)。

### Toy Case: 定义幺半群 (Monoid)

在 Mathlib 中，一个代数结构不仅包含**运算**（Data），还包含**法则**（Prop/Axioms）。

```lean
/-- MyMonoid: 简化的幺半群类型类
    要求: 二元运算 op、单位元 id、结合律与单位律 -/
class MyMonoid (α : Type) where
  op : α → α → α        -- 二元运算
  id : α                -- 单位元
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c) -- 结合律
  op_id    : ∀ a : α, op a id = a                       -- 右单位律
  id_op    : ∀ a : α, op id a = a                       -- 左单位律

-- 动机：
-- 任何实现了 MyMonoid 的类型，不仅能进行运算，还被“保证”满足数学定律。
-- 这使得我们可以基于 MyMonoid α 写出通用的数学定理证明，而不用关心 α 具体是什么。

```

### 8.5.2 实例化数学结构

让我们证明自然数 `Nat` 在加法下构成一个 `MyMonoid`。

```lean
/-- MyMonoid Nat 实例: 证明自然数在加法下构成幺半群 -/
instance : MyMonoid Nat where
  op := Nat.add
  id := 0
  -- 下面是证明部分
  op_assoc := Nat.add_assoc  -- Lean 标准库已经证明了自然数加法结合律
  op_id    := Nat.add_zero   -- 加 0 等于自身
  id_op    := Nat.zero_add   -- 0 加 任意数等于自身

```
这展示了 Lean 类型类的强大之处：**它将程序的实现（implementation）和数学的规范（specification）统一在了一起。**

---

## 本章小结

1. **Structure 用于数据建模**：它提供了命名、投影和继承机制，使用 `with` 语法进行非破坏性更新。
2. **Class 用于行为抽象**：它类似于接口，允许我们定义通用的操作（如打印、相加）。
3. **Instance 是连接两者的胶水**：Lean 的编译器会自动搜索实例，这是实现重载和自动化数学推理的关键。
4. **Mathlib 的基石**：Mathlib 使用复杂的类型类层级（如 `Group`, `Ring`, `Field`, `TopologicalSpace`）来组织整个数学大厦。

---

## 练习题

1. **矩形结构体**：定义一个 `Rect` 结构体，包含 `width` 和 `height` (Float)。实现一个方法 `area` 计算面积。
2. **复数运算**：
  - 定义 `structure Complex where re : Float; im : Float`。
  - 实现 `ToString` 实例，使其输出形式为 `a + bi`。
  - 实现 `Add` 实例（标准库中的加法类），使得可以用 `+` 号相加两个复数。
3. **偏序关系**：查看 Lean 标准库中 `LE` (Less or Equal) 类型类的定义，尝试为你定义的 `Rect` 实现面积大小的比较（即 `rect1 <= rect2` 当且仅当 `rect1` 的面积小于等于 `rect2`）。
