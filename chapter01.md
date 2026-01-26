# 第一章：初识 LEAN 4 —— 从编程到证明

> **本章目标**：
> 1. 理解 LEAN 作为"编程语言"和"证明器"的统一性。
> 2. 掌握 LEAN 4 开发环境（VS Code + Elan + Lake）的搭建与配置。
> 3. **核心原理**：直观理解"命题即类型，证明即程序"（Propositions as Types）。
> 4. **实战**：通过 Toy Case 跑通第一个交互式证明。

---

## 1.1 什么是 LEAN？

LEAN（目前主流版本为 LEAN 4）不仅仅是一个**交互式定理证明器**（Interactive Theorem Prover），它同时也是一门功能强大的**函数式编程语言**。

对于计算机科学背景的研究者，LEAN 4 可以被定义为：
**一门基于依赖类型理论（Dependent Type Theory, DTT）的纯函数式编程语言，其类型系统足够强大，以至于可以表达任意数学命题。**

### 1.1.1 两个身份的统一

LEAN 并不是分裂的，它完美贯彻了 **Curry-Howard 同构**：

| 逻辑/数学概念 | 编程/类型论概念 |
| :--- | :--- |
| **命题** (Proposition, $P$) | **类型** (Type) |
| **证明** (Proof of $P$) | 该类型的**实例/项** (Term of Type $P$) |
| **蕴含** ($P \implies Q$) | **函数类型** ($P \to Q$) |
| **全称量词** ($\forall x \in A, P(x)$) | **依赖函数类型** ($\Pi x : A, P(x)$) |
| **验证证明** | **类型检查** (Type Checking) |

当你写下一个证明时，你实际上是在编写一段代码（构造一个项），而 LEAN 的编译器（Kernel）负责检查这段代码的类型是否匹配。如果类型匹配，证明即成立。

### 1.1.2 为什么选择 LEAN 4？

* **Mathlib4**：拥有目前增长最快的数学形式化库，涵盖代数、拓扑、分析等。
* **元编程（Metaprogramming）**：LEAN 4 是"自举"的（Self-hosted）。你可以用 LEAN 语言本身去写 LEAN 的扩展、Tactics（策略）甚至 DSL。
* **现代化的工具链**：提供了类似 Rust `cargo` 的包管理器 `lake`，以及基于 LSP（Language Server Protocol）的极致 IDE 体验。

---

## 1.2 环境搭建：工欲善其事

LEAN 4 的工具链非常现代，主要由三部分组成：
1. **Elan**: 类似于 Rust 的 `rustup` 或 Python 的 `pyenv`，用于管理 LEAN 的版本。
2. **Lake**: LEAN 的包管理器和构建工具，类似于 Rust 的 `cargo`。
3. **VS Code + Lean 4 Extension**: 交互式编辑环境。

### 1.2.1 安装步骤

#### Windows 用户
1. **Git**: 确保已安装 git。
2. **VS Code**: 安装 Visual Studio Code。
3. **Elan**: 在 PowerShell 中运行官方脚本：
    ```powershell
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -o elan-init.ps1
    Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
    .\elan-init.ps1
    ```
    *注意：安装过程中按回车选择默认选项（Default）即可。*

#### macOS / Linux 用户
在终端运行：
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```
然后安装 VS Code 及其 "lean4" 插件。

### 1.2.2 验证安装与插件配置

```bash
lean --version
# 输出示例: Lean (version 4.x.x, ...)
```

---

## 1.3 Hello World：创建你的第一个项目

不要直接创建单文件，养成使用 `lake` 管理项目的习惯。

```bash
# 1. 初始化项目
lake new hello_proof

# 2. 进入目录
cd hello_proof

# 3. 用 VS Code 打开当前文件夹（关键步骤！）
code .
```

### 项目结构解析

- `lakefile.lean`: 项目的配置文件（依赖、构建配置），类似于 `package.json` 或 `Cargo.toml`。
- `lean-toolchain`: 指定当前项目使用的 LEAN 具体版本（例如 `leanprover/lean4:v4.6.0`）。
- `HelloProof.lean` (或 `Main.lean`): 源代码入口。

> **关键提示**：打开 `.lean` 文件后，请紧盯 VS Code 右侧。你应该会看到 **Lean Infoview** 面板自动弹出。如果没有，点击右上角的 "∀" 图标手动打开。Infoview 是你的"示波器"，它实时显示当前的证明状态（Goal）和错误信息。

---

## 1.4 Toy Case 1：LEAN 作为编程语言

在开始证明之前，先感受一下 LEAN 作为一门强类型函数式语言的特性。这有助于你理解"项"（Term）的构造。

在 `HelloProof.lean` 中输入以下代码（点击"在线运行"可在浏览器中体验）：

```lean
-- 1. 定义简单函数
-- 语法: def 函数名 (参数 : 类型) : 返回类型 := 函数体
def addFive (n : Nat) : Nat := n + 5

-- #eval 指令：编译期计算（类似于 Python 的 print/repl）
#eval addFive 10    -- Infoview 输出: 15

-- 2. 模式匹配与递归
-- LEAN 要求所有函数必须是 Total 的（对所有输入都有定义且必然终止）
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5   -- Infoview 输出: 120

-- 3. 类型检查
-- #check 指令：查看一个表达式的类型
#check addFive      -- 输出: Nat → Nat
#check factorial    -- 输出: Nat → Nat
```

**思考**：这里的 `addFive` 是一个函数，类型是 `Nat → Nat`。在下一节你会发现，证明一个蕴含命题 $P \implies Q$，本质上就是写一个类型为 $P \to Q$ 的函数。

---

## 1.5 Toy Case 2：LEAN 作为证明器

现在我们进入正题。LEAN 提供了两种写证明的方式：

1. **Term Mode（项模式）**：直接写出构造证明的 Lambda 表达式（像写程序一样）。
2. **Tactic Mode（策略模式）**：使用指令脚本指导 LEAN 逐步构建证明（像数学推导一样）。

我们将通过证明一个简单的逻辑命题来对比这两种方式：

**命题**：如果 $P$ 蕴含 $Q$，且 $P$ 成立，那么 $Q$ 成立。（即 Modus Ponens）

### 1.5.1 Term Mode（函数式写法）

```lean
-- 声明 P 和 Q 是命题 (Prop)
variable (P Q : Prop)

-- 定理声明
-- h_imp : P → Q  (假设 P 蕴含 Q)
-- h_p   : P      (假设 P 成立)
theorem modus_ponens_term : (P → Q) → P → Q :=
  -- 这是一个匿名函数 (lambda)，接收两个参数 h_imp 和 h_p
  fun h_imp => fun h_p =>
    -- 函数体：将 h_imp 应用于 h_p
    h_imp h_p
```

**解析**：
- `(P → Q) → P → Q` 是这个定理的类型（Type）。
- `fun h_imp => fun h_p => h_imp h_p` 是这个类型的项（Term）。
- 这完全等价于编程中的函数调用！

### 1.5.2 Tactic Mode（交互式写法）

这是你在写复杂数学证明时主要使用的方式。我们使用 `by` 关键字进入 Tactic 模式。

```lean
variable (P Q : Prop)

theorem modus_ponens_tactic : (P → Q) → P → Q := by
  -- 此时观察 Infoview 的 "Tactic State"
  -- 目标 (Goal): ⊢ (P → Q) → P → Q

  intro h_imp
  -- intro 类似于编程中的 "function definition"，将前提引入上下文
  -- 此时 Context 增加了 h_imp : P → Q
  -- 目标变为: ⊢ P → Q

  intro h_p
  -- 再次引入前提
  -- 此时 Context 增加了 h_p : P
  -- 目标变为: ⊢ Q

  apply h_imp
  -- apply h_imp 尝试通过应用函数 h_imp 来解决目标 Q
  -- 由于 h_imp 需要一个 P 类型的输入，目标从 Q 变成了 P
  -- 目标变为: ⊢ P

  exact h_p
  -- exact 告诉 LEAN：我手里正好有一个类型为 P 的项 h_p，这就是答案
  -- 目标解决！显示 "No goals"
```

> **Usage Tip**: 在 Tactic 模式下，将光标移动到每一行代码的末尾，Infoview 会显示执行该行代码之后的状态。**请务必亲自尝试移动光标，观察上下文（Context）和目标（Goal）的变化。**这是学习 LEAN 的唯一捷径。

---

## 1.6 深入理解：Prop 与 Type

在 LEAN 中，你经常会看到 `Prop` 和 `Type`。

- `Type` (或 `Type 0`): 数据类型的类型。例如 `Nat`, `List Int`, `String` 的类型都是 `Type`。
- `Prop`: 逻辑命题的类型。例如 `1 + 1 = 2`, `P → Q` 的类型都是 `Prop`。

```lean
variable (α : Type)  -- α 是某种数据类型（比如整数集合）
variable (β : Prop)  -- β 是某种逻辑命题（比如"它是偶数"）

#check 5             -- Nat
#check Nat           -- Type
#check 1 = 1         -- Prop
#check And           -- Prop → Prop → Prop (逻辑"与"是一个函数)
```

**重要区别**：LEAN 具有 **Proof Irrelevance（证明无关性）**。

- 对于数据（`Type`），我们关心它是哪个值（`5` 和 `6` 是不同的）。
- 对于命题（`Prop`），我们只关心它**是否有**证明。如果有两个不同的证明 `h1 : P` 和 `h2 : P`，在逻辑上我们将它们视为等价的。

---

## 1.7 第一个定理证明：1 + 1 = 2

现在，我们来证明一个非常简单的数学命题：$1 + 1 = 2$。

```lean
-- Toy Case 1: 显式构造证明项
-- 这里的 rfl 是 "reflexivity"（自反性）的缩写。
-- 因为 1 + 1 定义上计算结果就是 2，所以它们是"定义相等"的。
example : 1 + 1 = 2 := rfl

-- Toy Case 2: 使用 Tactic 模式
example : 1 + 1 = 2 := by
  -- 此时查看 Infoview，你会看到目标是 ⊢ 1 + 1 = 2
  rfl
  -- 证明完成后，Infoview 会显示 "No goals"
```

### 命题即类型（Propositions as Types）

这是本章最核心的**原理**。请仔细观察下面的代码：

```lean
-- 定义一个自然数 n，它的类型是 Nat
def n : Nat := 5

-- 定义一个命题 p，它的类型是 Prop
def p : Prop := 1 + 1 = 2

-- 定义一个证明 h，它的类型是 p (即 1 + 1 = 2)
def h : p := rfl
```

**解析**：
- `n : Nat` 读作 "n 是一个自然数"。
- `h : p` 读作 "h 是命题 p 的一个证明"。
- 在 LEAN 中，检查一个数学证明是否正确，本质上和编译器检查 `n` 是否真的是 `Nat` 类型是一样的（Type Checking）。

---

## 1.8 本章实战练习

请在你的 `HelloProof.lean` 文件中尝试完成以下证明（使用 Tactic 模式）。

**练习题：蕴含的传递性**

求证：如果 $P \implies Q$ 且 $Q \implies R$，则 $P \implies R$。

```lean
variable (P Q R : Prop)

theorem imp_trans (h1 : P → Q) (h2 : Q → R) : P → R := by
  -- 提示：
  -- 1. 先引入前提 (intro)
  -- 2. 观察你需要构造什么
  -- 3. 逐步 apply 你的假设
  sorry -- 将 sorry 替换为你的代码
```

<details>
<summary>点击查看参考答案</summary>

```lean
theorem imp_trans (h1 : P → Q) (h2 : Q → R) : P → R := by
  intro p_inst      -- 引入 P 的实例
  apply h2          -- 目标变成 Q (因为 h2 需要 Q 才能推出 R)
  apply h1          -- 目标变成 P (因为 h1 需要 P 才能推出 Q)
  exact p_inst      -- 提供了 P 的实例，证明结束
```

</details>

---

## 1.9 本章小结

1. **环境**：使用 `lake new` 创建项目，依赖 VS Code + Infoview 进行交互。
2. **原理**：**命题 = 类型**，**证明 = 程序**。
3. **模式**：
   - `def / theorem ... := term` (Term 模式，适合简单定义)
   - `theorem ... := by ...` (Tactic 模式，适合复杂推理)
4. **常用 Tactic**：
   - `intro`: 引入假设（相当于函数的参数）。
   - `exact`: 精确匹配目标（相当于函数返回值）。
   - `apply`: 应用引理或函数（相当于函数调用）。
   - `rfl`: 处理定义上的相等（Definitional Equality）。

下一章，我们将深入探讨 LEAN 的函数式编程特性与依赖类型理论基础。
