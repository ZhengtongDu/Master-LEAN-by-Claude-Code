# LEAN 4 交互式代码测试

本页面用于测试 LEAN 4 交互式代码功能。每个代码块上方都有工具栏，可以点击"在线运行"按钮在 [live.lean-lang.org](https://live.lean-lang.org) 中运行代码。

## 基础示例

### Hello World

最简单的 LEAN 4 程序：

```lean
#eval "Hello, LEAN 4!"
```

### 简单计算

LEAN 可以作为计算器使用：

```lean
#eval 1 + 1
#eval 2 * 3 + 4
#eval 10 / 3
#eval 10 % 3
```

## 类型与函数

### 定义函数

```lean
def double (x : Nat) : Nat := x * 2

#eval double 5
#eval double 21
```

### 多参数函数

```lean
def add (x y : Nat) : Nat := x + y

def multiply (x : Nat) (y : Nat) : Nat := x * y

#eval add 3 4
#eval multiply 6 7
```

## 命题与证明

### 简单证明

```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.add_succ, ih]
```

### 逻辑命题

```lean
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  constructor
  · exact h.right
  · exact h.left

theorem or_comm (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq
```

## 数据结构

### 列表操作

```lean
def myList : List Nat := [1, 2, 3, 4, 5]

#eval myList.length
#eval myList.reverse
#eval myList.map (· * 2)
#eval myList.filter (· > 2)
```

### 自定义类型

```lean
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.size : Tree α → Nat
  | .leaf _ => 1
  | .node l r => l.size + r.size

def myTree : Tree Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#eval myTree.size
```

## 策略证明示例

### 使用多种策略

```lean
example (a b c : Nat) : a + b + c = c + b + a := by
  omega

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  exact ⟨hp, hq, hr⟩

example (n : Nat) : n + n = 2 * n := by
  ring
```

## 注意事项

1. **代码长度限制**：由于 URL 长度限制，非常长的代码可能无法正常传递
2. **依赖库**：playground 环境已预装 Mathlib，可以直接使用
3. **网络要求**：需要能够访问 live.lean-lang.org

## 下一步

- 返回 [目录](index.md) 继续学习
- 查看 [第一章：走进 LEAN 的世界](chapter01.md)
