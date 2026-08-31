/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Init
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# The rose-tree data type

The single universal data type into which everything put on a Turing machine tape is encoded,
together with its size measure, its balanced-parenthesis bit encoding, and a handful of
list-sum helpers that the size lemmas downstream are built from.

Reproduced from the `roseTreeMachine` branch of the `crei/cslib` fork; see
[issue #611](https://github.com/leanprover/cslib/issues/611). Part of the draft complexity
development rooted at `Complexity.lean`.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-! ## 1. The rose-tree data type

Reproduced from the `roseTreeMachine` branch of `crei/cslib`; see the TODO above.
-/

/-- The rose-tree data type: the single universal data type into which we encode everything that
is put on a tape. It is expressive enough to mirror most Lean data types in a natural way, and it
supports a `fold` operation, which is the subject of this file. -/
inductive Data where
  /-- A node with the given children. -/
  | l : List Data → Data
  deriving Repr

/-- The children of a node. -/
def Data.asList : Data → List Data
  | Data.l xs => xs

/-- The empty rose tree. -/
abbrev Data.empty : Data := Data.l []

/-- The size of a rose tree, which is by construction exactly the length of its encoding
`Data.toBits` as a bit string: one bit for the opening and one for the closing parenthesis of
every node. This is *the* notion of input size used throughout this file. -/
def Data.size : Data → ℕ
  | Data.l xs => 2 + (xs.map Data.size).sum

/-- The nesting depth of a rose tree. Bounding this by a constant of the type is what lets a
machine skip over a subtree in constant work-tape space; see `DataEncode`. -/
def Data.depth : Data → ℕ
  | Data.l xs => 1 + (xs.map Data.depth).foldr max 0

/-- A uniform bound on the elements bounds a `foldr max`. -/
lemma foldr_max_le {α : Type} (xs : List α) (f : α → ℕ) (d : ℕ)
    (h : ∀ x ∈ xs, f x ≤ d) : (xs.map f).foldr max 0 ≤ d := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := h y (by simp)
    have hrest := ih fun x hx => h x (by simp [hx])
    simp only [List.map_cons, List.foldr_cons]
    omega

/-- Every rose tree costs at least the two bits of its root node. -/
lemma Data.two_le_size (d : Data) : 2 ≤ d.size := by
  cases d with
  | l xs => simp [Data.size]

mutual

/-- The canonical balanced-parenthesis encoding of a rose tree as a bit string: `false` opens a
node, `true` closes it. This is what is actually written on a Turing machine tape. -/
def Data.toBits : Data → List Bool
  | Data.l xs => false :: (Data.listToBits xs ++ [true])

/-- Auxiliary for `Data.toBits`: the concatenated encodings of a list of children. -/
def Data.listToBits : List Data → List Bool
  | [] => []
  | x :: xs => Data.toBits x ++ Data.listToBits xs

end

mutual

/-- `Data.size` is exactly the length of the bit encoding. This is the only reason `Data.size`
is defined with the constant `2`, and it is what lets us state all bounds in terms of `size`
while the machines actually operate on `Data.toBits`. -/
lemma Data.length_toBits (d : Data) : d.toBits.length = d.size := by
  cases d with
  | l xs =>
    simp [Data.toBits, Data.size, Data.length_listToBits xs]
    omega

/-- Auxiliary for `Data.length_toBits`. -/
lemma Data.length_listToBits (xs : List Data) :
    (Data.listToBits xs).length = (xs.map Data.size).sum := by
  cases xs with
  | nil => simp [Data.listToBits]
  | cons x xs =>
    simp [Data.listToBits, Data.length_toBits x, Data.length_listToBits xs]

end

/-! ### List helpers

Two arithmetic helpers about sums of mapped lists, used only to compute encoded sizes.
-/

/-- A uniform bound on the elements bounds the sum of a mapped list. -/
lemma sum_map_le {α : Type} (xs : List α) (f : α → ℕ) (b : ℕ)
    (h : ∀ x ∈ xs, f x ≤ b) : (xs.map f).sum ≤ b * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := h y (by simp)
    have hys := ih fun x hx => h x (by simp [hx])
    have hb : b * (ys.length + 1) = b * ys.length + b := by ring
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- A uniform lower bound on the elements bounds the sum of a mapped list from below. -/
lemma le_sum_map {α : Type} (xs : List α) (f : α → ℕ) (b : ℕ)
    (h : ∀ x ∈ xs, b ≤ f x) : b * xs.length ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := h y (by simp)
    have hys := ih fun x hx => h x (by simp [hx])
    have hb : b * (ys.length + 1) = b * ys.length + b := by ring
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- If the mapped function is constant, the sum is that constant times the length. -/
lemma sum_map_const {α : Type} (xs : List α) (f : α → ℕ) (b : ℕ)
    (h : ∀ x, f x = b) : (xs.map f).sum = b * xs.length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, h y]
    ring

/-- A pointwise bound `f x ≤ c * g x` lifts to the sums of the mapped lists. -/
lemma sum_map_le_of_le {α : Type} (l : List α) (f g : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c * g x) : (l.map f).sum ≤ c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    have hy := h y (by simp)
    have hrest := ih fun x hx => h x (by simp [hx])
    have hmul : c * (g y + (ys.map g).sum) = c * g y + c * (ys.map g).sum := by ring
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Summing over a prefix is bounded by summing over the whole list. -/
lemma sum_map_take_le {α : Type} (l : List α) (f : α → ℕ) (j : ℕ) :
    ((l.take j).map f).sum ≤ (l.map f).sum := by
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.map_append, List.sum_append]
  omega

end RoseTreeMachine

end Turing
