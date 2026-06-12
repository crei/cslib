/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Init
public import Mathlib.Data.Part

/-!
# Main internal data type for the rose tree machine (RTM)

This file contains the main internal data structure for the RTM, `Data`, a rose tree.

## Main definitions and notations

- `Data` - the main data structure
- `Data.size` - the size of a `Data` object when encoded using parentheses, complexity results
  use this size as the main measure.
- `Data.recL` - the main recursion principle for `Data`
- `Data.inductionL` - the main induction principle for `Data`

-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- Rose-tree data structure, it allows us to encode most of Lean's data structures in a
"natural" manner -/
inductive Data where
  | l : List Data → Data
deriving Repr

mutual
  def Data.decEq : ∀ (a b : Data), Decidable (a = b)
    | .l xs, .l ys =>
      match Data.listDecEq xs ys with
      | isTrue h => isTrue (congrArg Data.l h)
      | isFalse h => isFalse fun heq => h (Data.l.inj heq)
  def Data.listDecEq : ∀ (xs ys : List Data), Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by simp)
    | _ :: _, [] => isFalse (by simp)
    | x :: xs, y :: ys =>
      match Data.decEq x y, Data.listDecEq xs ys with
      | isTrue hxy, isTrue hxys => isTrue (congrArg₂ List.cons hxy hxys)
      | isFalse hxy, _ => isFalse fun h => hxy (List.cons.inj h).1
      | _, isFalse hxys => isFalse fun h => hxys (List.cons.inj h).2
end

instance : DecidableEq Data := Data.decEq
instance : BEq Data := inferInstance
instance : LawfulBEq Data := inferInstance

abbrev Data.empty := Data.l []


@[scoped grind =]
def Data.asList
  | Data.l xs => xs

@[simp]
lemma Data.asList_empty : Data.empty.asList = [] := by rfl

@[simp, scoped grind =]
lemma Data.asList_l (d : Data) : Data.l d.asList = d := by simp [Data.asList]; grind

@[simp, scoped grind =]
lemma Data.l_asList (xs : List Data) : (Data.l xs).asList = xs := by simp [Data.asList]

/-- The encoding length of `d`, relevant for complexity.
This is the encoded size assuming an encoding into parenthesized expressions. -/
def Data.size : Data → ℕ
  | Data.l xs => 2 + (xs.map Data.size |>.sum)

@[simp]
lemma Data.size_le {d : Data} : 0 < d.size := by
  obtain ⟨xs⟩ := d
  grind [Data.size]

@[simp, scoped grind =]
lemma Data.size_empty : Data.empty.size = 2 := by simp [Data.empty, Data.size]

@[simp, scoped grind =]
lemma Data.cons_size {h : Data} {t : List Data} :
    (Data.l (h :: t)).size = h.size + (Data.l t).size := by
  simp [Data.size]
  grind

/-- Recursion principle for `Data`. -/
@[elab_as_elim]
def Data.recL {motive : Data → Sort*}
    (nil : motive (Data.l []))
    (cons : ∀ (x : Data) (xs : List Data),
      motive x → motive (Data.l xs) → motive (Data.l (x :: xs))) :
    ∀ d, motive d
  | .l [] => nil
  | .l (x :: xs) =>
      cons x xs (Data.recL nil cons x) (Data.recL nil cons (.l xs))

/-- Induction principle for `Data`, the `Prop`-valued companion to `Data.recL`. -/
@[elab_as_elim]
theorem Data.inductionL {motive : Data → Prop}
    (nil : motive (Data.l []))
    (cons : ∀ (x : Data) (xs : List Data),
      motive x → motive (Data.l xs) → motive (Data.l (x :: xs)))
    (d : Data) : motive d :=
  Data.recL nil cons d

abbrev TapeIndex := ℕ

end RoseTreeMachine

end Turing
