/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Ite

namespace CslibTests

open Cslib Turing MultiTapeTM

/-- The Boolean `and` function is computable in constant time and zero space. -/
example : ∀ encIn encOut, ∃ c, ComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry Bool.and)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply computableInTimeAndSpace_of_finite

def fullAdder (a b carry : Bool) : Bool × Bool :=
  let sum := (a != b) != carry
  let newCarry := (a && b) || (carry && (a != b))
  (sum, newCarry)

/-- The binary full adder is computable in constant time and zero space. -/
example : ∀ encIn encOut, ∃ c, ComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry fullAdder)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply computableInTimeAndSpace_of_finite

/-- Equality comparison to a constant is computable in constant time and zero space,
also for infinite domains. -/
example {α : Type*} [DecidableEq α] : ∀ encIn encOut out, ∃ c, ComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (fun a : α => a == out)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut out
  refine computableInTimeAndSpace_of_exists_finite_ne ⟨false, ?_⟩
  exact Set.Finite.subset (Set.finite_singleton out) (by intro a ha; simp_all)

/-! ## Case analysis

Lean's `ite` is `Bool.rec` once the `Decidable` instance is erased, and a `match` on a finite
inductive type is `Bool.rec` nested once per constructor. So the single primitive
`computableInTimeAndSpace_cond` covers all of them, and the derived
`computableInTimeAndSpace_match` needs nothing of the scrutinee's type beyond being finite. -/

/-- A conditional on a decidable predicate is computable as soon as the predicate is decided by a
machine and both branches are computable. Only the branch that is taken runs, hence the `max`. -/
example {α β : Type} {encIn : α ↪ List Bool} {encBool : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {p : α → Prop} [DecidablePred p] {f g : α → β} {tc sc tf sf tg sg : α → ℕ}
    (hp : ComputableInTimeAndSpace (fun a => decide (p a)) encIn encBool tc sc)
    (hf : ComputableInTimeAndSpace f encIn encOut tf sf)
    (hg : ComputableInTimeAndSpace g encIn encOut tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun a => if p a then f a else g a) encIn encOut
      (fun a => c * (tc a + max (tf a) (tg a) + 1))
      (fun a => c * (sc a + max (sf a) (sg a) + 1)) :=
  computableInTimeAndSpace_ite hp hf hg

/-- A three-constructor enumeration, of the kind a `match` in Lean compiles to nested
`Bool.rec`s. -/
inductive Colour
  | red
  | green
  | blue
deriving DecidableEq

instance : Fintype Colour where
  elems := {.red, .green, .blue}
  complete := by intro c; cases c <;> simp

/-- A `match` on a finite inductive type is computable as soon as the scrutinee and every branch
are. Only the branch that is taken runs, so the branches contribute their maximum rather than their
sum, and nothing about `Colour` is needed beyond `Fintype`. Testing which constructor the scrutinee
is costs no space beyond the scrutinee's own, since a finite type has only finitely many encodings
and so the encoded scrutinee is of constant length. -/
example {α β : Type} {encIn : α ↪ List Bool} {encC : Colour ↪ List Bool}
    {encBool : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {sel : α → Colour} {red green blue : α → β} {tsel ssel t s : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn encC tsel ssel)
    (hred : ComputableInTimeAndSpace red encIn encOut t s)
    (hgreen : ComputableInTimeAndSpace green encIn encOut t s)
    (hblue : ComputableInTimeAndSpace blue encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace
      (fun a => match sel a with
        | .red => red a
        | .green => green a
        | .blue => blue a)
      encIn encOut
      (fun a => c * (tsel a + t a + 1))
      (fun a => c * (ssel a + s a + 1)) := by
  have hbr : ∀ i : Colour, ComputableInTimeAndSpace
      (fun a => match i with | .red => red a | .green => green a | .blue => blue a)
      encIn encOut t s := by
    intro i
    cases i <;> assumption
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_match (encCond := encBool) hsel hbr
  have hsupt : ∀ a, Finset.univ.sup (fun _ : Colour => t a) ≤ t a :=
    fun a => Finset.sup_le fun _ _ => le_rfl
  have hsups : ∀ a, Finset.univ.sup (fun _ : Colour => s a) ≤ s a :=
    fun a => Finset.sup_le fun _ _ => le_rfl
  refine ⟨c, hc.mono (fun a => Nat.mul_le_mul_left _ (by have := hsupt a; omega))
    (fun a => Nat.mul_le_mul_left _ (by have := hsups a; omega))⟩

/-- Branches of *different* result types need no dependent version of the combinator: the output
type is the sigma, and the case analysis is the same theorem instantiated at it. What makes this
work is that computability depends only on the encoded strings, not on the types they encode, so
the eliminator's `motive` has no computational content. -/
example {α ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type}
    {sel : α → ι} {br : (i : ι) → α → β i}
    {encIn : α ↪ List Bool} {encBool : Bool ↪ List Bool} {encS : (Σ i, β i) ↪ List Bool}
    {tc sc t s : ι → α → ℕ}
    (htest : ∀ i, ComputableInTimeAndSpace (fun a => decide (sel a = i)) encIn encBool
      (tc i) (sc i))
    (hbr : ∀ i, ComputableInTimeAndSpace (fun a => (⟨i, br i a⟩ : Σ i, β i)) encIn encS
      (t i) (s i)) :
    ∃ c, ComputableInTimeAndSpace (fun a => (⟨sel a, br (sel a) a⟩ : Σ i, β i)) encIn encS
      (fun a => c * (Finset.univ.sup (fun i => tc i a) + Finset.univ.sup (fun i => t i a) + 1))
      (fun a => c * (Finset.univ.sup (fun i => sc i a)
        + Finset.univ.sup (fun i => s i a) + 1)) :=
  computableInTimeAndSpace_casesOn (br := fun i a => (⟨i, br i a⟩ : Σ i, β i))
    (fun i a h => by rw [h]) htest hbr

end CslibTests
