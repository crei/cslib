/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.StackTape
public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Tactic.SetLike
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.Ring

/-!
# BiTape: Bidirectionally infinite TM tape representation using StackTape

This file defines `BiTape`, a tape representation for Turing machines
in the form of an `List` of `Option` values,
with the additional property that the list cannot end with `none`.

## Design

Note that Mathlib has a `Tape` type, but it requires the alphabet type to be inhabited,
and considers the ends of the tape to be filled with default values.

This design requires the tape elements to be `Option` values, and ensures that
`List`s of the base alphabet, rendered directly onto the tape by mapping over `some`,
will not collide.

## Main definitions

* `BiTape`: A tape with a head symbol and left/right contents stored as `StackTape`
* `BiTape.move`: Move the tape head left or right
* `BiTape.write`: Write a symbol at the current head position
* `BiTape.space_used`: The space used by the tape
-/

@[expose] public section

namespace Turing

@[ext]
structure BiTape (Symbol : Type) where
  /-- the tape contents -/
  cells : ℤ → Option Symbol

namespace BiTape

variable {Symbol : Type}

/-- The empty `BiTape` -/
def nil : BiTape Symbol := ⟨fun _ => none⟩

instance : Inhabited (BiTape Symbol) where
  default := nil

instance : EmptyCollection (BiTape Symbol) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil : (∅ : BiTape Symbol) = nil := rfl

/--
Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def mk₁ {Symbol : Type} (l : List Symbol) : BiTape Symbol :=
  { cells
    | .ofNat n => l[n]?
    | _ => none }

section Move

@[simp, local grind =]
def optionMoveToInt : Option Dir → ℤ
  | none => 0
  | some .left => -1
  | some .right => 1

@[simp, local grind =]
def moveInt (t : BiTape Symbol) (δ : ℤ) : BiTape Symbol := ⟨ fun i => t.cells (i - δ) ⟩

/--
Optionally perform a `move`, or do nothing if `none`.
-/
@[simp, local grind =]
def optionMove (t : BiTape Symbol) (dir : Option Dir) : BiTape Symbol :=
  t.moveInt (optionMoveToInt dir)

end Move

/--
Write a value under the head of the `BiTape`.
-/
@[local grind =]
def write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol :=
  ⟨ Function.update t.cells 0 a ⟩

@[local grind =]
def read (t : BiTape Symbol) : Option Symbol := t.cells 0

@[simp]
lemma write_read (t : BiTape Symbol) : t.write t.read = t := by simp [write, read]

/--
The cells of `t` are non-blank only at indices in `s`.
-/
def supportSubset (t : BiTape Symbol) (s : Finset ℤ) : Prop :=
  ∀ i, t.cells i ≠ none → i ∈ s

lemma supportSubset_mk₁ (l : List Symbol) :
    supportSubset (mk₁ l) ((Finset.range l.length).image (Int.ofNat ·)) := by
  intro i hi
  simp only [mk₁] at hi
  match i with
  | .ofNat n => grind
  | .negSucc n => grind

lemma supportSubset_write_insert (t : BiTape Symbol) (a : Option Symbol) (s : Finset ℤ)
    (hs : supportSubset t s) : supportSubset (t.write a) (insert 0 s) := by
  intro i hi
  simp only [write] at hi
  by_cases h : i = 0
  · simp [h]
  · rw [Function.update_of_ne h] at hi
    exact Finset.mem_insert_of_mem (hs i hi)

lemma supportSubset_moveInt (t : BiTape Symbol) (δ : ℤ) (s : Finset ℤ)
    (hs : supportSubset t s) :
    supportSubset (t.moveInt δ) (s.image (· + δ)) := by
  intro i hi
  simp only [moveInt] at hi
  exact Finset.mem_image.mpr ⟨i - δ, hs _ hi, by ring⟩

lemma supportSubset_optionMove (t : BiTape Symbol) (d : Option Dir) (s : Finset ℤ)
    (hs : supportSubset t s) :
    supportSubset (t.optionMove d) (s.image (· + optionMoveToInt d)) :=
  supportSubset_moveInt _ _ _ hs

end BiTape

end Turing
