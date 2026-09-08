/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concat

/-!
# Complexity of a generic constructor

A non-recursive inductive type is a finite sum of finite products,
`γ ≅ Σ (i : ι), Π (j : Fin kᵢ), A i j`, so its constructors and its eliminator are the introduction
rule of a finite product and the elimination rule of a finite coproduct. This file is the first of
those; `Cslib.Computability.Machines.Turing.MultiTape.Combinators.Ite` is the second.

The two are built the same way, by nesting the binary case once per field resp. per constructor:

* the eliminator nests `computableInTimeAndSpace_cond`, and the branches contribute their
  **supremum**, since only the branch that is taken runs;
* the constructor nests `computableInTimeAndSpace_concat`, and the fields contribute their
  **sum**, since every field is computed.

The tag of a constructor needs no work: it is a fixed string, and prefixing an encoding with a
fixed string is again an encoding, so `computableInTimeAndSpace_concat`'s hypothesis absorbs it.
A constructor with no fields is a constant, which is the base case of the induction.

## What this does not cover

The number of fields has to be a constant of the type. Each nesting costs one rewind of the input
tape, so `k` fields cost `k` times the input length in time; that is absorbed into the existential
constant only because `k` is fixed. A structure with a variable number of components — a list, a
tree — is not a finite product and needs the loop of
`Cslib.Computability.Machines.Turing.MultiTape.Combinators.Loop` with an iteration bound instead.
That is the same boundary as for the eliminator, where a recursive type needs a fold rather than a
case analysis.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_flatten`: finitely many computations, concatenated.
* `Turing.MultiTapeTM.computableInTimeAndSpace_ctor`: the same read as a constructor, for any
  encoding that is the concatenation of the encoded fields.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α δ : Type*}

/-- **Concatenating finitely many computations.** The bounds are the sums of the fields' bounds,
plus one rewind of the input tape per field.

Compare `computableInTimeAndSpace_casesOn`, which nests the *other* binary combinator and takes a
supremum: there only one branch runs, here every field does. -/
public theorem computableInTimeAndSpace_flatten {encIn : α ↪ List Bool}
    {k : ℕ} {fs : Fin k → α → List Bool} {t s : Fin k → α → ℕ}
    (hfs : ∀ j, ComputableInTimeAndSpace (fs j) encIn (Function.Embedding.refl (List Bool))
      (t j) (s j)) :
    ∃ c, ComputableInTimeAndSpace (fun a => (List.ofFn fun j => fs j a).flatten) encIn
      (Function.Embedding.refl (List Bool))
      (fun a => c * ((∑ j, t j a) + (encIn a).length + 1))
      (fun a => c * ((∑ j, s j a) + 1)) := by
  have key : ∀ (k : ℕ) (fs : Fin k → α → List Bool) (t s : Fin k → α → ℕ),
      (∀ j, ComputableInTimeAndSpace (fs j) encIn (Function.Embedding.refl (List Bool))
        (t j) (s j)) →
      ∃ c, ComputableInTimeAndSpace (fun a => (List.ofFn fun j => fs j a).flatten) encIn
        (Function.Embedding.refl (List Bool))
        (fun a => c * ((∑ j, t j a) + (encIn a).length + 1))
        (fun a => c * ((∑ j, s j a) + 1)) := by
    intro k
    induction k with
    | zero =>
      -- no fields: the result is the empty string
      intro fs t s _
      obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (α := α) (encIn := encIn)
        (encOut := Function.Embedding.refl (List Bool)) ([] : List Bool)
      refine ⟨c, hc.mono (fun a => ?_) (fun a => ?_)⟩
      · simpa using Nat.le_mul_of_pos_right c (by omega)
      · simp
    | succ k ih =>
      -- one more field, concatenated in front of the rest
      intro fs t s hfs
      obtain ⟨c₀, hc₀⟩ := ih (fun j => fs j.succ) (fun j => t j.succ) (fun j => s j.succ)
        fun j => hfs j.succ
      obtain ⟨c₁, hc₁⟩ := computableInTimeAndSpace_concat
        (h := fun a => fs 0 a ++ (List.ofFn fun j => fs j.succ a).flatten)
        (encD := Function.Embedding.refl (List Bool)) (fun _ => rfl) (hfs 0) hc₀
      have hfun : (fun a => fs 0 a ++ (List.ofFn fun j => fs j.succ a).flatten) =
          fun a => (List.ofFn fun j => fs j a).flatten := by
        funext a
        rw [List.ofFn_succ]
        rfl
      rw [hfun] at hc₁
      refine ⟨c₀ + c₁ + 4, hc₁.mono (fun a => ?_) (fun a => ?_)⟩
      · rw [Fin.sum_univ_succ]
        have hmul : c₀ * ((∑ j : Fin k, t j.succ a) + (encIn a).length + 1)
            ≤ c₀ * (t 0 a + (∑ j : Fin k, t j.succ a) + (encIn a).length + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hexp : (c₀ + c₁ + 4) * (t 0 a + (∑ j : Fin k, t j.succ a) + (encIn a).length + 1)
            = c₀ * (t 0 a + (∑ j : Fin k, t j.succ a) + (encIn a).length + 1)
              + c₁ * (t 0 a + (∑ j : Fin k, t j.succ a) + (encIn a).length + 1)
              + 4 * (t 0 a + (∑ j : Fin k, t j.succ a) + (encIn a).length + 1) := by ring
        omega
      · rw [Fin.sum_univ_succ]
        have hmul : c₀ * ((∑ j : Fin k, s j.succ a) + 1)
            ≤ c₀ * (s 0 a + (∑ j : Fin k, s j.succ a) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hc₁le : c₁ ≤ c₁ * (s 0 a + (∑ j : Fin k, s j.succ a) + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have hexp : (c₀ + c₁ + 4) * (s 0 a + (∑ j : Fin k, s j.succ a) + 1)
            = c₀ * (s 0 a + (∑ j : Fin k, s j.succ a) + 1)
              + c₁ * (s 0 a + (∑ j : Fin k, s j.succ a) + 1)
              + 4 * (s 0 a + (∑ j : Fin k, s j.succ a) + 1) := by ring
        omega
  exact key k fs t s hfs

/-- **Complexity of a generic constructor.** If every field is computable and the encoding of the
constructed value is the concatenation of the encoded fields, then the constructor is computable.

Nothing is asked of the encoding beyond `henc`: building a value needs no computability assumption
on its encoding, unlike taking one apart, which is why the destructors of a type are collected as
requirements in `Cslib.Computability.Machines.Turing.MultiTape.Encodings.Option` and its kin while
the constructors are not. -/
public theorem computableInTimeAndSpace_ctor {k : ℕ} {A : Fin k → Type*}
    {fs : (j : Fin k) → α → A j} {h : α → δ}
    {encIn : α ↪ List Bool} {encA : (j : Fin k) → A j ↪ List Bool} {encD : δ ↪ List Bool}
    {t s : Fin k → α → ℕ}
    (henc : ∀ a, encD (h a) = (List.ofFn fun j => encA j (fs j a)).flatten)
    (hfs : ∀ j, ComputableInTimeAndSpace (fs j) encIn (encA j) (t j) (s j)) :
    ∃ c, ComputableInTimeAndSpace h encIn encD
      (fun a => c * ((∑ j, t j a) + (encIn a).length + 1))
      (fun a => c * ((∑ j, s j a) + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_flatten (encIn := encIn)
    (fs := fun j a => encA j (fs j a)) (t := t) (s := s)
    fun j => (hfs j).congr (fun _ => rfl) fun _ => rfl
  exact ⟨c, hc.congr (fun _ => rfl) henc⟩

end Turing.MultiTapeTM
