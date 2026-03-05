/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

def copy₁ : MultiTapeTM 2 (WithSep α) where
  State := PUnit
  stateFintype := inferInstance
  q₀ := PUnit.unit
  tr _ syms := sorry

@[simp]
lemma copy₁_eval_list {tapes : Fin 2 → List (List α)} :
  copy₁.eval_list tapes =
    Part.some (Function.update tapes 1 (((tapes 0).headD []) :: tapes 1)) := by
  sorry

@[simp]
lemma copy₁_halts {tapes : Fin 2 → BiTape (WithSep α)} :
  copy₁.haltsOn tapes := by
  sorry

@[simp]
lemma copy₁_spaceUsed_list {tapes : Fin 2 → List (List α)} :
  copy₁.spaceUsed_list tapes = Function.update (Function.update (spaceUsed_init tapes)
    0 (1 + (listToString (tapes 0)).length))
    1 (listToString (((tapes 0).headD []) :: tapes 1)).length := by
  sorry


/--
A Turing machine that copies the first word on tape `i` to tape `j`.
If Tape `i` is empty, pushes the empty word to tape `j`.
-/
public def copy {k : ℕ} (i j : Fin k)
  (h_inj : [i, j].get.Injective := by intro x y; grind) :
    MultiTapeTM k (WithSep α) :=
  copy₁.with_tapes [i, j].get h_inj

@[simp]
public lemma copy_halts {k : ℕ} {i j : ℕ} {h_neq : i ≠ j} {h_i_lt : i < k} {h_j_lt : j < k}
  {tapes : Fin k → BiTape (WithSep α)} :
  (copy i j (h_neq := h_neq) (h_i_lt) (h_j_lt)).haltsOn tapes = true := by
  simp [copy]

@[simp, grind =]
public lemma copy_eval_list
  {k : ℕ}
  {i j : Fin k}
  (h_inj : [i, j].get.Injective)
  {tapes : Fin k → List (List α)} :
  (copy i j h_inj).eval_list tapes = Part.some
    (Function.update tapes j (((tapes i).headD []) :: (tapes j))) := by
  simp_all [copy]
  grind

@[simp]
public lemma copy_spaceUsed_list
  {k : ℕ} {i j : ℕ} {h_neq : i ≠ j} {h_i_lt : i < k} {h_j_lt : j < k}
  {tapes : Fin k → List (List α)} :
  (copy i j h_neq h_i_lt h_j_lt).spaceUsed_list tapes (by simp [copy]) =
    Function.update (Function.update (spaceUsed_init tapes)
    ⟨i, h_i_lt⟩ (1 + (listToString (tapes ⟨i, h_i_lt⟩)).length))
    ⟨j, h_j_lt⟩ (listToString (((tapes ⟨i, h_i_lt⟩).headD []) :: tapes ⟨j, h_j_lt⟩)).length := by
  have h_inj : [(⟨i, h_i_lt⟩ : Fin k), ⟨j, h_j_lt⟩].get.Injective := by intro x y; grind
  simp_all [copy, apply_updates_function]
  grind

end Routines

end Turing
