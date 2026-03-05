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
lemma copy₁_spaceUsed_list {tapes : Fin 2 → List (List α)} :
  copy₁.spaceUsed_list (by simp) tapes = Function.update (Function.update (spaceUsed_init tapes)
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
public lemma copy_spaceUsed_list {k : ℕ} (i j : Fin k)
  (h_inj : [i, j].get.Injective := by intro x y; grind)
  {tapes : Fin k → List (List α)} :
  (copy i j h_inj).spaceUsed_list (by simp) tapes =
    Function.update (Function.update (spaceUsed_init tapes)
    i (1 + (listToString (tapes i)).length))
    j (listToString (((tapes i).headD []) :: tapes j)).length := by
  sorry

end Routines

end Turing
