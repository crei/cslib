/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.LoopCombinator

import Mathlib.Data.Nat.Bits

namespace Turing

namespace Routines

def succ₀ : MultiTapeTM 1 (WithSep OneTwo) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
lemma succ₀_eval_list {tapes : Fin 1 → List (List OneTwo)} :
  succ₀.eval_list tapes = .some (Function.update tapes 0
    ((dya (dya_inv ((tapes 0).headD [])).succ) :: (tapes 0).tail)) := by
  sorry

/--
A Turing machine that increments the head of tape `i` by one (in dyadic encoding).
Pushes zero if the tape is empty. -/
public def succ {k : ℕ} (i : Fin k) : MultiTapeTM k (WithSep OneTwo) :=
  succ₀.with_tapes [i].get (by intro x y; grind)

@[simp]
public theorem succ_halts {k : ℕ} {i : Fin k} : ∀ tapes, (succ i).haltsOn tapes := by
  sorry

@[simp]
public theorem succ_eval_list {k : ℕ} {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (succ i).eval_list tapes = .some (Function.update tapes i
    ((dya (dya_inv ((tapes i).headD [])).succ) :: (tapes i).tail)) := by
  simpa [succ] using apply_updates_function_update (by intro x y; grind)

lemma succ₀_evalWithStats_list {n : ℕ} {ls : List (List OneTwo)} :
  succ₀.evalWithStats_list [(dya n) :: ls].get =
    .some (
      [(dya n.succ) :: ls].get,
      -- this depends on if we have overflow on the highest dyadic character or not.
      if (dya n.succ).length = (dya n).length then
        [⟨0, (dya n).length, 0, by omega⟩].get
      else
        [⟨-1, (dya n).length, -1, by omega⟩].get) := by
  sorry

@[simp, grind =]
lemma succ_spaceUsed {k : ℕ} {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (succ i).spaceUsed_list tapes sorry = Function.update (spaceUsed_init tapes) i
    1 + ((dya (dya_inv ((tapes i).headD [])).succ) :: (tapes i).tail).length := by
  sorry
  --   (if (dya (dya_inv ((tapes i).headD [])).succ).length = ((tapes i).headD []).length then
  --     1 + (listToString (tapes i)).length -- We need to move at least one char to the left.
  --   else
  --     2 + (listToString (tapes i)).length) -- We need to move at least one char to the left
  -- := by sorry

@[simp]
lemma succ_spaceUsed_mono_iter {k : ℕ} {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (succ i).spaceUsed_list tapes (by simp) i ≤
    (succ i).spaceUsed_list (((succ i).eval_list tapes).get (by simp)) succ_halts i := by
  simp


@[simp]
lemma succ_output_length_mono {k : ℕ} {i j : Fin k} : output_length_mono (succ i) j := by
  apply output_length_mono_iff.mpr
  intro tapes
  simp [output_length_value]
  sorry

@[simp]
lemma succ_space_use_is_output_length {k : ℕ} {i j : Fin k} :
    space_use_is_output_length (succ i) j := by
  apply space_use_is_output_length_iff.mpr
  intro tapes
  simp [output_length_value]

  -- TODO this is actually wrong!




  sorry

end Routines

end Turing
