/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.LoopCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

import Mathlib.Tactic.FinCases

namespace Turing

variable {k : ℕ}

namespace Routines

@[simp]
lemma succ_iter {k r : ℕ} {i : Fin k.succ} {tapes : Fin k.succ → List (List OneTwo)} :
  (Part.bind · (succ i).eval_list)^[r] (.some tapes) = Part.some (Function.update tapes i (
    if r ≠ 0 then
      (dya ((dya_inv ((tapes i).headD [])) + r)) :: (tapes i).tail
    else
      tapes i)) := by
  induction r with
    | zero => simp
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      simp [ih]
      grind

--- Add 0 and 1 and store the result in 2.
--- Assumes zero for an empty tape.
def add₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  (copy 1 2) <;> loop (h_i := by decide) 0 (succ 2)

@[simp, grind =]
theorem add₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  add₀.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).headD []) +
      dya_inv ((tapes 1).headD [])) :: (tapes 2)))) := by
  simp [add₀]
  by_cases h : dya_inv ((tapes 0).head?.getD []) = 0
  · simp [h]; grind
  · grind

/-- The value of succ's eval_list at index j when applied via get. -/
private lemma succ_eval_list_get_apply {k : ℕ} {i j : Fin k}
    {tapes : Fin k → List (List OneTwo)}
    (h : ((succ i).eval_list tapes).Dom) :
    ((succ i).eval_list tapes).get h j =
    (Function.update tapes i ((dya (dya_inv ((tapes i).headD [])).succ) :: (tapes i).tail)) j := by
  sorry


private lemma succ_space_at_iter {k : ℕ} (i j : Fin k)
    (h_halts : ∀ tapes, (succ i).haltsOn tapes)
    (n : ℕ) (tapes : Fin k → List (List OneTwo)) :
    (space_at_iter h_halts n tapes) j =
      if j = i then (listToString (((succ i).eval_list tapes).get (by sorry) j)).length
      else spaceUsed_init tapes j := by
  sorry

theorem add₀_spaceUsed {tapes : Fin 6 → List (List OneTwo)} :
  add₀.spaceUsed_list tapes (h_halts := by sorry) = fun j : Fin 6 =>
    match j with
    | 0 => spaceUsed_init tapes 0
    | 1 => 1 + spaceUsed_init tapes 1
    | 2 => max (((tapes 1).headD []).length + 1 + spaceUsed_init tapes 2)
               ((dya (dya_inv ((tapes 1).headD [])).succ).length + 1 + spaceUsed_init tapes 2)
    | 3 => ((tapes 0).headD []).length + 1 + spaceUsed_init tapes 3
    | 4 => ((tapes 0).headD []).length + 1 + spaceUsed_init tapes 4
    | 5 => ((tapes 0).headD []).length + 1 + spaceUsed_init tapes 5 := by
  -- Establish halting proofs for each component
  have h_halts_copy : ∀ t : Fin 6 → BiTape (WithSep OneTwo),
      (copy (k := 6) 1 2 (h_neq := by decide)).haltsOn t := by intro; sorry
  have h_halts_loop : ∀ t : Fin 6 → BiTape (WithSep OneTwo),
      (loop (h_i := by decide) (k := 3) 0 (succ (2 : Fin 3))).haltsOn t :=
    loop_halts_of_halts succ_halts
  -- Unfold add₀ = (copy 1 2) <;> loop 0 (succ 2), split space via seq
  simp only [add₀, MultiTapeTM.seq_spaceUsed_list h_halts_copy h_halts_loop]
  -- Compute the copy step's space usage and the intermediate tape state
  simp only [copy_spaceUsed_list, copy_eval_list]
  -- Expand the loop's space: aux tapes (≥3) get fixed formula, inner tapes (<3) use space_at_iter
  simp only [loop_space_list (h_halts := succ_halts)]
  -- Case analysis on tape index; apply succ_space_at_iter after j is concrete
  funext ⟨j, hj⟩
  match j, hj with
  | 0, _ =>
    simp only [succ_space_at_iter (2 : Fin 3) _ succ_halts]
    simp [Function.update, Fin.ext_iff]
  | 1, _ =>
    simp only [succ_space_at_iter (2 : Fin 3) _ succ_halts]
    simp [Function.update, Fin.ext_iff]
  | 2, _ =>
    simp only [succ_space_at_iter (2 : Fin 3) _ succ_halts]
    simp only [succ_eval_list_get_apply, Part.get_some, Function.update,
               Fin.ext_iff, listToString_length_cons]
    simp (config := { decide := true }) only [if_true, dif_pos, List.headD_cons, List.tail_cons,
               listToString_length_cons, spaceUsed_init_simp]
    simp only [show (⟨1, (by omega : 1 < 6)⟩ : Fin 6) = 1 from rfl,
               show (⟨2, (by omega : 2 < 6)⟩ : Fin 6) = 2 from rfl]
  | 3, _ => simp [Function.update, Fin.ext_iff]
  | 4, _ => simp [Function.update, Fin.ext_iff]
  | 5, _ => simp [Function.update, Fin.ext_iff]

/--
A Turing machine that adds the heads of tapes i and j (in dyadic encoding) and pushes the result
to tape l.
Assumes zero for an empty tape. -/
public def add (i j l : Fin (k + 6)) (aux : Fin (k + 6) := ⟨k + 3, by omega⟩)
  (h_inj : [i, j, l, aux, aux + 1, aux + 2].get.Injective := by decide) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  add₀.with_tapes [i, j, l, aux, aux + 1, aux + 2].get h_inj

@[simp, grind =]
public theorem add_eval_list (i j l aux : Fin (k + 6))
  {h_inj : [i, j, l, aux, aux + 1, aux + 2].get.Injective}
  {tapes : Fin (k + 6) → List (List OneTwo)} :
  (add i j l aux h_inj).eval_list tapes =
      .some (Function.update tapes l (
        (dya (dya_inv ((tapes i).headD []) + dya_inv ((tapes j).headD [])) :: (tapes l)))) := by
  simp [add]
  grind

-- Add head of 0 to head of 1 (and store it in head of 1).
def add_assign₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  add 0 1 2 (h_inj := by decide) <;> pop 1 <;> copy 2 1 <;> pop 2

@[simp]
lemma add_assign₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  add_assign₀.eval_list tapes = .some
    (Function.update tapes 1 ((dya (dya_inv ((tapes 0).headD []) +
      dya_inv ((tapes 1).headD [])) :: (tapes 1).tail))) := by
  simp [add_assign₀]
  grind

/--
A Turing machine that adds the head of tape `i` to the head of tape `j` (and updates the
head of tape `j` with the result). -/
public def add_assign
  (i j : Fin (k + 6))
  (aux : Fin (k + 6) := ⟨k + 2, by omega⟩)
  (h_inj : [i, j, aux, aux + 1, aux + 2, aux + 3].get.Injective := by decide) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  add_assign₀.with_tapes [i, j, aux, aux + 1, aux + 2, aux + 3].get h_inj

@[simp]
public theorem add_assign_eval_list {i j aux : Fin (k + 6)}
  {h_inj : [i, j, aux, aux + 1, aux + 2, aux + 3].get.Injective}
  {tapes : Fin (k + 6) → List (List OneTwo)} :
  (add_assign i j aux h_inj).eval_list tapes =
      .some (Function.update tapes j (
        (dya (dya_inv ((tapes i).headD []) +
          dya_inv ((tapes j).headD [])) :: (tapes j).tail))) := by
  simpa [add_assign] using apply_updates_function_update h_inj

end Routines

end Turing
