/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.LoopCombinator

namespace Turing

namespace Routines

def dec₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  push 1 [] <;> push 2 [] <;>
  loop 0 (h_i := by decide) (pop 2 <;> copy 1 2 <;> succ 1) <;>
  pop 0 <;>
  copy 2 0 <;>
  pop 2 <;>
  pop 1

@[simp]
lemma inner_eval_list {tapes : Fin 3 → List (List OneTwo)} :
  (pop 2 <;> copy 1 2 <;> succ 1).eval_list tapes = .some (
    (if h : tapes 1 = [] then Function.update tapes 2 ((tapes 1).head?.getD [] :: (tapes 2).tail)
  else
    Function.update (Function.update tapes 2 ((tapes 1).head?.getD [] :: (tapes 2).tail)) 1
      (dya (dya_inv ((tapes 1).headD []) + 1) :: (tapes 1).tail))) := by
  simp
  grind

@[simp]
lemma inner_eval_iter {r : ℕ} {tapes : Fin 3 → List (List OneTwo)} :
  (Part.bind · (pop 2 <;> copy 1 2 <;> succ 1).eval_list)^[r] (.some tapes) = Part.some (
    if r = 0 then
      tapes
    else if tapes 1 = [] then
      Function.update tapes 2 ([] :: (tapes 2).tail)
    else
      Function.update (Function.update tapes
        2 ((dya ((dya_inv ((tapes 1).headD [])) + (r - 1))) :: (tapes 2).tail))
        1 ((dya ((dya_inv ((tapes 1).headD [])) + r)) :: (tapes 1).tail)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    simp [ih, inner_eval_list, -copy_eval_list, -succ_eval_list, -pop_eval_list, -MultiTapeTM.seq_eval_list]
    by_cases h_tape1_empty : tapes 1 = []
    · simp [h_tape1_empty]
      by_cases h : r = 0
      · simp [h]; grind
      · simp [h]; grind
    · simp [h_tape1_empty]
      by_cases h : r = 0
      · simp [h, h_tape1_empty]
      · simp [h]; grind

@[simp, grind =]
lemma dec₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  dec₀.eval_list tapes = .some (Function.update tapes 0
    ((dya ((dya_inv ((tapes 0).headD [])) - 1)) :: (tapes 0).tail)) := by
  simp [dec₀]
  grind

/--
A Turing machine that decrements the dyadic value at the head of tape `i`.
If the value is zero already, keeps it at zero. If the tape is empty, pushes zero.
-/
public def dec {k : ℕ} (i : Fin (k + 3))
  (aux : Fin (k + 3) := ⟨k, by omega⟩)
  (h_inj : [i, aux, aux + 1].get.Injective := by intro x y; grind) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  push ⟨aux, by omega⟩ [] <;> push ⟨aux + 1, by omega⟩ [] <;>
  loop i (h_i := by omega) (copy aux (aux + 1) (by sorry) <;> succ aux) <;>
  pop ⟨i, by omega⟩ <;>
  copy ⟨aux + 1, by omega⟩ ⟨i, by omega⟩ (by sorry) <;>
  pop ⟨aux + 1, by omega⟩ <;>
  pop ⟨aux, by omega⟩

@[simp, grind =]
public theorem duplicate_eval_list {k : ℕ} {i : Fin k.succ}
  (aux : Fin k.succ := ⟨k, by omega⟩)
  (h_inj : [i, aux].get.Injective)
  {tapes : Fin k.succ → List (List OneTwo)} :
  (duplicate i aux h_inj).eval_list tapes = Part.some (Function.update tapes i
    (((tapes i).headD []) :: (tapes i))) := by
  simp [duplicate]
  grind

end Routines

end Turing
