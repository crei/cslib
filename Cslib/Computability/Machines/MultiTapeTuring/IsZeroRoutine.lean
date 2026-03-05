/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.IteCombinator

namespace Turing

variable {k : ℕ}

namespace Routines

/--
A Turing machine that computes the logical negation: It replaces an empty (or non-existing) head
on tape `i` by the word "1" and everything else by the empty word. -/
public def isZero (i : Fin k) := ite i (pop i ;ₜ push i []) (pop i ;ₜ push i [OneTwo.one])

@[simp, grind =]
public theorem isZero_eval_list {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (isZero i).eval_list tapes = .some (Function.update tapes i (
    (if (tapes i).headD [] = [] then [OneTwo.one] else []) :: (tapes i).tail)) := by
  simp [isZero]
  grind

@[simp]
public theorem isZero_spaceUsed_list {i j : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (isZero i).spaceUsed_list tapes (by simp [isZero]) = Function.update (spaceUsed_init tapes) i
    (if (tapes i).headD [] = [] then
      (listToString ([OneTwo.one] :: (tapes i).tail)).length
    else
      (listToString (tapes i)).length) := by
  simp only [isZero, ite_spaceUsed_list]
  by_cases h : j = i
  · simp only [List.headD_eq_head?_getD, pop_halts, implies_true, push_halts_on,
    MultiTapeTM.seq_spaceUsed_list, pop_spaceUsed, pop_eval_list, Part.get_some,
    push_spaceUsed_list, Function.update_self, listToString_length_cons, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd]
    sorry
    -- cases (tapes i) with
    -- | nil =>  grind
    -- | cons hd tl => grind
  · simp [h]
    -- grind
    sorry


end Routines
end Turing
