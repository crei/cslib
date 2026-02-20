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
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.WhileCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.IteCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.EqualRoutine

namespace Turing

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

namespace Routines

def isZero (i : Fin k) := ite i (pop i <;> push i []) (pop i <;> push i [OneTwo.one])

@[simp, grind =]
theorem isZero_eval_list {k : ℕ} {i : Fin k} {tapes : Fin k → List (List OneTwo)} :
  (isZero i).eval_list tapes = .some (Function.update tapes i (
    (if (tapes i).headD [] = [] then [OneTwo.one] else []) :: (tapes i).tail)) := by
  simp [isZero]
  grind

public def neq {k : ℕ} (q s t : Fin k)
  (h_inj : [q, s, t].get.Injective := by decide) :
  MultiTapeTM k (WithSep OneTwo) := eq q s t <;> isZero t

@[simp, grind =]
public theorem neq_eval_list {k : ℕ} {q s t : Fin k}
  {h_inj : [q, s, t].get.Injective}
  {tapes : Fin k → List (List OneTwo)} :
  (neq q s t h_inj).eval_list tapes =
    Part.some (Function.update tapes t
      ((if (tapes q).headD [] = (tapes s).headD [] then
        []
      else
        [.one]) :: (tapes t))) := by
  -- TOOD why do we need to instantiate eq_eval_list here?
  simp_all [neq, eq_eval_list (h_inj := h_inj)]

/-- Execute `tm` a number of times as given by the first word on tape `i`.
If tape `i` is empty, do not execute the TM.
Note that the iteration counter is not directly available to the TM. -/
def loop (i : ℕ) {h_i : i < k}
  (tm : MultiTapeTM k (WithSep OneTwo)) : MultiTapeTM (k + 3) (WithSep OneTwo) :=
  sorry
  -- let target : Fin (k + (aux + 3)) := ⟨aux, by omega⟩
  -- let counter : Fin (k + (aux + 3)) := ⟨aux + 1, by omega⟩
  -- let cond : Fin (k + (aux + 3)) := ⟨aux + 2, by omega⟩
  -- (copy (k := k + (aux + 3)) i target (h_neq := by grind) <;>
  -- push counter [] <;>
  -- neq target counter cond (by grind) (by grind) (by grind) <;>
  -- doWhile cond (
  --   pop cond <;>
  --   tm.toMultiTapeTM <;>
  --   succ counter <;>
  --   neq target counter cond (by grind) (by grind) (by grind)) <;>
  -- pop cond <;>
  -- pop counter <;>
  -- pop target).set_aux_tapes (aux + 3)


@[simp]
theorem loop_eval_list {i : ℕ} {h_i : i < k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {tapes : Fin (k + 3) → List (List OneTwo)} :
  (loop i tm (h_i := h_i)).eval_list tapes =
      (((Part.bind · tm.eval_list)^[dya_inv ((tapes ⟨i, by omega⟩).headD [])]
        (Part.some (tapes_take tapes k (by omega))))).map
          fun tapes' => tapes_extend_by tapes' tapes := by
  sorry

@[simp]
lemma succ_iter {k r : ℕ} {i : Fin k.succ} {tapes : Fin k.succ → List (List OneTwo)} :
  (Part.bind · (succ i).eval_list)^[r] (.some tapes) = Part.some (Function.update tapes i (
    if h : tapes i ≠ [] then
      (dya ((dya_inv ((tapes i).head h)) + r)) :: (tapes i).tail
    else
      tapes i)) := by
  induction r with
    | zero => simp
    | succ r ih =>
      rw [Function.iterate_succ_apply']
      simp [ih, succ_eval_list]
      by_cases h_empty : tapes i = []
      · simp [h_empty]
      · simp [h_empty]
        grind

-- Add 0 and 1 and store the result in 2.
-- Assumes zero for an empty tape.
public def add₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  (copy 1 2) <;> loop (h_i := by decide) 0 (succ 2)

@[simp, grind =]
public theorem add₀_eval_list {tapes : Fin 6 → List (List OneTwo)} :
  add₀.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).headD []) +
      dya_inv ((tapes 1).headD [])) :: (tapes 2)))) := by
  simp [add₀]
  grind

-- TODO we could also use `k + 3` for aux and thus assume it's always the last `aux` tapes.

public def add (i j l aux : Fin (k + 6))
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
def add_assign₀' : MultiTapeTM 6 (WithSep OneTwo) :=
  add 0 1 2 3 (by decide) <;> pop 1 <;> copy 2 1 <;> pop 2

@[simp]
lemma add_assign₀'_eval_list_aux {tapes : Fin 6 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add_assign₀'.eval_list tapes = .some
    (Function.update tapes 1 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 1).tail))) := by
  simp [add_assign₀', h_nonempty₁, h_nonempty₀]
  grind

@[simp]
lemma add_assign₀'_eval_list {tapes : Fin 6 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add_assign₀'.eval_list tapes = .some
    (Function.update tapes 1 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 1).tail))) := by
  simp [add_assign₀', h_nonempty₁, h_nonempty₀]
  grind

public def add_assign
  (i j aux : ℕ)
  (h_bounds : i ≠ j ∧ i < aux ∧ j < aux ∧ aux + 4 ≤ k + 6) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  add_assign₀'.with_tapes #v[
    ⟨i, by omega⟩, ⟨j, by omega⟩,
    ⟨aux, by omega⟩, ⟨aux + 1, by omega⟩, ⟨aux + 2, by omega⟩, ⟨aux + 3, by omega⟩]
    (h_le := by omega)

public theorem add_assign_eval_list {i j aux : ℕ}
  {h_bounds : i ≠ j ∧ i < aux ∧ j < aux ∧ aux + 4 ≤ k + 6}
  {tapes : Fin (k + 6) → List (List OneTwo)}
  {h_nonempty_i : tapes ⟨i, by omega⟩ ≠ []}
  {h_nonempty_j : tapes ⟨j, by omega⟩ ≠ []} :
  (add_assign i j aux h_bounds).eval_list tapes =
      .some (Function.update tapes ⟨j, by omega⟩ (
        (dya (dya_inv ((tapes ⟨i, by omega⟩).head h_nonempty_i) +
          dya_inv ((tapes ⟨j, by omega⟩).head h_nonempty_j)) :: (tapes ⟨j, by omega⟩).tail))) := by
  sorry

-- Multiplies the heads of 0 and 1 and stores the result in 2.
public def mul : MultiTapeTM 10 (WithSep OneTwo) :=
  (push 2 []) <;> loop' 0 (h_i := by omega) (add_assign (k := 1) 1 2 3 (by omega))

@[simp]
lemma add_assign_iter {k i j aux r : ℕ}
  {h_bounds : i ≠ j ∧ i < aux ∧ j < aux ∧ aux + 4 ≤ k + 6}
  {tapes : Fin (k + 6) → List (List OneTwo)}
  {h_tapes_i : tapes ⟨i, by omega⟩ ≠ []}
  {h_tapes_j : tapes ⟨j, by omega⟩ ≠ []} :
  (Part.bind · (add_assign i j aux h_bounds).eval_list)^[r] (.some tapes) =
    Part.some (Function.update tapes ⟨j, by omega⟩ (
      (dya ((dya_inv ((tapes ⟨j, by omega⟩).head h_tapes_j)) +
        r * (dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)))) ::
        (tapes ⟨j, by omega⟩).tail)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    simp only [ih, Part.bind_some]
    rw [add_assign_eval_list]
    · simp; grind
    · grind
    · grind

public theorem mul_eval_list {tapes : Fin 10 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  mul.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).head h_nonempty₀) *
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 2)))) := by
  simp [mul, h_nonempty₀, h_nonempty₁]
  grind

end Routines

end Turing
