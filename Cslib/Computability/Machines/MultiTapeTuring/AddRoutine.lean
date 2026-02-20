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
public import Cslib.Computability.Machines.MultiTapeTuring.TMWithAuxTapes

namespace Turing

variable [Inhabited α] [Fintype α]
variable {aux k : ℕ}

namespace Routines

def isZero (i : Fin k.succ) := ite i (pop i <;> push i []) (pop i <;> push i [OneTwo.one])

@[simp, grind =]
theorem isZero_eval_list {k : ℕ} {i : Fin k.succ} {tapes : Fin k.succ → List (List OneTwo)}
  {h_tapes_i : tapes i ≠ []} :
  (isZero i).eval_list tapes = .some (Function.update tapes i (
    (if (tapes i).head h_tapes_i = [] then [OneTwo.one] else []) :: (tapes i).tail)) := by
  simp [isZero, ite_eval, h_tapes_i]
  grind

public def neq {k : ℕ} (q s t : Fin k.succ)
  (h_neq : q ≠ s := by decide) (h_neq' : q ≠ t := by decide) (h_neq'' : s ≠ t := by decide) :
  MultiTapeTM k.succ (WithSep OneTwo) :=
  (eq q s t h_neq h_neq' h_neq'') <;> (isZero ⟨t, by omega⟩)

@[simp, grind =]
public theorem neq_eval_list {k : ℕ} {q s t : Fin k.succ}
  {h_neq : q ≠ s} {h_neq' : q ≠ t} {h_neq'' : s ≠ t}
  {tapes : Fin k.succ → List (List OneTwo)}
  {h_q_nonempty : tapes q ≠ []} {h_s_nonempty : tapes s ≠ []} :
  (neq q s t (h_neq := h_neq) (h_neq' := h_neq') (h_neq'' := h_neq'')).eval_list tapes =
    Part.some (Function.update tapes t
      ((if (tapes q).head h_q_nonempty = (tapes s).head h_s_nonempty then
        []
      else
        [.one]) :: (tapes t))) := by
  simp [neq, h_q_nonempty, h_s_nonempty]

/-- Execute `tm` a number of times as given by the first word on tape `i`.
Note that the iteration counter is not directly available to the TM. -/
-- TODO maybe it's easier to require that `aux` is at least 3
def loop (i : Fin k) (tm : MultiTapeTMWithAuxTapes k aux (WithSep OneTwo)) :
    MultiTapeTMWithAuxTapes k (max aux 3) (WithSep OneTwo) :=
  sorry
  -- let tm := tm.add_aux_tapes 3
  -- let target : Fin (k + (aux + 3)) := ⟨k, by omega⟩
  -- let counter : Fin (k + (aux + 3)) := ⟨k.succ, by omega⟩
  -- let cond : Fin (k + (aux + 3)) := ⟨k.succ.succ, by omega⟩
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

def loop' (i : ℕ) {h_i : i < k}
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
theorem loop_eval_list {i : Fin k}
  {tm : MultiTapeTMWithAuxTapes k aux (WithSep OneTwo)}
  {tapes : Fin k → List (List OneTwo)}
  (h_tapes_i : tapes ⟨i, by omega⟩ ≠ []) :
  (loop i tm).eval_list_aux tapes =
      ((Part.bind · tm.eval_list_aux)^[dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)]
        (Part.some tapes)) := by
  sorry

@[simp]
theorem loop'_eval_list {i : ℕ} {h_i : i < k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {tapes : Fin (k + 3) → List (List OneTwo)}
  (h_tapes_i : tapes ⟨i, by omega⟩ ≠ []) :
  (loop' i tm (h_i := h_i)).eval_list tapes =
      (((Part.bind · tm.eval_list)^[dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)]
        (Part.some (tapes_take tapes k (by omega))))).map
          fun tapes' => tapes_extend_by tapes' tapes := by
  sorry

-- @[simp]
-- theorem loop_eval_list' {i : Fin k}
--   {tm : MultiTapeTM k (WithSep OneTwo)}
--   {tapes : Fin (k + 3) → List (List OneTwo)}
--   (h_tapes_i : tapes ⟨i, by omega⟩ ≠ []) :
--   (loop i tm).eval_list tapes =
--       (Part.bind · (tm.extend (k₂ := k + 3) (by omega)).eval_list)
--       ^[dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)]
--       (Part.some tapes) := by
--   sorry

/-- Execute `tm` in a loop as long as running `cond` pushes a non-empty value to the last tape. -/
def whileCond (cond : MultiTapeTM k.succ (WithSep α)) (tm : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k.succ (WithSep α) :=
  let k := ⟨k, by omega⟩
  cond <;>
  doWhile k ((pop k) <;> (tm.extend (by omega) <;> cond)) <;>
  (pop ⟨k, by omega⟩)

-- lemma whileCond_eval_list {cond : MultiTapeTM k.succ (WithSep α)}
--   {tm : MultiTapeTM k (WithSep α)}
--   {tm_f : Fin k.succ → List (List α) → Option (Fin k.succ → List (List α))}
--   {cond_f : (Fin k.succ → List (List α)) → List α}
--   {h_cond_f : ∀ t, cond.eval_list t = Part.some (Function.update t ⟨k, _⟩ ((cond_f t) :: (t ⟨k, _⟩)))}
--   {tapes : Fin k.succ → List (List α)}
--   {h_nonempty : tapes ⟨k, by omega⟩ ≠ []} :
--   (whileCond cond tm).eval_list tapes =
--     cond.eval_list tapes >>= fun tapes' =>
--       doWhile_eval_list ⟨k, by omega⟩
--         (Function.update tapes' ⟨k, by omega⟩ (tapes' ⟨k, by omega⟩.tail))
--         (pop ⟨k, by omega⟩)
--         (tm.extend (by omega) <;> cond) >>= fun tapes'' =>
--           pop.eval_list tapes'' := by
--   simp [whileCond, seq_eval_list, doWhile_eval_list, pop_eval_list]
--   grind


-- public def add₀ : MultiTapeTM 4 (WithSep OneTwo) :=
--   copy 1 2 <;> push 1 []
--   -- Here we have [a, 0 :: b, b]

-- lemma add₀_eval_list {a b : List OneTwo} {ls₁ ls₂ ls₃ ls₄ : List (List OneTwo)} :
--   add₀.eval_list
--     [a :: ls₁, b :: ls₂, ls₃, ls₄].get =
--     .some [a :: ls₁, [] :: b :: ls₂, b :: ls₃, ls₄].get := by
--   simp [add₀]
--   grind [add₀]

@[simp]
lemma succ_iter {k r : ℕ} {i : Fin k.succ} {tapes : Fin k.succ → List (List OneTwo)}
  {h_tapes_i : tapes i ≠ []} :
  (Part.bind · (succ i).eval_list)^[r] (.some tapes) = Part.some (Function.update tapes i (
    (dya ((dya_inv ((tapes i).head h_tapes_i)) + r)) :: (tapes i).tail)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    simp [ih, succ_eval_list]
    grind

@[simp]
lemma succ'_iter {k aux r : ℕ} {i : ℕ} {tapes : Fin k → List (List OneTwo)}
  {h_i_lt : i < k}
  {h_tapes_i : tapes ⟨i, h_i_lt⟩ ≠ []} :
  (Part.bind · (succ' (aux := aux) i h_i_lt).eval_list_aux)^[r] (.some tapes) =
    Part.some (Function.update tapes ⟨i, h_i_lt⟩ (
      (dya ((dya_inv ((tapes ⟨i, h_i_lt⟩).head h_tapes_i)) + r)) :: (tapes ⟨i, h_i_lt⟩).tail)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    simp [ih]
    grind

-- Add 0 and 1 and store the result in 2.
public def add₀ : MultiTapeTM 6 (WithSep OneTwo) :=
  (copy 1 2) <;> loop' (h_i := by decide) 0 (succ (k := 2) 2)

@[simp]
lemma Function.update_update {α β : Type} [DecidableEq α] {f : α → β} {i : α} {x y : β} :
  Function.update (Function.update f i x) i y = Function.update f i y := by
  grind

@[simp, grind =]
public theorem add₀_eval_list {tapes : Fin 6 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add₀.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 2)))) := by
  simp [add₀, h_nonempty₁, h_nonempty₀]
  grind

-- TODO do the 'aux, aux + 1, aux + 2' automatically.

public def add {k : ℕ} (i j l aux : ℕ)
  (h_bounds : i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ i < aux ∧ j < aux ∧ l < aux ∧ aux + 3 ≤ k + 6) :
  MultiTapeTM (k + 6) (WithSep OneTwo) :=
  add₀.with_tapes #v[
    ⟨i, by omega⟩, ⟨j, by omega⟩, ⟨l, by omega⟩,
    ⟨aux, by omega⟩, ⟨aux + 1, by omega⟩, ⟨aux + 2, by omega⟩] (h_le := by omega)

@[simp, grind =]
public theorem add_eval_list {i j l aux : ℕ}
  {h_bounds : i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ i < aux ∧ j < aux ∧ l < aux ∧ aux + 3 ≤ k + 6}
  {tapes : Fin (k + 6) → List (List OneTwo)}
  {h_nonempty_i : tapes ⟨i, by omega⟩ ≠ []}
  {h_nonempty_j : tapes ⟨j, by omega⟩ ≠ []} :
  (add i j l aux h_bounds).eval_list tapes =
      .some (Function.update tapes ⟨l, by omega⟩ (
        (dya (dya_inv ((tapes ⟨i, by omega⟩).head h_nonempty_i) +
          dya_inv ((tapes ⟨j, by omega⟩).head h_nonempty_j)) :: (tapes ⟨l, by omega⟩)))) := by
  sorry

-- TODO remove this? (inline)

-- TODO continue here:
-- I think we don't even need eval_list on Aux machines.
-- Check if it works to remove the whole aux machine stuff and instead provide an
-- aux variable explicitly

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
