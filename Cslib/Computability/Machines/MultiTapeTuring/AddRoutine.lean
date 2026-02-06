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

namespace Routines

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

-- a
-- b
-- 0

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
  (eq q s t (h_neq := h_neq) (h_neq' := h_neq') (h_neq'' := h_neq'')).eval_list tapes =
    Part.some (Function.update tapes t
      ((if (tapes q).head h_q_nonempty = (tapes s).head h_s_nonempty then
        []
      else
        [.one]) :: (tapes t))) := by
  sorry

/-- Execute `tm` a number of times as given by the first word on tape `i`.
Note that the iteration counter is not directly available to the TM. -/
def loop (i : Fin k) (tm : MultiTapeTM k (WithSep OneTwo)) :
    MultiTapeTM (k + 3) (WithSep OneTwo) :=
  let target : Fin (k + 3) := ⟨k, by omega⟩
  let counter : Fin (k + 3) := ⟨k.succ, by omega⟩
  let cond : Fin (k + 3) := ⟨k.succ.succ, by omega⟩
  copy ⟨i, by omega⟩ target (h_neq := by grind) <;>
  push counter [] <;>
  neq target counter cond (by grind) (by grind) (by grind) <;>
  doWhile cond (
    pop cond <;>
    tm.extend (by omega) <;>
    succ counter <;>
    neq target counter cond (by grind) (by grind) (by grind)) <;>
  pop cond <;>
  pop counter <;>
  pop target

theorem loop_eval_list_inner {i : Fin k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {f_tm : (Fin k → List (List OneTwo)) → (Fin k → List (List OneTwo))}
  {tapes : Fin (k + 3) → List (List OneTwo)}
  {h_tapes_i : tapes ⟨i, by omega⟩ ≠ []} :
  let target : Fin (k + 3) := ⟨k, by omega⟩
  let counter : Fin (k + 3) := ⟨k.succ, by omega⟩
  let cond : Fin (k + 3) := ⟨k.succ.succ, by omega⟩
  (pop cond <;>
    tm.extend (by omega) <;>
    succ counter <;>
    neq target counter cond (by grind) (by grind) (by grind)).eval_list tapes = do
    let tapes := (tm.extend (by omega)).eval_list tapes
    Function.update tapes counter (
      (dya ((dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)).succ)) :: (tapes counter).tail) := by
    tm.eva
  (loop i tm).eval_list tapes = .some
    fun j => if h : j < k then
      (f_tm^[dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)] (fun i => tapes ⟨i, by omega⟩)) ⟨j, h⟩
    else
      tapes j := by
  sorry

theorem loop_eval_list {i : Fin k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {f_tm : (Fin k → List (List OneTwo)) → (Fin k → List (List OneTwo))}
  {tapes : Fin (k + 3) → List (List OneTwo)}
  {h_tapes_i : tapes ⟨i, by omega⟩ ≠ []} :
  (loop i tm).eval_list tapes = .some
    fun j => if h : j < k then
      (f_tm^[dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)] (fun i => tapes ⟨i, by omega⟩)) ⟨j, h⟩
    else
      tapes j := by
  sorry

/-- Execute `tm` in a loop as long as running `cond` pushes a non-empty value to the last tape. -/
def whileCond (cond : MultiTapeTM k.succ (WithSep α)) (tm : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k.succ (WithSep α) :=
  let k := ⟨k, by omega⟩
  cond <;>
  doWhile k ((pop k) <;> (tm.extend (by omega) <;> cond)) <;>
  (pop ⟨k, by omega⟩)

lemma whileCond_eval_list {cond : MultiTapeTM k.succ (WithSep α)}
  {tm : MultiTapeTM k (WithSep α)}
  {tm_f : Fin k.succ → List (List α) → Option (Fin k.succ → List (List α))}
  {cond_f : (Fin k.succ → List (List α)) → List α}
  {h_cond_f : ∀ t, cond.eval_list t = Part.some (Function.update t ⟨k, _⟩ ((cond_f t) :: (t ⟨k, _⟩)))}
  {tapes : Fin k.succ → List (List α)}
  {h_nonempty : tapes ⟨k, by omega⟩ ≠ []} :
  (whileCond cond tm).eval_list tapes =
    cond.eval_list tapes >>= fun tapes' =>
      doWhile_eval_list ⟨k, by omega⟩
        (Function.update tapes' ⟨k, by omega⟩ (tapes' ⟨k, by omega⟩.tail))
        (pop ⟨k, by omega⟩)
        (tm.extend (by omega) <;> cond) >>= fun tapes'' =>
          pop.eval_list tapes'' := by
  simp [whileCond, seq_eval_list, doWhile_eval_list, pop_eval_list]
  grind


-- public def add₀ : MultiTapeTM 4 (WithSep OneTwo) :=
--   copy 1 2 <;> push 1 []
--   -- Here we have [a, 0 :: b, b]

-- lemma add₀_eval_list {a b : List OneTwo} {ls₁ ls₂ ls₃ ls₄ : List (List OneTwo)} :
--   add₀.eval_list
--     [a :: ls₁, b :: ls₂, ls₃, ls₄].get =
--     .some [a :: ls₁, [] :: b :: ls₂, b :: ls₃, ls₄].get := by
--   simp [add₀]
--   grind [add₀]

public def add₀ : MultiTapeTM 4 (WithSep OneTwo) :=
  (((copy 1 2 <;> push 1 []) <;>
  -- Here we have [a, 0 :: b, b]
  (whileCond ((eq 0 1 3) <;> isZero 3) (succ 1 <;> succ 2))) <;>
  -- Here we have [a, a :: b, a + b]
  (pop 1))

-- lemma add₀_while_eval_list {tapes : Fin 4 → List (List OneTwo)}
--   {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
--   (whileCond ((eq 0 1 3) <;> not 3) (succ 1 <;> succ 2)).eval_list tapes = .some
--     (Function.update tapes 2 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
--       dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 2)))) := by

@[simp, grind =]
theorem add₀_eval_list {tapes : Fin 4 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add₀.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 2)))) := by
  sorry

-- --- Repeatedly run a sub routine as long as a condition on the symbol
-- --- at the first head is true.
-- public def ite (tm₁ tm₂ : MultiTapeTM k.succ (WithSep α)) :
--     MultiTapeTM k.succ (WithSep α) where
--   Λ := PUnit
--   q₀ := 0
--   M _ syms := sorry

-- @[simp]
-- public theorem ite_eval
--   (tm₁ tm₂ : MultiTapeTM k.succ (WithSep α))
--   (tapes : Fin k.succ → List (List α))
--   (h_nonempty : tapes 0 ≠ []) :
--   (ite tm₁ tm₂).eval_list tapes =
--     if (tapes 0).head h_nonempty = [] then tm₂.eval_list tapes else tm₁.eval_list tapes := by
--   sorry

end Routines

end Turing
