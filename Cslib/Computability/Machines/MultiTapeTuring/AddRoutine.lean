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

public structure MultiTapeTMWithAuxTapes (k aux : ℕ) (α : Type)
    extends MultiTapeTM (k + aux) (WithSep α)

--- Adds `aux` many tapes to the TM, which are guaranteed to be restored to their original
--- content at the end of the computation.
public def MultiTapeTM.allocate_aux_tapes (tm : MultiTapeTM k (WithSep α)) (aux : ℕ) :
    MultiTapeTMWithAuxTapes k aux α where
  toMultiTapeTM := tm.extend (by omega)

--- Sets the last `aux` many tapes to be aux tapes, which are guaranteed to be restored to their
--- original content at the end of the computation.
public def MultiTapeTM.set_aux_tapes (aux : ℕ) (tm : MultiTapeTM (k + aux) (WithSep α)) :
    MultiTapeTMWithAuxTapes k aux α where
  toMultiTapeTM := tm

public def MultiTapeTMWithAuxTapes.with_tapes
  {aux₁ aux₂ k₁ k₂ : ℕ}
  {h_le_k : k₁ ≤ k₂}
  {h_le_aux : aux₁ ≤ aux₂}
  (tm : MultiTapeTMWithAuxTapes k₁ aux₁ α)
  (seq : Vector (Fin k₂) k₁) : MultiTapeTMWithAuxTapes k₂ aux₂ α :=
  -- For (i, t) in seq, we need to swap i and t and then again for all
  -- i = 1,...,aux₁, we need to swap (k₁ + i and k₂ + i).
  (tm.toMultiTapeTM.with_tapes (h_le := by omega) (
    ((seq.map fun (t : Fin k₂) => (⟨t, by omega⟩ : Fin (k₂ + aux₂))) : (Vector (Fin (k₂ + aux₂)) k₁)) ++
    (((Vector.ofFn fun i => ⟨k₂ + i, by omega⟩) : (Vector (Fin (k₂ + aux₂)) aux₁))))).set_aux_tapes aux₂


namespace Routines


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
  (neq q s t (h_neq := h_neq) (h_neq' := h_neq') (h_neq'' := h_neq'')).eval_list tapes =
    Part.some (Function.update tapes t
      ((if (tapes q).head h_q_nonempty = (tapes s).head h_s_nonempty then
        []
      else
        [.one]) :: (tapes t))) := by
  simp [neq, h_q_nonempty, h_s_nonempty]

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

-- loop is a TM with k  tapes and 3 aux tapes.

-- TODO the main complication is how to use 'with_tapes', because it is supposed
-- to assign the aux tapes to some tapes that we know are not used for anything else.
-- So define a with_tapes function on MultiTapeTMWithAuxTapes

def loop' (i : Fin k) (tm : MultiTapeTM k (WithSep OneTwo)) :
    MultiTapeTMWithAuxTapes 3 k (WithSep OneTwo) :=
  let target : Fin (k + 3) := ⟨k, by omega⟩
  let counter : Fin (k + 3) := ⟨k.succ, by omega⟩
  let cond : Fin (k + 3) := ⟨k.succ.succ, by omega⟩
  (copy ⟨i, by omega⟩ target (h_neq := by grind) <;>
  push counter [] <;>
  neq target counter cond (by grind) (by grind) (by grind) <;>
  doWhile cond (
    pop cond <;>
    tm.extend (by omega) <;>
    succ counter <;>
    neq target counter cond (by grind) (by grind) (by grind)) <;>
  pop cond <;>
  pop counter <;>
  pop target).set_aux_tapes 3



@[simp]
theorem loop_eval_list {i : Fin k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {tapes : Fin (k + 3) → List (List OneTwo)}
  (h_tapes_i : tapes ⟨i, by omega⟩ ≠ []) :
  (loop i tm).eval_list tapes =
      ((Part.bind · tm.eval_list)^[dya_inv ((tapes ⟨i, by omega⟩).head h_tapes_i)]
        (Part.some (fun j => tapes (j.castLE (by omega))))).map fun tapes' =>
          fun j => if h : j.val < k then tapes' ⟨j, h⟩ else (tapes j) := by
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

-- Add 0 and 1 and store the result in 2.
public def add : MultiTapeTMWithAuxTapes 3 4 (WithSep OneTwo) :=
  copy 1 2 <;>
  loop 0 (succ 2)

@[simp]
lemma Function.update_update {α β : Type} [DecidableEq α] {f : α → β} {i : α} {x y : β} :
  Function.update (Function.update f i x) i y = Function.update f i y := by
  grind

@[simp]
public theorem add_eval_list {tapes : Fin 7 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 2)))) := by
  -- TODO this is weird, the second case, j ≠ 2 somehow has problems
  -- with the different Fin types.
  simp only [add, Fin.isValue, MultiTapeTM.seq_eval_list, ne_eq, h_nonempty₁, not_false_eq_true,
    copy_eval_list, Nat.succ_eq_add_one, Nat.reduceAdd, Part.bind_eq_bind, Part.bind_some,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta, Fin.reduceEq, Function.update_of_ne,
    h_nonempty₀, loop_eval_list, Fin.reduceCastLE, Function.update_self, reduceCtorEq, succ_iter,
    List.head_cons, List.tail_cons, Part.map_some, Part.some_inj]
  funext j
  by_cases hx : j = 2
  · simp [hx]
    grind
  · unfold Function.update
    simp only [Fin.isValue, eq_rec_constant, Fin.castLE_mk, Fin.eta, hx, ↓reduceDIte, dite_eq_ite,
      dite_eq_right_iff, ite_eq_right_iff]
    intro h h_eq
    have : (⟨↑j, h⟩ : Fin 4) = 2 := h_eq
    have : j = 2 := by
      ext
      simpa using Fin.val_eq_of_eq this
    contradiction

-- Add head of 0 to head of 1 (and store it in head of 1).
public def add_assign₀ : MultiTapeTM 7 (WithSep OneTwo) :=
  add <;>
  pop 1 <;>
  copy 2 1 <;>
  pop 2

public theorem add_assign₀_eval_list {tapes : Fin 7 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add_assign₀.eval_list tapes = .some
    (Function.update tapes 1 ((dya (dya_inv ((tapes 0).head h_nonempty₀) +
      dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 1).tail))) := by
  simp [add_assign₀, h_nonempty₀, h_nonempty₁]
  grind

public def add_assign {k : ℕ} (i j : Fin k) (h_neq : i ≠ j := by decide) :
    MultiTapeTM k (WithSep OneTwo) :=
  add_assign₀.with_tapes #v[i, j] (h_le := by omega)

-- Multiplies the heads of 0 and 1 and stores the result in 2.
public def mul : MultiTapeTM 7 (WithSep OneTwo) :=
  loop 0 (
    add_assigncopy 2 3 <;>
    loop 3 (add_assign <;> push 2 []))

end Routines

end Turing
