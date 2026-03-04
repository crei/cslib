/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding

public import Mathlib.Order.Monotone.Defs

namespace Turing

namespace Routines

variable {k : ℕ}

/--
A Turing machine that executes `tm` a number of times as given by the first word on tape `i`.
If tape `i` is empty, do not execute the TM.
Note that the iteration counter is not directly available to `tm`. -/
public def loop (i : ℕ) {h_i : i < k}
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
public theorem loop_eval_list {i : ℕ} {h_i : i < k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {tapes : Fin (k + 3) → List (List OneTwo)} :
  (loop i tm (h_i := h_i)).eval_list tapes =
      (((Part.bind · tm.eval_list)^[dya_inv ((tapes ⟨i, by omega⟩).headD [])]
        (Part.some (tapes_take tapes k (by omega))))).map
          fun tapes' => tapes_extend_by tapes' tapes := by
  sorry

@[simp]
public theorem loop_halts_of_halts
  {i : ℕ} {h_i : i < k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  (h_halts : ∀ tapes, tm.haltsOn tapes) :
  ∀ tapes, (loop i tm (h_i := h_i)).haltsOn tapes := by
  sorry

public noncomputable def space_at_iter {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  (h_halts : ∀ tapes, tm.haltsOn tapes)
  (iteration : ℕ)
  (tapes : Fin k → List (List OneTwo)) : Fin k → ℕ :=
  match iteration with
  | 0 => spaceUsed_init tapes
  | Nat.succ iter => fun i => max
      (space_at_iter h_halts iter tapes i)
      (tm.spaceUsed_list
        ((fun tapes => (tm.eval_list tapes).get (by sorry))^[iter] tapes) h_halts i)

public theorem space_at_iter_of_mono {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  (h_halts : ∀ tapes, tm.haltsOn tapes)
  (i : Fin k)
  (h_mono_step : ∀ tapes, tm.spaceUsed_list tapes h_halts i ≤
     tm.spaceUsed_list ((tm.eval_list tapes).get sorry) h_halts i)
  (iteration : ℕ)
  (tapes : Fin k → List (List OneTwo)) :
  space_at_iter h_halts iteration.succ tapes i = tm.spaceUsed_list
      ((fun tapes => (tm.eval_list tapes).get sorry)^[iteration] tapes) h_halts i := by
  induction iteration generalizing tapes with
  | zero => simp [space_at_iter]
  | succ iter ih =>
    unfold space_at_iter
    rw [ih]
    simp only [Function.iterate_succ', Function.comp_apply, sup_eq_right, h_mono_step]

@[simp]
public theorem space_at_iter_of_constant {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {h_halts : ∀ tapes, tm.haltsOn tapes}
  {i : Fin k}
  (h_constant_space : ∀ tapes, tm.spaceUsed_list tapes h_halts i = spaceUsed_init tapes i)
  (h_constant_semantics : ∀ tapes, ((tm.eval_list tapes).map fun t => t i) = .some (tapes i))
  {iteration : ℕ}
  {tapes : Fin k → List (List OneTwo)} :
  space_at_iter h_halts iteration tapes i = spaceUsed_init tapes i := by
  induction iteration generalizing tapes with
  | zero => simp [space_at_iter]
  | succ iter ih =>
    unfold space_at_iter
    have h_id : (fun tapes : Fin k → List (List OneTwo) => tapes) = id := rfl
    rw [ih]
    simp [h_constant_space, h_constant_semantics, h_id, Function.iterate_id]
    sorry

-- TODO the following is probably not true for aux tapes. There we might need a bound.

public noncomputable def output_length {k : ℕ}
  (tm : MultiTapeTM k (WithSep OneTwo))
  (tapes : Fin k → List (List OneTwo))
  (i : Fin k) : Part ℕ :=
  (tm.eval_list tapes).map fun t => (listToString (t i)).length

public lemma output_length_value {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  (tapes : Fin k → List (List OneTwo))
  (i : Fin k) :
  output_length tm tapes i = (tm.eval_list tapes).map fun t => (listToString (t i)).length := by
  simp [output_length]

public def output_length_mono {k : ℕ}
  (tm : MultiTapeTM k (WithSep OneTwo))
  (i : Fin k) : Prop :=
  ∀ tapes, ((output_length tm tapes i).map
    fun len => len ≥ (listToString (tapes i)).length) = .some true

public lemma output_length_mono_iff {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {i : Fin k} :
  output_length_mono tm i ↔ ∀ tapes, (output_length tm tapes i).map
    fun len => len ≥ (listToString (tapes i)).length = .some true := by
  simp [output_length_mono]

public def space_use_is_output_length {k : ℕ}
  (tm : MultiTapeTM k (WithSep OneTwo))
  (i : Fin k) : Prop :=
  ∀ tapes, (.some (tm.spaceUsed_list tapes sorry i) = output_length tm tapes i)

public lemma space_use_is_output_length_iff {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {i : Fin k} :
  space_use_is_output_length tm i ↔
    ∀ tapes, (.some (tm.spaceUsed_list tapes sorry i) = output_length tm tapes i) := by
  simp [space_use_is_output_length]

-- TODO this still does not work, it only works if it only depends on the length.
public def space_use_mono {k : ℕ}
  (tm : MultiTapeTM k (WithSep OneTwo))
  (i : Fin k) : Prop :=
  ∀ tapes, (listToString (tapes i)).length ≤ (tm.spaceUsed_list tapes sorry i)

public lemma space_use_mono_iff {k : ℕ}
  (tm : MultiTapeTM k (WithSep OneTwo))
  (i : Fin k) :
  space_use_mono tm i ↔
    ∀ tapes, (listToString (tapes i)).length ≤ (tm.spaceUsed_list tapes sorry i) := by
  simp [space_use_mono]

@[simp]
public lemma space_at_iter_of_mono' {k : ℕ}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  (h_halts : ∀ tapes, tm.haltsOn tapes)
  (i : Fin k)
  -- The machine's output on tape i is at least as large as the input.
  (h_mono_output : output_length_mono tm i)
  -- The machine's space use is the same as the output length.
  (h_mono_space : space_use_is_output_length tm i)
  (iteration : ℕ)
  (tapes : Fin k → List (List OneTwo)) :
  space_at_iter h_halts iteration tapes i =
    (((Part.bind · tm.eval_list)^[iteration] tapes).get sorry i).length := by
  sorry

@[simp]
public theorem loop_space_list {i : ℕ} {h_i : i < k}
  {tm : MultiTapeTM k (WithSep OneTwo)}
  {h_halts : ∀ tapes, tm.haltsOn tapes}
  {tapes : Fin (k + 3) → List (List OneTwo)} :
  (loop i tm (h_i := h_i)).spaceUsed_list tapes sorry = (fun j : Fin (k + 3) =>
      (if h : j < k then
        space_at_iter h_halts
          (dya_inv ((tapes ⟨i, by omega⟩).headD [])) (fun i => tapes ⟨i, sorry⟩) ⟨j, h⟩
      else
        ((tapes ⟨i, by omega⟩).headD []).length + 1 + (spaceUsed_init tapes j))) := by
  sorry

end Routines
end Turing
