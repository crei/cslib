/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives

/-!
# Example: `fun (i, v, l) => l.set i v`
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

/-! ## 6. Worked example: `fun (i, v, l) => l.set i v`

Updating a list at an index is a fold that combines the two ideas of the previous examples: the
countdown of `ListIndex` decides *when* to write, and the in-order append of `ListMap` builds the
result. The accumulator is a triple — the countdown, the value to write (carried along unchanged,
because `step` sees only the accumulator and the current element), and the output produced so far.

As in `ListIndex` the counter is stored *offset by one*: `init` produces `i + 1` and the new value
is emitted exactly when the counter reads `1`. Truncated subtraction then pins the counter at `0`,
which the guard never matches again, so at most one position is overwritten. Past the end of the
list nothing fires at all, which is precisely the `l.set i v = l` behaviour of `List.set` for
out-of-range indices.

Appending with `acc ++ [·]` rather than consing keeps the output in order, so no final reverse is
needed; only the projection out of the triple remains, which is again `ComputableUpTo.comp`.

The accumulator is bounded by `A n = 2 * n + 6` rather than `n + O(1)`: the value `v` occurs twice
in it — once as the carried value and once inside the output list — and `v` can be as large as the
whole input. That is still linear, so the space bound is still linear.
-/

namespace ListUpdate

variable {α : Type}

/-- The list the update fold runs over: the list component of the input. -/
def updateList (p : ℕ × α × List α) : List α := p.2.2

/-- The initial accumulator: the index offset by one, the value to write, and an empty output. -/
def updateInit (p : ℕ × α × List α) : ℕ × α × List α := (p.1 + 1, p.2.1, [])

/-- One step of the update fold: count down, carry the value along, and append either the new
value (exactly when the counter reads `1`) or the element that was already there. -/
def updateStep (acc : ℕ × α × List α) (x : α) : ℕ × α × List α :=
  (acc.1 - 1, acc.2.1, acc.2.2 ++ [if acc.1 = 1 then acc.2.1 else x])

/-- The final projection: the output list is the third component of the accumulator. -/
def updateOut (acc : ℕ × α × List α) : List α := acc.2.2

/-- **List update as a fold**: run `updateStep` over the list and project the output out. -/
def updateFun (p : ℕ × α × List α) : List α :=
  updateOut (foldFun updateList updateInit updateStep p)

/-! ### Correctness of the fold -/

/-- Once the counter has reached `0` the guard never fires again, so the remaining elements are
copied across unchanged. -/
lemma foldl_zero (l : List α) (v : α) (out : List α) :
    l.foldl updateStep (0, v, out) = (0, v, out ++ l) := by
  induction l generalizing out with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    change xs.foldl updateStep (0, v, out ++ [if (0 : ℕ) = 1 then v else x])
      = (0, v, out ++ x :: xs)
    rw [ite_eq_right (by omega), ih (out ++ [x])]
    simp

/-- **The fold writes the new value at exactly the right position.** The counter starts offset by
one, so starting from `i + 1` the output is the input list with position `i` replaced. -/
lemma foldl_out (l : List α) (i : ℕ) (v : α) (out : List α) :
    (l.foldl updateStep (i + 1, v, out)).2.2 = out ++ l.set i v := by
  induction l generalizing i out with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases i with
    | zero =>
      change (xs.foldl updateStep (0 + 1 - 1, v, out ++ [if 0 + 1 = 1 then v else x])).2.2
        = out ++ (x :: xs).set 0 v
      rw [ite_eq_left rfl]
      change (xs.foldl updateStep (0, v, out ++ [v])).2.2 = out ++ (x :: xs).set 0 v
      rw [foldl_zero]
      simp
    | succ k =>
      change (xs.foldl updateStep (k + 1 + 1 - 1, v, out ++ [if k + 1 + 1 = 1 then v else x])).2.2
        = out ++ (x :: xs).set (k + 1) v
      rw [ite_eq_right (by omega), show k + 1 + 1 - 1 = k + 1 from by omega, ih k (out ++ [x])]
      simp

/-- **The fold computes `List.set`.** -/
lemma foldFun_out (p : ℕ × α × List α) :
    (foldFun updateList updateInit updateStep p).2.2 = p.2.2.set p.1 p.2.1 := by
  obtain ⟨i, v, l⟩ := p
  change (l.foldl updateStep (i + 1, v, [])).2.2 = l.set i v
  rw [foldl_out]
  simp

/-- **Correctness of `updateFun`.** -/
lemma updateFun_eq (p : ℕ × α × List α) : updateFun p = p.2.2.set p.1 p.2.1 :=
  foldFun_out p

/-! ### Size bookkeeping -/

/-- The counter never exceeds its initial value. -/
lemma foldl_fst_le (l : List α) (m : ℕ) (v : α) (out : List α) :
    (l.foldl updateStep (m, v, out)).1 ≤ m := by
  induction l generalizing m out with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    change (xs.foldl updateStep (m - 1, v, out ++ [if m = 1 then v else x])).1 ≤ m
    exact le_trans (ih _ _) (Nat.sub_le _ _)

/-- The value to be written is carried along unchanged. -/
lemma foldl_snd_fst (l : List α) (m : ℕ) (v : α) (out : List α) :
    (l.foldl updateStep (m, v, out)).2.1 = v := by
  induction l generalizing m out with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    change (xs.foldl updateStep (m - 1, v, out ++ [if m = 1 then v else x])).2.1 = v
    exact ih _ _

private lemma size_take_le [DataEncode α] (l : List α) (j : ℕ) :
    (DataEncode.encode (l.take j)).size ≤ (DataEncode.encode l).size := by
  have h := sum_map_take_le l (fun x => (DataEncode.encode x).size) j
  rw [DataEncode.size_list, DataEncode.size_list]
  omega

private lemma size_set_le [DataEncode α] (l : List α) (i : ℕ) (v : α) :
    (DataEncode.encode (l.set i v)).size
      ≤ (DataEncode.encode l).size + (DataEncode.encode v).size := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero =>
      rw [List.set_cons_zero, DataEncode.size_cons, DataEncode.size_cons]
      omega
    | succ k =>
      rw [List.set_cons_succ, DataEncode.size_cons, DataEncode.size_cons]
      have := ih k
      omega

private lemma size_triple [DataEncode α] (q : ℕ × α × List α) :
    (DataEncode.encode q).size
      = (DataEncode.encode q.1).size + (DataEncode.encode q.2.1).size
        + (DataEncode.encode q.2.2).size + 4 := by
  have h1 : (DataEncode.encode q).size
      = (DataEncode.encode q.1).size + (DataEncode.encode q.2).size + 2 :=
    DataEncode.size_pair _ _
  have h2 : (DataEncode.encode q.2).size
      = (DataEncode.encode q.2.1).size + (DataEncode.encode q.2.2).size + 2 :=
    DataEncode.size_pair _ _
  omega

private lemma accSizeCore [DataEncode α] (l : List α) (i j : ℕ) (v : α) :
    (DataEncode.encode ((l.take j).foldl updateStep (i + 1, v, []))).size
      ≤ (DataEncode.encode i).size + 2 * (DataEncode.encode v).size
        + (DataEncode.encode l).size + 10 := by
  have hsplit := size_triple ((l.take j).foldl updateStep (i + 1, v, []))
  have h1 : (DataEncode.encode ((l.take j).foldl updateStep (i + 1, v, [])).1).size
      ≤ (DataEncode.encode i).size + 6 :=
    le_trans (DataEncode.size_nat_mono (foldl_fst_le _ _ _ _)) (DataEncode.size_nat_succ i)
  have h2 : (DataEncode.encode ((l.take j).foldl updateStep (i + 1, v, [])).2.1).size
      = (DataEncode.encode v).size := by rw [foldl_snd_fst]
  have h3 : ((l.take j).foldl updateStep (i + 1, v, [])).2.2 = (l.take j).set i v := by
    rw [foldl_out]
    simp
  have h4 : (DataEncode.encode ((l.take j).foldl updateStep (i + 1, v, [])).2.2).size
      ≤ (DataEncode.encode l).size + (DataEncode.encode v).size := by
    rw [h3]
    exact le_trans (size_set_le _ _ _) (Nat.add_le_add_right (size_take_le l j) _)
  omega

/-- The list folded over is a component of the input, so it is no bigger: `S n = n`. -/
lemma listSize [DataEncode α] (p : ℕ × α × List α) :
    (DataEncode.encode (updateList p)).size ≤ (DataEncode.encode p).size := by
  obtain ⟨i, v, l⟩ := p
  have hp := size_triple ((i, v, l) : ℕ × α × List α)
  change (DataEncode.encode l).size ≤ (DataEncode.encode ((i, v, l) : ℕ × α × List α)).size
  simp only at hp
  omega

/-- **The accumulator stays linear in the input: `A n = 2 * n + 6`.**

The counter is at most `i + 1`, whose encoding costs at most six more than that of `i`; the
carried value is `v` itself; and the output so far is a prefix of the list with one entry replaced
by `v`, hence at most the list plus one more copy of `v`. It is that second copy of `v` — which
may be as large as the whole input — that forces the factor of two. -/
lemma accSize [DataEncode α] (p : ℕ × α × List α) (j : ℕ) :
    (DataEncode.encode (foldAcc updateList updateInit updateStep p j)).size
      ≤ 2 * (DataEncode.encode p).size + 6 := by
  obtain ⟨i, v, l⟩ := p
  have hacc : foldAcc updateList updateInit updateStep (i, v, l) j
      = (l.take j).foldl updateStep (i + 1, v, []) := rfl
  have hp := size_triple ((i, v, l) : ℕ × α × List α)
  have hc := accSizeCore l i j v
  simp only at hp
  rw [hacc]
  omega

/-- The output of the fold is an accumulator, so it obeys the same bound: `S_f n = 2 * n + 6`. -/
lemma foldOutSize [DataEncode α] (p : ℕ × α × List α) :
    (DataEncode.encode (foldFun updateList updateInit updateStep p)).size
      ≤ 2 * (DataEncode.encode p).size + 6 :=
  foldFun_size_le (fun n => 2 * n + 6) accSize p

/-! ### The complexity statement -/

/--
**Updating a list at an index runs in polynomial time and linear space.**

Given that the three ingredients of the fold — taking the list component, building the initial
accumulator, and one countdown-and-append step — as well as the final projection are each
computable in polynomial time and linear space, so is `fun (i, v, l) => l.set i v`.

Unfolded, the composed bounds are time `3n² + 12n + 6` and space `12n + 26` in the encoded input
size `n`, which `ComputableUpTo.absorb` restates as "polynomial, linear".
-/
theorem listUpdate_polyTimeLinSpace [DataEncode α]
    (h_list : PolyTimeLinSpace (updateList (α := α)))
    (h_init : PolyTimeLinSpace (updateInit (α := α)))
    (h_step : PolyTimeLinSpace (Function.uncurry (updateStep (α := α))))
    (h_out : PolyTimeLinSpace (updateOut (α := α))) :
    PolyTimeLinSpace (fun p : ℕ × α × List α => p.2.2.set p.1 p.2.1) := by
  -- The fold itself: `S n = n`, `A n = 2n + 6`, hence step arguments of size at most `3n + 8`.
  have h_fold := foldl_computableUpTo updateList updateInit updateStep
    (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n)
    (fun n => 2 * n + 6) (fun n => n)
    h_list h_init h_step monotone_id monotone_id listSize accSize
  -- Project the output list out of the accumulator.
  have h_comp := ComputableUpTo.comp (S_f := fun n => 2 * n + 6) h_fold h_out
    monotone_id monotone_id (foldOutSize (α := α))
  have h_eq : (updateOut ∘ foldFun updateList updateInit updateStep)
      = fun p : ℕ × α × List α => p.2.2.set p.1 p.2.1 := funext fun p => updateFun_eq p
  rw [h_eq] at h_comp
  -- Absorb the composed closed form into "polynomial time, linear space":
  -- time `3n² + 12n + 6 ≤ 3 * (n + n + 2)²`, space `12n + 26 ≤ 26 * (n + 1)`.
  refine h_comp.absorb 3 2 26 (fun n => ?_) (fun n => ?_)
  · nlinarith [sq_nonneg n]
  · omega

/-! ### The same result in the `Bounds` algebra -/

/-- Taking the list component is two projections. -/
def listBounds [DataEncode α] : Bounds (updateList (α := α)) :=
  Bounds.congr
    (Bounds.comp (Bounds.snd : Bounds (Prod.snd : α × List α → List α))
      (Bounds.snd : Bounds (Prod.snd : ℕ × α × List α → α × List α))) rfl

/-- Projecting the output list out of the accumulator is the same two projections. -/
def outBounds [DataEncode α] : Bounds (updateOut (α := α)) :=
  listBounds

/-- **List update in the `Bounds` algebra.**

The same result as `listUpdate_polyTimeLinSpace`, built compositionally: the two projections are
primitives, so only the initial accumulator and the step have to be assumed, and the accumulator
bound `A n = 2 * n + 6` is the single creative input to `Bounds.fold`. -/
def updateBounds [DataEncode α] (hinit : Bounds (updateInit (α := α)))
    (hstep : Bounds (Function.uncurry (updateStep (α := α)))) :
    Bounds (fun p : ℕ × α × List α => p.2.2.set p.1 p.2.1) :=
  Bounds.congr
    (Bounds.comp outBounds
      (Bounds.fold listBounds hinit hstep (fun n => 2 * n + 6)
        (fun _ _ h => Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 6) accSize))
    (funext fun p => updateFun_eq p)

end ListUpdate

end MultiTapeTM

end Turing
