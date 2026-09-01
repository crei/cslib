/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold

/-!
# Example: `fun (i, l) => l[i]?`
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

/-! ## 5. Worked example: `fun (i, l) => l[i]?`

Indexing is a fold: walk the list carrying a countdown and the element found so far.

The counter is stored *offset by one* — `init` produces `i + 1`, and the element is picked up when
the counter reads `1`. That offset is what makes the fold stop writing: truncated subtraction pins
the counter at `0`, which the guard never matches again, so later elements cannot overwrite the
answer. Storing `i` itself and grabbing at `0` would re-grab on every subsequent element.

The final accumulator is a pair, so the answer is extracted with `Prod.snd`; that is what forces
`ComputableUpTo.comp` into the picture. It is worth noting that the fold theorem *alone* is not
enough to state a complexity result for a function as simple as list indexing — a composition
principle is needed as well.
-/

namespace ListIndex

variable {α : Type}

/-- The list the indexing fold runs over: the list component of the input. -/
def listFn (p : ℕ × List α) : List α := p.2

/-- The initial accumulator: the index, offset by one, and "nothing found yet". -/
def initFn (p : ℕ × List α) : ℕ × Option α := (p.1 + 1, none)

/-- One step of the indexing fold: count down, and pick up the element exactly when the counter
reads `1`. -/
def stepFn (acc : ℕ × Option α) (x : α) : ℕ × Option α :=
  (acc.1 - 1, if acc.1 = 1 then some x else acc.2)

/-! ### Correctness of the fold -/

/-- Once the counter has reached `0` the accumulator is frozen: truncated subtraction keeps it at
`0`, and the guard `acc.1 = 1` never fires again. -/
lemma foldl_zero (l : List α) (r : Option α) :
    l.foldl stepFn (0, r) = (0, r) := by
  induction l generalizing r with
  | nil => rfl
  | cons x xs ih => simpa [stepFn] using ih r

/-- Past the end of the list the fold returns the accumulator it started with. -/
lemma foldl_snd_of_ge (l : List α) (i : ℕ) (r : Option α) (h : l.length ≤ i) :
    (l.foldl stepFn (i + 1, r)).2 = r := by
  induction l generalizing i r with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons] at h
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [List.foldl_cons]
    change (xs.foldl stepFn (k + 1 + 1 - 1, if k + 1 + 1 = 1 then some x else r)).2 = r
    rw [ite_eq_right (by omega), show k + 1 + 1 - 1 = k + 1 from by omega]
    exact ih k r (by omega)

/-- Within the list the fold returns the element at the index. -/
lemma foldl_snd_of_lt (l : List α) (i : ℕ) (r : Option α) (h : i < l.length) :
    (l.foldl stepFn (i + 1, r)).2 = some l[i] := by
  induction l generalizing i r with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.length_cons] at h
    cases i with
    | zero =>
      rw [List.foldl_cons]
      change (xs.foldl stepFn (0 + 1 - 1, if 0 + 1 = 1 then some x else r)).2 = some (x :: xs)[0]
      rw [ite_eq_left rfl]
      simp [foldl_zero]
    | succ k =>
      rw [List.foldl_cons]
      change (xs.foldl stepFn (k + 1 + 1 - 1, if k + 1 + 1 = 1 then some x else r)).2
        = some (x :: xs)[k + 1]
      rw [ite_eq_right (by omega), show k + 1 + 1 - 1 = k + 1 from by omega,
        List.getElem_cons_succ]
      exact ih k r (by omega)

/-- **The fold computes list indexing.** -/
lemma foldFun_snd (p : ℕ × List α) :
    (foldFun listFn initFn stepFn p).2 = p.2[p.1]? := by
  obtain ⟨i, l⟩ := p
  change (l.foldl stepFn (i + 1, none)).2 = l[i]?
  by_cases h : i < l.length
  · rw [foldl_snd_of_lt l i none h, List.getElem?_eq_getElem h]
  · rw [foldl_snd_of_ge l i none (by omega), List.getElem?_eq_none (by omega)]

/-! ### Size bookkeeping -/

/-- The counter never exceeds its initial value. -/
lemma foldl_fst_le (l : List α) (m : ℕ) (r : Option α) :
    (l.foldl stepFn (m, r)).1 ≤ m := by
  induction l generalizing m r with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, stepFn]
    exact le_trans (ih _ _) (Nat.sub_le _ _)

/-- The "found so far" component is either the one we started with or an element of the list. -/
lemma foldl_snd_mem (l : List α) (m : ℕ) (r : Option α) :
    (l.foldl stepFn (m, r)).2 = r ∨ ∃ x ∈ l, (l.foldl stepFn (m, r)).2 = some x := by
  induction l generalizing m r with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, stepFn]
    rcases ih (m - 1) (if m = 1 then some x else r) with h | ⟨y, hy, hy2⟩
    · rw [h]
      by_cases hm : m = 1
      · exact Or.inr ⟨x, by simp, by simp [hm]⟩
      · exact Or.inl (by simp [hm])
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hy2⟩

/-- The list folded over is a component of the input, so it is no bigger: `S n = n`. -/
lemma listSize [DataEncode α] (p : ℕ × List α) :
    (DataEncode.encode (listFn p)).size ≤ (DataEncode.encode p).size := by
  obtain ⟨i, l⟩ := p
  rw [DataEncode.size_pair]
  change (DataEncode.encode l).size ≤ _
  omega

/-- **The accumulator stays linear in the input: `A n = n + 8`.**

The counter is at most `i + 1`, whose encoding costs at most six more than that of `i` (this is
where size-monotonicity of the `ℕ` encoding is used); the element found so far is either `none` or
a subtree of the encoded list. -/
lemma accSize [DataEncode α] (p : ℕ × List α) (j : ℕ) :
    (DataEncode.encode (foldAcc listFn initFn stepFn p j)).size
      ≤ (DataEncode.encode p).size + 8 := by
  obtain ⟨i, l⟩ := p
  have hacc : foldAcc listFn initFn stepFn (i, l) j
      = (l.take j).foldl stepFn (i + 1, none) := rfl
  -- the counter component
  have h1 : ((l.take j).foldl stepFn (i + 1, none)).1 ≤ i + 1 := foldl_fst_le _ _ _
  have h1' : (DataEncode.encode ((l.take j).foldl stepFn (i + 1, none)).1).size
      ≤ (DataEncode.encode i).size + 6 :=
    le_trans (DataEncode.size_nat_mono h1) (DataEncode.size_nat_succ i)
  -- the "found so far" component
  have h2 : (DataEncode.encode ((l.take j).foldl stepFn (i + 1, none)).2).size
      ≤ (DataEncode.encode l).size + 2 := by
    rcases foldl_snd_mem (l.take j) (i + 1) none with h | ⟨x, hx, hx2⟩
    · rw [h, DataEncode.size_none]
      omega
    · rw [hx2, DataEncode.size_some]
      have := DataEncode.size_mem_le (List.mem_of_mem_take hx)
      omega
  -- split the encoded pair (uses eta for structures)
  have hsplit : (DataEncode.encode ((l.take j).foldl stepFn (i + 1, none))).size
      = (DataEncode.encode ((l.take j).foldl stepFn (i + 1, none)).1).size
        + (DataEncode.encode ((l.take j).foldl stepFn (i + 1, none)).2).size + 2 :=
    DataEncode.size_pair _ _
  rw [hacc, hsplit, DataEncode.size_pair]
  omega

/-- The output of the fold is an accumulator, so it obeys the same bound: `S_f n = n + 8`. -/
lemma foldOutSize [DataEncode α] (p : ℕ × List α) :
    (DataEncode.encode (foldFun listFn initFn stepFn p)).size
      ≤ (DataEncode.encode p).size + 8 :=
  foldFun_size_le (fun n => n + 8) accSize p

/-! ### The complexity statement -/

/--
**Indexing into a list runs in polynomial time and linear space.**

Given that the three ingredients of the fold — taking the list component, building the initial
accumulator, and one countdown step — as well as the final projection are each computable in
polynomial time and linear space, so is `fun (i, l) => l[i]?`.

Unfolded, the composed bounds are time `2n² + 13n + 8` and space `8n + 34` in the encoded input
size `n`, which `ComputableUpTo.absorb` restates as "polynomial, linear". The quadratic time is
not an artefact of the slack: the fold really does rescan the accumulator once per element.
-/
theorem listIndex_polyTimeLinSpace [DataEncode α]
    (h_list : PolyTimeLinSpace (listFn (α := α)))
    (h_init : PolyTimeLinSpace (initFn (α := α)))
    (h_step : PolyTimeLinSpace (Function.uncurry (stepFn (α := α))))
    (h_snd : PolyTimeLinSpace (Prod.snd : ℕ × Option α → Option α)) :
    PolyTimeLinSpace (fun p : ℕ × List α => p.2[p.1]?) := by
  -- The fold itself: `S n = n`, `A n = n + 8`, hence step arguments of size at most `2n + 10`.
  have h_fold := foldl_computableUpTo listFn initFn stepFn
    (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n)
    (fun n => n + 8) (fun n => n)
    h_list h_init h_step monotone_id monotone_id listSize accSize
  -- Project the answer out of the accumulator.
  have h_comp := ComputableUpTo.comp (S_f := fun n => n + 8) h_fold h_snd
    monotone_id monotone_id (foldOutSize (α := α))
  have h_eq : (Prod.snd ∘ foldFun listFn initFn stepFn) = fun p : ℕ × List α => p.2[p.1]? :=
    funext fun p => foldFun_snd p
  rw [h_eq] at h_comp
  -- Absorb the composed closed form into "polynomial time, linear space":
  -- time  `2n² + 13n + 8 ≤ 2 * (n + n + 2)²`, space `8n + 34 ≤ 34 * (n + 1)`.
  refine h_comp.absorb 2 2 34 (fun n => ?_) (fun n => ?_)
  · nlinarith [sq_nonneg n]
  · omega

end ListIndex

end MultiTapeTM

end Turing
