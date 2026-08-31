/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives

/-!
# Example: `List.map`
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

/-! ## 1. `List.map`

`List.map f l = l.foldl (fun acc x => acc ++ [f x]) []`, so the list is the input itself, the
initial accumulator is empty, and the accumulator at any point is a prefix of the result.

The hypothesis that matters is `h_out`: each output element is at most a *constant factor* larger
than its input. That makes the accumulator linear in the input — the sum of the output sizes is
bounded by `c` times the sum of the input sizes, which is the encoded size of the input list. A
merely polynomial per-element bound would give a polynomial-space, not linear-space, result.
-/

namespace ListMap

variable {α β : Type}

/-- The step of `List.map` as a fold: append the image of the next element. -/
def mapStep (f : α → β) (acc : List β) (x : α) : List β := acc ++ [f x]

/-- The initial accumulator of the `List.map` fold. -/
def mapInit (_ : List α) : List β := []

lemma foldl_mapStep (f : α → β) (l : List α) (acc : List β) :
    l.foldl (mapStep f) acc = acc ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp [mapStep, ih]

/-- **The fold computes `List.map`.** -/
lemma foldFun_map (f : α → β) (l : List α) :
    foldFun (id : List α → List α) mapInit (mapStep f) l = l.map f := by
  simpa [foldFun, mapInit] using foldl_mapStep f l []

lemma foldAcc_map (f : α → β) (l : List α) (j : ℕ) :
    foldAcc (id : List α → List α) mapInit (mapStep f) l j = (l.take j).map f := by
  simpa [foldAcc, mapInit] using foldl_mapStep f (l.take j) []

variable [DataEncode α] [DataEncode β]

omit [DataEncode β] in
lemma mapListSize (l : List α) :
    (DataEncode.encode (id l)).size ≤ (DataEncode.encode l).size := le_refl _

/-- **The accumulator stays linear**: it is a prefix of the output, and each output element is at
most `c` times its input element, so the whole accumulator is at most `c` times the input list. -/
lemma mapAccSize (f : α → β) (c : ℕ)
    (h_out : ∀ x : α, (DataEncode.encode (f x)).size ≤ c * (DataEncode.encode x).size)
    (l : List α) (j : ℕ) :
    (DataEncode.encode (foldAcc (id : List α → List α) mapInit (mapStep f) l j)).size
      ≤ 2 + c * (DataEncode.encode l).size := by
  rw [foldAcc_map, DataEncode.size_list, List.map_map]
  have h1 : ((l.take j).map ((fun y => (DataEncode.encode y).size) ∘ f)).sum
      ≤ (l.map ((fun y => (DataEncode.encode y).size) ∘ f)).sum := sum_map_take_le _ _ _
  have h2 : (l.map ((fun y => (DataEncode.encode y).size) ∘ f)).sum
      ≤ c * (l.map fun x => (DataEncode.encode x).size).sum :=
    sum_map_le_of_le l _ _ c fun x _ => h_out x
  have h3 : c * (l.map fun x => (DataEncode.encode x).size).sum
      ≤ c * (DataEncode.encode l).size :=
    Nat.mul_le_mul_left c (by rw [DataEncode.size_list]; omega)
  omega

/--
**`List.map f` runs in polynomial time and linear space**, provided the fold's ingredients do and
each output element is at most a constant factor larger than its input.

Unlike `ListIndex`, no final projection is needed: the accumulator *is* the result, so this
follows from `foldl_computableUpTo` alone.
-/
theorem map_polyTimeLinSpace (f : α → β) (c : ℕ)
    (h_list : PolyTimeLinSpace (id : List α → List α))
    (h_init : PolyTimeLinSpace (mapInit : List α → List β))
    (h_step : PolyTimeLinSpace (Function.uncurry (mapStep f)))
    (h_out : ∀ x : α, (DataEncode.encode (f x)).size ≤ c * (DataEncode.encode x).size) :
    PolyTimeLinSpace (fun l : List α => l.map f) := by
  have h_fold := foldl_computableUpTo (id : List α → List α) mapInit (mapStep f)
    (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n)
    (fun n => 2 + c * n) (fun n => n)
    h_list h_init h_step monotone_id monotone_id mapListSize (mapAccSize f c h_out)
  have h_eq : foldFun (id : List α → List α) mapInit (mapStep f) = fun l : List α => l.map f :=
    funext (foldFun_map f)
  rw [h_eq] at h_fold
  refine h_fold.absorb (c + 8) 2 (2 * c + 6) (fun n => ?_) (fun n => ?_)
  · have hexp : (n + n + 2) ^ 2 = 4 * n * n + 8 * n + 4 := by ring
    rw [hexp]
    nlinarith
  · nlinarith

/-- **`List.map` in the `Bounds` algebra.**

The same result as `map_polyTimeLinSpace`, built compositionally instead of by discharging a list
of hypotheses. Compare the call sites: the monotonicity side conditions (`monotone_id monotone_id`
above) have vanished, because monotonicity travels inside the certificates, and the output-size
bound is a *field* of `Bounds.fold`'s result rather than an implicit argument that has to be
supplied by hand.

The bounds it computes are, with `hstep` the step's certificate and `A n = 2 + c * n`:
`time n = (n + 2) + 4 + n * hstep.time (A n + n + 2)` and
`space n = hstep.space (A n + n + 2) + A n + n`. -/
def mapBounds (f : α → β) (c : ℕ)
    (hstep : Bounds (Function.uncurry (mapStep f)))
    (h_out : ∀ x : α, (DataEncode.encode (f x)).size ≤ c * (DataEncode.encode x).size) :
    Bounds (fun l : List α => l.map f) :=
  (Bounds.fold (Bounds.id : Bounds (id : List α → List α))
      (Bounds.const [] : Bounds (mapInit : List α → List β)) hstep
      (fun n => 2 + c * n)
      (by intro x y h; exact Nat.add_le_add_left (Nat.mul_le_mul_left c h) 2)
      (mapAccSize f c h_out)).congr (funext (foldFun_map f))

end ListMap

end MultiTapeTM

end Turing
