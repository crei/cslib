/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Bounds

/-!
# Complexity of `List.foldl`

The main theorem of the development, plus its `Bounds` packaging.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

/-! ## 4. Complexity of `foldl` -/

variable {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]

/-- The accumulator reached after `j` steps of folding `step` over `list a`, starting from
`init a`. The point of naming it is that the hypothesis of `foldl_computableUpTo` has to bound
*all* intermediate accumulators, not just the final result. -/
def foldAcc (list : α → List β) (init : α → γ) (step : γ → β → γ) (a : α) (j : ℕ) : γ :=
  ((list a).take j).foldl step (init a)

/-- The function computed by folding `step` over `list`, starting from `init`. -/
def foldFun (list : α → List β) (init : α → γ) (step : γ → β → γ) (a : α) : γ :=
  (list a).foldl step (init a)

omit [DataEncode α] [DataEncode β] [DataEncode γ] in
/-- The final accumulator is the value of the fold. -/
lemma foldAcc_length (list : α → List β) (init : α → γ) (step : γ → β → γ) (a : α) :
    foldAcc list init step a (list a).length = foldFun list init step a := by
  simp [foldAcc, foldFun]

omit [DataEncode β] in
/-- An accumulator bound is automatically a bound on the fold's *output*, since the output is the
accumulator after the last element. Every example needs this, and so does `Bounds.fold`. -/
lemma foldFun_size_le {list : α → List β} {init : α → γ} {step : γ → β → γ} (A : ℕ → ℕ)
    (hA : ∀ (a : α) (j : ℕ),
      (DataEncode.encode (foldAcc list init step a j)).size ≤ A (DataEncode.encode a).size)
    (a : α) :
    (DataEncode.encode (foldFun list init step a)).size ≤ A (DataEncode.encode a).size := by
  rw [← foldAcc_length list init step a]
  exact hA a _

/--
**Complexity of `foldl` on multi-tape Turing machines.**

Assume that

* `list : α → List β` is computable in time `t_l` and space `s_l`,
* `init : α → γ` is computable in time `t_i` and space `s_i`,
* `step : γ → β → γ`, seen as a function of the pair `(accumulator, element)`, is computable in
  time `t_s` and space `s_s`, both monotone,
* the encoded list `list a` has size at most `S n`, and
* every intermediate accumulator `foldAcc list init step a j` has encoded size at most `A n`,

where `n` is the encoded size of the input `a`. Then `fun a => (list a).foldl step (init a)` is
computable by some multi-tape Turing machine in

* time  `t_l n + t_i n + S n * t_s (A n + S n + 2)` — the list and the initial accumulator are
  produced once, and then at most `S n` iterations each cost one `step` on an argument of size at
  most `A n + S n + 2`;
* space `s_l n + s_i n + s_s (A n + S n + 2) + A n + S n` — the list and the current accumulator
  have to be kept, plus the workspace of a single `step` invocation, which is reused across
  iterations.

Both up to the slack of `ComputableUpTo`: a polynomial in time, a constant factor in space.
-/
theorem foldl_computableUpTo
    (list : α → List β) (init : α → γ) (step : γ → β → γ)
    (t_l s_l t_i s_i t_s s_s A S : ℕ → ℕ)
    (h_list : ComputableUpTo list t_l s_l)
    (h_init : ComputableUpTo init t_i s_i)
    (h_step : ComputableUpTo (Function.uncurry step) t_s s_s)
    (h_t_s : Monotone t_s) (h_s_s : Monotone s_s)
    (h_listSize : ∀ a : α,
      (DataEncode.encode (list a)).size ≤ S (DataEncode.encode a).size)
    (h_accSize : ∀ (a : α) (j : ℕ),
      (DataEncode.encode (foldAcc list init step a j)).size ≤ A (DataEncode.encode a).size) :
    ComputableUpTo (foldFun list init step)
      (fun n => t_l n + t_i n + S n * t_s (A n + S n + 2))
      (fun n => s_l n + s_i n + s_s (A n + S n + 2) + A n + S n) := by
  sorry

/-- **`foldl` as a `Bounds` combinator.**

Every other combinator derives its bounds from those of its parts. `fold` is the only one that
needs something a human has to supply: `A`, a uniform bound on the encoded size of the
intermediate accumulators. Making that the single explicit argument is the point of the
packaging — it isolates the one creative step of a fold complexity argument. -/
def Bounds.fold {list : α → List β} {init : α → γ} {step : γ → β → γ}
    (hl : Bounds list) (hi : Bounds init) (hs : Bounds (Function.uncurry step))
    (A : ℕ → ℕ) (hA_mono : Monotone A)
    (hA : ∀ (a : α) (j : ℕ),
      (DataEncode.encode (foldAcc list init step a j)).size ≤ A (DataEncode.encode a).size) :
    Bounds (foldFun list init step) where
  time n := hl.time n + hi.time n + hl.outSize n * hs.time (A n + hl.outSize n + 2)
  space n := hl.space n + hi.space n + hs.space (A n + hl.outSize n + 2) + A n + hl.outSize n
  outSize := A
  time_mono := by
    intro a b h
    have h1 := hl.time_mono h
    have h2 := hi.time_mono h
    have h3 := hl.outSize_mono h
    have h4 : hs.time (A a + hl.outSize a + 2) ≤ hs.time (A b + hl.outSize b + 2) :=
      hs.time_mono (by have := hA_mono h; omega)
    exact Nat.add_le_add (Nat.add_le_add h1 h2) (Nat.mul_le_mul h3 h4)
  space_mono := fun _ _ h =>
    Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (hl.space_mono h) (hi.space_mono h))
          (hs.space_mono (Nat.add_le_add
            (Nat.add_le_add (hA_mono h) (hl.outSize_mono h)) (le_refl 2))))
        (hA_mono h))
      (hl.outSize_mono h)
  outSize_mono := hA_mono
  computes := sorry
  out_le := foldFun_size_le A hA

/-- A `foldl` whose step ignores the element is iteration: the list only supplies a trip count.
This is how a step *budget* on the input turns into a bounded run. -/
lemma foldl_const_iterate {β γ : Type} (f : γ → γ) (l : List β) (c : γ) :
    l.foldl (fun x _ => f x) c = f^[l.length] c := by
  induction l generalizing c with
  | nil => simp
  | cons _ l ih => simp [ih, Function.iterate_succ_apply]

end MultiTapeTM

end Turing
