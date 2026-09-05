/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Ite
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Loop

/-!
# While combinator

This file defines the partial function computed by a `while` loop

```
while cond a do a := step a
return a
```

and gives two characterisations of it. It is the version of `loopFunction` with an explicit loop
condition; the complexity result is derived from the one for `loopFunction` by fusing the condition
and the body into a single function.

## Main definitions

* `Turing.MultiTapeTM.whileFunction`: the partial function computed by the loop, the `loopFunction`
  of the fused body. It is undefined on the inputs for which the loop diverges.
* `Turing.MultiTapeTM.WhileRel`: the graph of the loop, defined inductively.

## Main results

* `Turing.MultiTapeTM.mem_whileFunction`: `whileFunction` is characterised by `WhileRel`.
* `Turing.MultiTapeTM.whileRel_iff_iterate`: `WhileRel cond step a b` holds exactly if `b` is the
  first iterate of `step` starting from `a` that does not satisfy `cond`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_optionIte`: the condition and the body of a loop can
  be fused into a single function.
* `Turing.MultiTapeTM.computableInTimeAndSpace_whileFunction`: the complexity of a while loop,
  obtained from `computableInTimeAndSpace_optionIte` and `computableInTimeAndSpace_loopFunction`.
-/

namespace Turing.MultiTapeTM

variable {α : Type*} {cond : α → Bool} {step : α → α}

/-- The partial function computed by `while cond do step`. It is defined exactly on the inputs
for which the loop terminates. -/
public def whileFunction (cond : α → Bool) (step : α → α) : α →. α :=
  loopFunction fun a => if cond a then some (step a) else none

/-- The graph of the loop `while cond do step`: `WhileRel cond step a b` means that running the
loop from the state `a` terminates in the state `b`. -/
public inductive WhileRel (cond : α → Bool) (step : α → α) : α → α → Prop
  /-- The loop condition does not hold, so the loop exits immediately. -/
  | done {a : α} (h : cond a = false) : WhileRel cond step a a
  /-- The loop condition holds, so the loop runs its body once and continues. -/
  | loop {a b : α} (h : cond a = true) (hb : WhileRel cond step (step a) b) : WhileRel cond step a b

/-- The graph of `whileFunction` is `WhileRel`. -/
public theorem mem_whileFunction {a b : α} :
    b ∈ whileFunction cond step a ↔ WhileRel cond step a b := by
  have hnone {c : α} : (if cond c then some (step c) else none) = none ↔ cond c = false := by
    simp
  have hmem {c d : α} : d ∈ (if cond c then some (step c) else none) ↔
      cond c = true ∧ d = step c := by
    cases h : cond c <;> simp [eq_comm]
  rw [whileFunction, loopFunction, StateTransition.mem_eval]
  constructor
  · rintro ⟨hreach, hstop⟩
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact .done (hnone.mp hstop)
    | head hstep _ ih =>
      obtain ⟨hcond, rfl⟩ := hmem.mp hstep
      exact .loop hcond ih
  · intro hrel
    induction hrel with
    | done h => exact ⟨.refl, hnone.mpr h⟩
    | loop h _ ih => exact ⟨.head (hmem.mpr ⟨h, rfl⟩) ih.1, ih.2⟩

/-- The loop terminates in the first iterate of its body that does not satisfy the loop
condition. -/
public theorem whileRel_iff_iterate {a b : α} :
    WhileRel cond step a b ↔
      ∃ n, (∀ i < n, cond (step^[i] a) = true) ∧ cond (step^[n] a) = false ∧ b = step^[n] a := by
  constructor
  · intro hrel
    induction hrel with
    | done h => exact ⟨0, by simp, by simpa using h, rfl⟩
    | loop h _ ih =>
      obtain ⟨n, hlt, hn, rfl⟩ := ih
      refine ⟨n + 1, ?_, by rw [Function.iterate_succ_apply]; exact hn, ?_⟩
      · rintro (_ | i) hi
        · simpa using h
        · rw [Function.iterate_succ_apply]
          exact hlt i (by omega)
      · rw [Function.iterate_succ_apply]
  · rintro ⟨n, hlt, hn, rfl⟩
    induction n generalizing a with
    | zero => exact .done (by simpa using hn)
    | succ n ih =>
      refine .loop (by simpa using hlt 0 (by omega)) (ih ?_ ?_)
      · intro i hi
        rw [← Function.iterate_succ_apply]
        exact hlt (i + 1) (by omega)
      · rw [← Function.iterate_succ_apply]
        exact hn

/-- The graph of `whileFunction`, in terms of the iterates of the loop body. -/
public theorem mem_whileFunction_iff_iterate {a b : α} :
    b ∈ whileFunction cond step a ↔
      ∃ n, (∀ i < n, cond (step^[i] a) = true) ∧ cond (step^[n] a) = false ∧ b = step^[n] a := by
  rw [mem_whileFunction, whileRel_iff_iterate]

/-- If one iteration of the loop body makes the encoding grow by at most `growth`, then after `i`
iterations it has grown by at most `i * growth`. This is one way of obtaining the bound on the
intermediate values required by `computableInTimeAndSpace_whileFunction`. -/
public theorem length_enc_iterate_le {enc : α ↪ List Bool} {growth : ℕ}
    (hgrowth : ∀ a, (enc (step a)).length ≤ (enc a).length + growth) (a : α) (i : ℕ) :
    (enc (step^[i] a)).length ≤ (enc a).length + i * growth := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    calc (enc (step (step^[i] a))).length ≤ (enc (step^[i] a)).length + growth := hgrowth _
      _ ≤ (enc a).length + i * growth + growth := by omega
      _ = (enc a).length + (i + 1) * growth := by rw [Nat.succ_mul]; omega

/-- **Fusing the condition and the body of a loop into a single function.** This is a consequence
of `computableInTimeAndSpace_ite`, of `IsOptionEncoding.constructor_computable` composed with
`step` via `computableInTimeAndSpace_comp` (for the `some` branch), and of
`computableInTimeAndSpace_of_const` (for the constant `none` branch); no reasoning about machines
is needed. The length of the encoding of the new value enters the bounds because the composition
has to store it on a work tape. -/
proof_wanted computableInTimeAndSpace_optionIte
    {α : Type*} {cond : α → Bool} {step : α → α}
    {enc : α ↪ List Bool} {encOpt : Option α ↪ List Bool} {encBool : Bool ↪ List Bool}
    {tc sc ts ss : α → ℕ} (henc : IsOptionEncoding enc encOpt)
    (hcond : ComputableInTimeAndSpace cond enc encBool tc sc)
    (hstep : ComputableInTimeAndSpace step enc enc ts ss) :
    ∃ c, ComputableInTimeAndSpace (fun a => if cond a then some (step a) else none) enc encOpt
      (fun a => c * (tc a + ts a + (enc (step a)).length + 1))
      (fun a => c * (sc a + ss a + (enc (step a)).length + 1))

/-- **Complexity of a while loop.**

Assume that
* `f` picks, for every input, a value at which the loop terminates (`hf`), and the loop started at
  `a` needs at most `iterBound a` iterations (`hiter`);
* `cond` and `step` are both computable in time `t` and space `s` (`hcond`, `hstep`), where `s`
  also bounds the encoded length of all the values encountered while running the loop (`hsize`;
  note that this includes `a` itself, and see `length_enc_iterate_le` for how to obtain such a
  bound from a per-iteration growth bound);
* these bounds do not increase along the iterations of the loop (`ht`, `hs`).

Then `f` is computable in time proportional to the number of iterations times the cost of one
iteration, and in space proportional to the space of one iteration.

This is obtained from `computableInTimeAndSpace_optionIte`, which fuses `cond` and `step` into a
single body function, and `computableInTimeAndSpace_loopFunction`, which implements the loop for a
fused body; `whileFunction` is by definition the `loopFunction` of the fused body. No machine is
constructed here.

As in `computableInTimeAndSpace_loopFunction`, `hsize` is a genuine additional assumption on `s`,
since the space bound of `step` does not bound the length of its output. Since the resulting bounds
are stated up to a constant factor, using a single `s` for all three purposes is no weaker than
using three separate bounds, whose maximum `s` can be taken to be, and likewise for using a single
time bound for `cond` and `step`. -/
proof_wanted computableInTimeAndSpace_whileFunction
    {α : Type*} {cond : α → Bool} {step : α → α} {f : α → α}
    {enc : α ↪ List Bool} {encOpt : Option α ↪ List Bool} {encBool : Bool ↪ List Bool}
    {t s iterBound : α → ℕ}
    (hf : ∀ a, f a ∈ whileFunction cond step a)
    (hiter : ∀ a, ∃ m ≤ iterBound a, cond (step^[m] a) = false)
    (hsize : ∀ a i, (enc (step^[i] a)).length ≤ s a)
    (henc : IsOptionEncoding enc encOpt)
    (hcond : ComputableInTimeAndSpace cond enc encBool t s)
    (hstep : ComputableInTimeAndSpace step enc enc t s)
    (ht : ∀ a i, t (step^[i] a) ≤ t a) (hs : ∀ a i, s (step^[i] a) ≤ s a) :
    ∃ c, ComputableInTimeAndSpace f enc enc
      (fun a => c * (iterBound a + 1) * (t a + s a + 1))
      (fun a => c * (s a + 1))

end Turing.MultiTapeTM
