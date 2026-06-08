/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.Prog
public import Cslib.Computability.Machines.MultiTapeTuring.Basic


/-! # RoseTreeMachine V4 — simulation theorems (statements only)

This file collects the cross-model simulation statements relating the functional language
`Prog`, its first-order fragment `InPlace`, and multi-tape Turing machines. All statements are
currently `sorry`-ed; they record the intended theorems and their resource overheads.

Each statement is phrased with the `…ComputableInTimeAndSpace` predicates, so the only remaining
quantifier is the existentially quantified constant `a` carrying the (constant-factor or
provisional polynomial) overhead.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

/-- A boolean function is computable by some multi-tape Turing machine within the given time and
space bounds. -/
def TMComputableInTimeAndSpace (f : List Bool → List Bool) (t s : ℕ → ℕ) : Prop :=
  ∃ (k : ℕ) (tm : MultiTapeTM k Bool), tm.ComputesFunInTimeAndSpace f t s

/-- A boolean function is computable by some `Prog` within the given time and space bounds. -/
def ProgComputableInTimeAndSpace (f : List Bool → List Bool) (t s : ℕ → ℕ) : Prop :=
  ∃ (p : Prog), p.ComputesBoolFunInTimeAndSpace f t s

/-- A boolean function is computable by some *in-place* `Prog` within the given time and space
bounds. -/
def InPlaceProgComputableInTimeAndSpace (f : List Bool → List Bool) (t s : ℕ → ℕ) : Prop :=
  ∃ (p : Prog), InPlace p ∧ p.ComputesBoolFunInTimeAndSpace f t s

/-- **In-place `Prog` → Turing machine.** An in-place program is implemented by a multi-tape
Turing machine with only constant-factor time and space overhead.

The linear *space* bound `a * s` reflects a constant-factor tape encoding of the rose-tree data.
The linear *time* bound `a * t` is the strong part of the statement: the `Prog` cost model
charges nothing for environment manipulation (variable access is charged by value size, binding
`σ ++ [v]` is free), so achieving a *linear* — rather than e.g. `a * (t * s)` — time overhead
relies on the tape encoding supporting O(1)-amortized variable addressing and environment
extension. -/
lemma inPlace_prog_to_tm
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : InPlaceProgComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ), TMComputableInTimeAndSpace f (fun n => a * t n) (fun n => a * s n) := by
  sorry

/-- **`Prog` → in-place `Prog`.** Every program is simulated by an in-place program computing the
same function (defunctionalisation: the explicit-stack machine of `StackSim` realised as a single
`while_` loop).

Provisional overhead: making environment threading explicit multiplies time by (at most) the
space, hence `a * (t * s)`; the space bound `a * s` assumes a shared-environment encoding that
avoids duplicating the environment into every stack frame. -/
lemma prog_to_inPlace
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : ProgComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ),
      InPlaceProgComputableInTimeAndSpace f (fun n => a * (t n * s n)) (fun n => a * s n) := by
  sorry

/-- **`Prog` → Turing machine.** Corollary of `prog_to_inPlace` followed by `inPlace_prog_to_tm`:
every program is implemented by a multi-tape Turing machine. The overhead is inherited from the
`Prog → InPlace` step. -/
lemma prog_to_tm
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : ProgComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ), TMComputableInTimeAndSpace f (fun n => a * (t n * s n)) (fun n => a * s n) := by
  sorry

/-- **Turing machine → in-place `Prog`.** The reverse direction (the universal-machine
construction of `UniversalTM`): every multi-tape Turing machine is simulated by an in-place
program.

Provisional overhead: each Turing-machine step is realised by scanning the encoded tape
configuration, costing time proportional to the space, hence `a * (t * s)`; space stays within a
constant factor, `a * s`. -/
lemma tm_to_inPlace_prog
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : TMComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ),
      InPlaceProgComputableInTimeAndSpace f (fun n => a * (t n * s n)) (fun n => a * s n) := by
  sorry

end V4

end RoseTreeMachine

end Turing
