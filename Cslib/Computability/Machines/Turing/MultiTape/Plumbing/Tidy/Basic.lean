/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Basic properties of tidy computations

A tidy computation is a computation, it emits at most one symbol per step, and it stays tidy when
the machine is given more work tapes.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace`: a tidily
  computable function is computable, within the same bounds.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.length_output_le`: a tidy computation emits at
  most one symbol per step.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.extendTapes`: a tidy computation stays tidy with
  more work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

namespace ComputesTidilyInTimeAndSpace

variable {input output : List Symbol}

/-- A tidy computation is a computation in the sense of
`Turing.MultiTapeTM.ComputesInTimeAndSpace`. -/
theorem computesInTimeAndSpace (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t s := by
  obtain ⟨hrun, hspace⟩ := computesTidily_iff.mp h
  rw [← Cfg.init_eq_wordsCfg] at hrun hspace
  have hhalt := congrArg Cfg.state hrun
  exact ⟨⟨t, hhalt, congrArg Cfg.output hrun⟩, runsInTime_iff_halted.mpr hhalt,
    runsInSpace_of_halted hhalt hspace⟩

/-- A tidy computation within `t` steps emits at most `t` symbols. -/
theorem length_output_le (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    output.length ≤ t := by
  simpa [(computesTidily_iff.mp h).1] using
    tm.length_output_runFrom_le (wordsCfg input (some tm.q₀) (fun _ => []) []) t

/-- A tidy computation stays tidy with more work tapes, at one cell per added tape. -/
theorem extendTapes {k' : ℕ} (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).ComputesTidilyInTimeAndSpace input output t (s + (k' - k)) := by
  refine (TransformsTapes.extendTapes h e).imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by subst hws; rfl⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨⟨hv, hout⟩, hx⟩ => ⟨funext fun l => ?_, hout⟩) le_rfl le_rfl
  by_cases hl : l ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hl
    exact congrFun hv j
  · exact (hx l hl).trans (congrFun hws l)

end ComputesTidilyInTimeAndSpace

variable {α β : Type*}

/-- A tidy computation of a function is a computation of it. -/
theorem ComputesFunTidilyInTimeAndSpace.computesFunInTimeAndSpace {encIn : α ↪ List Symbol}
    {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t s :=
  fun a => (h a).computesInTimeAndSpace

namespace ComputableTidilyInTimeAndSpace

variable {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}

/-- The output of a tidily computable function is no longer than its time bound. -/
theorem length_le (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) (a : α) :
    (encOut (f a)).length ≤ t a :=
  let ⟨_, _, _, _, htm⟩ := h
  (htm a).length_output_le

/-- A tidily computable function is computable. -/
theorem computableInTimeAndSpace (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace f encIn encOut t s :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, State, hfinite, tm, htm.computesFunInTimeAndSpace⟩

end ComputableTidilyInTimeAndSpace

end Turing.MultiTapeTM
