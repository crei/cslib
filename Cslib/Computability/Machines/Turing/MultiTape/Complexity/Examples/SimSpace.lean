/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SimConfig
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SpaceBound

/-!
# The simulation runs in the simulated machine's space

`SimConfig` shows the finite stand-in reproduces a machine's run. This file bounds its *size*, and
bounds it by the simulated machine's **space** rather than by its running time — the distinction
that makes a simulation worth having, since a machine may run for exponentially many steps in
polynomial space.

The argument has two halves, both already proved elsewhere:

* `Extent` says a zipper stores exactly the cells spanned by the positions its head has covered,
  so it grows only on ground the head has not been on before;
* `span_le_spaceUsedByTape` says that span is bounded by the number of distinct cells visited,
  which is exactly `MultiTapeTM.spaceUsedByTape`.

`ExtentOK` is what carries the first half along a run: it pins each zipper's extent between two
positions the head has actually occupied (to within one cell). Because `Extent.of_applyAction` moves
an endpoint only *to the head's own position*, that invariant survives each step, and no
`min`/`max` over the whole history is needed.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace Simulation

open RoseTreeMachine

variable {k sym state : ℕ}

/-- The position of work head `i` at time `t` of the canonical run. -/
def headPos (tm : MultiTapeTM k (Fin sym) (Fin state)) (inp : List (Fin sym))
    (i : Fin k) (t : ℕ) : ℤ :=
  (tm.runFrom (tm.initCfg inp) t).workTapePos i

/-- The finite stand-in after `t` steps. -/
def simRun (tm : MultiTapeTM k (Fin sym) (Fin state)) (inp : List (Fin sym)) (t : ℕ) :
    SimCfg sym state :=
  (cfgStep tm)^[t] (initSimCfg tm inp)

/-- **The extent invariant along a run**: the zipper for tape `i` has an extent whose endpoints
each lie within one cell of a position the head has actually occupied. -/
def ExtentOK (tm : MultiTapeTM k (Fin sym) (Fin state)) (inp : List (Fin sym))
    (i : Fin k) (t : ℕ) : Prop :=
  ∃ lo hi, Extent (workZipper (simRun tm inp t) i.val) lo (headPos tm inp i t) hi
    ∧ (∃ a ≤ t, headPos tm inp i a - 1 ≤ lo)
    ∧ (∃ b ≤ t, hi ≤ headPos tm inp i b + 1)

lemma extentOK_zero (tm : MultiTapeTM k (Fin sym) (Fin state)) (inp : List (Fin sym))
    (i : Fin k) : ExtentOK tm inp i 0 := by
  have hz : workZipper (simRun tm inp 0) i.val = (([], []) : Tape (Option (Fin sym))) := by
    unfold simRun workZipper initSimCfg
    simp [i.isLt]
  have hp : headPos tm inp i 0 = 0 := by simp [headPos]
  refine ⟨0, 0, ?_, ⟨0, le_refl _, ?_⟩, ⟨0, le_refl _, ?_⟩⟩
  · rw [hz, hp]; exact Extent.init
  · rw [hp]; omega
  · rw [hp]; omega

lemma extentOK_succ (tm : MultiTapeTM k (Fin sym) (Fin state)) (inp : List (Fin sym))
    (i : Fin k) (t : ℕ) (h : ExtentOK tm inp i t) : ExtentOK tm inp i (t + 1) := by
  obtain ⟨lo, hi, hext, ⟨a, ha, hla⟩, ⟨b, hb, hhb⟩⟩ := h
  have hrep : Represents (simRun tm inp t) (tm.runFrom (tm.initCfg inp) t) :=
    simulates tm inp t
  have hrun : simRun tm inp (t + 1) = cfgStep tm (simRun tm inp t) := by
    unfold simRun
    rw [Function.iterate_succ_apply']
  cases hq : (simRun tm inp t).1 with
  | none =>
    -- the machine has halted, so nothing changes
    have hcfg : (tm.runFrom (tm.initCfg inp) t).state = none := by rw [← hrep.1, hq]
    have hstep : tm.runFrom (tm.initCfg inp) (t + 1) = tm.runFrom (tm.initCfg inp) t := by
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_of_halt hcfg]
    have hz : workZipper (simRun tm inp (t + 1)) i.val = workZipper (simRun tm inp t) i.val := by
      rw [hrun]
      have : cfgStep tm (simRun tm inp t) = simRun tm inp t := by simp [cfgStep, hq]
      rw [this]
    have hp : headPos tm inp i (t + 1) = headPos tm inp i t := by
      unfold headPos; rw [hstep]
    exact ⟨lo, hi, by rw [hz, hp]; exact hext,
      ⟨a, by omega, hla⟩, ⟨b, by omega, hhb⟩⟩
  | some q =>
    have hcfg : (tm.runFrom (tm.initCfg inp) t).state = some q := by rw [← hrep.1, hq]
    set cfg := tm.runFrom (tm.initCfg inp) t with hcfgdef
    set o := tm.tr q cfg.inputSymbol cfg.workTapeSymbols with hodef
    have ho : tm.tr q (cursorRead none (simRun tm inp t).2.1)
        (fun j : Fin k => read none (workZipper (simRun tm inp t) j.val)) = o :=
      Represents.tr_eq hrep tm q
    have hz := workZipper_cfgStep tm (simRun tm inp t) q hq o ho i
    rw [← hrun] at hz
    have hp : headPos tm inp i (t + 1) = headPos tm inp i t + (o.workActions i).2 := by
      unfold headPos
      rw [MultiTapeTM.runFrom_succ_eq_step', step_workTapePos tm cfg q hcfg i]
    obtain ⟨lo', hi', hext', _, _, _, _, hlo', hhi'⟩ :=
      Extent.of_applyAction (blank := (none : Option (Fin sym))) (o.workActions i) hext
    refine ⟨lo', hi', ?_, ?_, ?_⟩
    · rw [hz, hp]
      exact hext'
    · rcases hlo' with hl | hl
      · exact ⟨a, by omega, by omega⟩
      · exact ⟨t + 1, le_refl _, by rw [hp]; omega⟩
    · rcases hhi' with hh | hh
      · exact ⟨b, by omega, by omega⟩
      · exact ⟨t, by omega, by omega⟩

lemma extentOK (tm : MultiTapeTM k (Fin sym) (Fin state)) (inp : List (Fin sym))
    (i : Fin k) (t : ℕ) : ExtentOK tm inp i t := by
  induction t with
  | zero => exact extentOK_zero tm inp i
  | succ t ih => exact extentOK_succ tm inp i t ih

/-- **The simulation's tapes are bounded by the simulated machine's space.**

The number of cells the stand-in stores for work tape `i` after `t` steps is at most the number of
cells the real machine's head has visited, plus one. In particular it does *not* grow with the
running time: a machine that runs for exponentially many steps in a bounded region is simulated in
a bounded amount of storage. -/
theorem zipper_length_le_spaceUsed (tm : MultiTapeTM k (Fin sym) (Fin state))
    (inp : List (Fin sym)) (i : Fin k) (t : ℕ) :
    (workZipper (simRun tm inp t) i.val).1.length
        + (workZipper (simRun tm inp t) i.val).2.length
      ≤ tm.spaceUsedByTape (tm.initCfg inp) t i + 1 := by
  obtain ⟨lo, hi, hext, ⟨a, ha, hla⟩, ⟨b, hb, hhb⟩⟩ := extentOK tm inp i t
  have hlen := Extent.length_eq hext
  have hspan := span_le_spaceUsedByTape tm (tm.initCfg inp) t i ha hb
  unfold headPos at hla hhb
  omega

end Simulation

end MultiTapeTM

end Turing
