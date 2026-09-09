/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Reducing one step of an explicit machine

Every explicit-machine proof — `Copy`, `Clear`, `Rewind`, `Sweep`, `instrument`, the redirections —
computes `tm.step cfg` for a configuration in a known state `some q` and reads off the fields of
the result. The `Action.apply_*` projections here are `@[simp]`, so a caller reduces a step with
`simp [step, hq, <machine>]` without having to name `Action.apply` and without the projection
debris in the fields it does not care about; `step_apply_of_state hq` turns `step` at a live state
into an `Action.apply` for a one-field rewrite, leaving the transition `tm.tr q _ _` folded until
the caller computes it.

Also here: reduction of `SignType` casts to `ℤ` (`SignType.cast_neg`/`zero`/`pos`). Combined with
`Turing.val_moveInputPos_eq` — the input head's post-move position as an `omega`-native clamped
integer — these are what let head-position goals over the boundary-clamping input head close by
`omega` instead of by a `SignType`-case analysis. The redirection machines are the customers.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

@[simp] public lemma _root_.SignType.cast_neg_one : ((SignType.neg : SignType) : ℤ) = -1 := by
  simp [SignType.cast]

@[simp] public lemma _root_.SignType.cast_zero_int : ((SignType.zero : SignType) : ℤ) = 0 := by
  simp [SignType.cast]

@[simp] public lemma _root_.SignType.cast_one_int : ((SignType.pos : SignType) : ℤ) = 1 := by
  simp [SignType.cast]

@[simp] public lemma Action.apply_state (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) : (a.apply cfg).state = a.state := rfl

@[simp] public lemma Action.apply_inputPos (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (a.apply cfg).inputPos = moveInputPos cfg.inputPos a.inputTape := rfl

@[simp] public lemma Action.apply_output (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (a.apply cfg).output = cfg.output ++ a.output.toList := rfl

@[simp] public lemma Action.apply_workTapePos (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    (a.apply cfg).workTapePos i = cfg.workTapePos i + (a.workTapes i).2 := rfl

@[simp] public lemma Action.apply_workTapes (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    (a.apply cfg).workTapes i = match (a.workTapes i).1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s := rfl

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State} {cfg : Cfg k Symbol State input} {q : State}

/-- One step at a live state is the transition's action applied to the configuration. This is the
form `simp only [step_apply_of_state hq]` uses to reduce a whole step. -/
public lemma step_apply_of_state (h : cfg.state = some q) :
    tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  rw [step, h]

/-- The state after a live step. -/
public lemma step_state_of_state (h : cfg.state = some q) :
    (tm.step cfg).state = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).state := by
  rw [step_apply_of_state h, Action.apply_state]

/-- The input head after a live step. -/
public lemma step_inputPos_of_state (h : cfg.state = some q) :
    (tm.step cfg).inputPos =
      moveInputPos cfg.inputPos (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputTape := by
  rw [step_apply_of_state h, Action.apply_inputPos]

/-- A work tape after a live step. -/
public lemma step_workTapes_of_state (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapes i =
      match (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i |>.1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s := by
  rw [step_apply_of_state h, Action.apply_workTapes]

/-- A work tape head after a live step. -/
public lemma step_workTapePos_of_state (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapePos i =
      cfg.workTapePos i + ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i).2 := by
  rw [step_apply_of_state h, Action.apply_workTapePos]

end MultiTapeTM

end Turing
