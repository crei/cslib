/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.StepLemmas
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Machines that never write the real output

Every tape *transformer* redirects its result onto a work tape and never touches the real output.
For such a machine the real output is inert: preserved along the whole run, and the run and space
usage commute with replacing it. This is what lets a transformer be run from a configuration whose
output is already present, as the word-transformer interface
`Turing.MultiTapeTM.TransformsTapes` quantifies over — the caller need not know the output is
empty.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A machine none of whose transitions emit an output symbol. -/
public def NeverOutputs (tm : MultiTapeTM k Symbol State) : Prop :=
  ∀ q inp work, (tm.tr q inp work).output = none

variable {tm : MultiTapeTM k Symbol State}

/-- Such a machine's step commutes with replacing the real output. -/
public lemma step_withOutput_of_neverOutputs (h : NeverOutputs tm)
    (cfg : Cfg k Symbol State input) (out : List Symbol) :
    tm.step (cfg.withOutput out) = (tm.step cfg).withOutput out := by
  cases hq : cfg.state with
  | none =>
    have h1 : (cfg.withOutput out).state = none := hq
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (cfg.withOutput out).state = some q := hq
    have hin : (cfg.withOutput out).inputSymbol = cfg.inputSymbol := rfl
    have hws : (cfg.withOutput out).workTapeSymbols = cfg.workTapeSymbols := rfl
    rw [step_apply_of_state h1, step_apply_of_state hq, hin, hws]
    refine Cfg.ext rfl rfl (funext fun l => funext fun z => by simp [Cfg.withOutput])
      (funext fun l => by simp [Cfg.withOutput]) ?_
    simp only [Action.apply_output, Cfg.withOutput_output,
      h q cfg.inputSymbol cfg.workTapeSymbols, Option.toList_none, List.append_nil]

/-- The run of such a machine commutes with replacing the real output. -/
public lemma runFrom_withOutput_of_neverOutputs (h : NeverOutputs tm)
    (cfg : Cfg k Symbol State input) (out : List Symbol) (n : ℕ) :
    tm.runFrom (cfg.withOutput out) n = (tm.runFrom cfg n).withOutput out :=
  runFrom_comm_of_step (fun c => c.withOutput out)
    (fun c => step_withOutput_of_neverOutputs h c out) cfg n

/-- Such a machine's space does not depend on the real output already present. -/
public lemma spaceUsed_withOutput_of_neverOutputs (h : NeverOutputs tm)
    (cfg : Cfg k Symbol State input) (out : List Symbol) (u : ℕ) :
    tm.spaceUsed (cfg.withOutput out) u = tm.spaceUsed cfg u := by
  refine spaceUsed_eq_of_workTapePos _ _ u fun m _ => ?_
  rw [runFrom_withOutput_of_neverOutputs h]; rfl

/-- The real output is unchanged along the run of such a machine. -/
public lemma output_runFrom_of_neverOutputs (h : NeverOutputs tm)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.runFrom cfg n).output = cfg.output := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [runFrom_succ_eq_step', step_output, ih]
    rcases hs : (tm.runFrom cfg n).state with _ | q
    · simp [outputSymbol, hs]
    · simp [outputSymbol, hs, h q]

end Turing.MultiTapeTM
