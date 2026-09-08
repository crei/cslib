/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.List.Infix
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Basic vocabulary for machine plumbing

Combining Turing machines is mostly about moving data between tapes and about running a machine
on tapes other than the ones it was written for. The statements of these constructions have to
talk about configurations without mentioning the state of the machine, since the machines that are
combined all have different state types.

This file provides that vocabulary:

## Main definitions

* `Turing.MultiTapeTM.Cfg.withState`: a configuration with its state replaced, possibly over a
  different state type.
* `Turing.MultiTapeTM.Tapes`: the state-erased part of a configuration, i.e. a configuration over
  the state type `Unit` with state `none`.
* `Turing.MultiTapeTM.Cfg.AgreesOutside`: two configurations differ at most on a given set of work
  tapes (and on the output, which can only grow).
* `Turing.MultiTapeTM.TransformsCfg`: the specification format of the plumbing machines: started in
  its initial state from a configuration satisfying a precondition, the machine halts within given
  time and space bounds in a configuration related to the initial one by a postcondition, touching
  only a given set of work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- The configuration `cfg` with its state replaced by `q`, possibly over a different state
type. -/
public def Cfg.withState (cfg : Cfg k Symbol State input) {State' : Type*}
    (q : Option State') : Cfg k Symbol State' input :=
  ⟨q, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

@[simp]
public lemma Cfg.withState_state {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).state = q := rfl

@[simp]
public lemma Cfg.withState_inputPos {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).inputPos = cfg.inputPos := rfl

@[simp]
public lemma Cfg.withState_workTapes {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).workTapes = cfg.workTapes := rfl

@[simp]
public lemma Cfg.withState_workTapePos {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).workTapePos = cfg.workTapePos := rfl

@[simp]
public lemma Cfg.withState_output {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).output = cfg.output := rfl

@[simp]
public lemma Cfg.withState_inputSymbol {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).inputSymbol = cfg.inputSymbol := rfl

@[simp]
public lemma Cfg.withState_workTapeSymbols {cfg : Cfg k Symbol State input} {State' : Type*}
    {q : Option State'} : (cfg.withState q).workTapeSymbols = cfg.workTapeSymbols := rfl

@[simp]
public lemma Cfg.withState_withState {cfg : Cfg k Symbol State input} {State' State'' : Type*}
    {q : Option State'} {q' : Option State''} :
    (cfg.withState q).withState q' = cfg.withState q' := rfl

@[simp]
public lemma Cfg.withState_self {cfg : Cfg k Symbol State input} :
    cfg.withState cfg.state = cfg := rfl

/-- The part of a configuration that does not depend on the machine: the input head position, the
work tapes, the work tape heads and the output. It is represented as a configuration over the
state type `Unit`. -/
public abbrev Tapes (k : ℕ) (Symbol : Type*) (input : List Symbol) := Cfg k Symbol Unit input

/-- The state-erased part of a configuration. -/
public def Cfg.tapes (cfg : Cfg k Symbol State input) : Tapes k Symbol input := cfg.withState none

/-- `AgreesOutside S tp₁ tp₂` states that `tp₂` differs from `tp₁` at most on the work tapes in `S`
and on the output, which can only have grown. -/
public def Cfg.AgreesOutside (S : Finset (Fin k)) (tp₁ tp₂ : Tapes k Symbol input) : Prop :=
  tp₁.inputPos = tp₂.inputPos ∧ tp₁.output <+: tp₂.output ∧
    ∀ i ∉ S, tp₁.workTapes i = tp₂.workTapes i ∧ tp₁.workTapePos i = tp₂.workTapePos i

/-- The specification format of the plumbing machines. `TransformsCfg tm S P Q t s` states that,
started in the state `tm.q₀` from any configuration whose tapes satisfy `P`, the machine `tm` halts
after at most `t` steps and using at most `s` space, in a configuration whose tapes are related to
the initial ones by `Q`, and only the work tapes in `S` have been touched.

Note that `t` and `s` are numbers: the dependency on the data on the tapes is expressed by
quantifying over that data outside of `TransformsCfg`, with `P` pinning it down. -/
public def TransformsCfg (tm : MultiTapeTM k Symbol State) (S : Finset (Fin k))
    (P : (input : List Symbol) → Tapes k Symbol input → Prop)
    (Q : (input : List Symbol) → Tapes k Symbol input → Tapes k Symbol input → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (cfg : Cfg k Symbol State input),
    cfg.state = some tm.q₀ → P input cfg.tapes →
      ∃ t' ≤ t, (tm.runFrom cfg t').state = none ∧
        Q input cfg.tapes (tm.runFrom cfg t').tapes ∧
        tm.spaceUsed cfg t' ≤ s ∧
        Cfg.AgreesOutside S cfg.tapes (tm.runFrom cfg t').tapes

/-- Weakening the bounds of a `TransformsCfg` statement. -/
proof_wanted TransformsCfg.mono {tm : MultiTapeTM k Symbol State} {S P Q} {t s t' s' : ℕ}
    (h : TransformsCfg tm S P Q t s) (ht : t ≤ t') (hs : s ≤ s') : TransformsCfg tm S P Q t' s'

end Turing.MultiTapeTM
