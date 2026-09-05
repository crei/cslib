/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic

/-!
# Machines that halt cleanly

A machine *halts cleanly* if, whenever it is started in its initial state with blank work tapes and
all work tape heads at position `0`, it halts in a configuration in which the work tapes are blank
again and all work tape heads are back at position `0`. The position of the input head and the
output produced are not constrained: they are part of the specification of the machine, not of the
plumbing.

Halting cleanly is what makes machines composable: the machine that runs next can assume that it
starts on blank tapes, without knowing anything about the machine that ran before it.

## Main definitions

* `Turing.MultiTapeTM.Cfg.IsClean`: all work tapes are blank and all work tape heads are at
  position `0`.
* `Turing.MultiTapeTM.HaltsClean`: started clean, the machine halts clean.

## Main results

* `Turing.MultiTapeTM.exists_haltsClean_computesFun`: the clean normal form. Every machine can be
  replaced by one that computes the same function, halts cleanly, and stays within a constant
  factor of the original time and space bounds.

The construction uses one *shadow tape per work tape*: the machine with `k` work tapes is simulated
by a machine with `2 * k` work tapes, where writing to tape `i` also writes a marker to tape
`k + i`, whose head is kept at the same position. When the simulated machine halts, the marked
region of every tape is walked and erased. Note that:

* erasing "until a blank is found" without the shadow tapes is unsound, since a machine may write
  blanks inside the region it has used;
* a single global shadow tape does not work, since the heads of different tapes are at different
  positions; with one shadow tape per work tape the head positions stay in bijection;
* the clean-up has to run on all tapes in parallel, otherwise the time is `k * s` instead of `s`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A configuration is clean if all its work tapes are blank and all work tape heads are at
position `0`. -/
public def Cfg.IsClean (cfg : Cfg k Symbol State input) : Prop :=
  (∀ (i : Fin k) (z : ℤ), cfg.workTapes i z = none) ∧ ∀ i : Fin k, cfg.workTapePos i = 0

/-- A machine halts cleanly if every halting configuration that it reaches from a clean initial
configuration is clean. -/
public def HaltsClean (tm : MultiTapeTM k Symbol State) : Prop :=
  ∀ (input : List Symbol) (cfg : Cfg k Symbol State input), cfg.state = some tm.q₀ → cfg.IsClean →
    ∀ t : ℕ, (tm.runFrom cfg t).state = none → (tm.runFrom cfg t).IsClean

/-- The initial configuration is clean. -/
proof_wanted isClean_initCfg {tm : MultiTapeTM k Symbol State} (input : List Symbol) :
    (tm.initCfg input : Cfg k Symbol State input).IsClean

/-- **The clean normal form.** Every machine can be replaced by a machine that computes the same
function, halts cleanly and stays within a constant factor of the original time and space bounds.
The new machine has twice as many work tapes: one shadow tape per work tape, recording the cells
that have been written to. -/
proof_wanted exists_haltsClean_computesFun {Symbol : Type} [Nonempty Symbol] {State : Type}
    [Finite State] {α β : Type*} {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol}
    {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s) :
    ∃ (c : ℕ) (State' : Type) (_ : Finite State') (tm' : MultiTapeTM (2 * k) Symbol State'),
      HaltsClean tm' ∧
      ComputesFunInTimeAndSpace tm' encIn encOut f (fun a => c * (t a + 1)) (fun a => c * (s a + 1))

end Turing.MultiTapeTM
