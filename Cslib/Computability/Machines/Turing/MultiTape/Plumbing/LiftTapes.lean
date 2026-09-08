/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic

/-!
# Running a machine on other tapes

A machine that is combined with other machines needs more work tapes than it uses itself, and its
tapes have to be placed among the tapes of the combined machine. `liftTapes e tm`, for an injection
`e : Fin k ↪ Fin k'`, runs the `k`-tape machine `tm` on a machine with `k'` work tapes, using tape
`e i` for tape `i` and leaving all other tapes and their heads untouched.

## Main definitions

* `Turing.MultiTapeTM.Tapes.restrict`: the tapes in the image of `e`, seen as the tapes of a
  `k`-tape machine.

## Main results

* `Turing.MultiTapeTM.exists_transformsCfg_liftTapes`: a transformation performed by a `k`-tape
  machine can be performed by a `k'`-tape machine on any `k` of its tapes, in the same time. Note
  that the space bound grows by `k'`, since every work tape head visits at least one cell.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The tapes of a `k'`-tape configuration in the image of `e`, seen as the tapes of a `k`-tape
configuration. -/
public def Tapes.restrict (e : Fin k ↪ Fin k') (tp : Tapes k' Symbol input) :
    Tapes k Symbol input :=
  ⟨none, tp.inputPos, fun i => tp.workTapes (e i), fun i => tp.workTapePos (e i), tp.output⟩

/-- **Running a machine on other tapes.** A transformation performed by a `k`-tape machine can be
performed by a `k'`-tape machine on the tapes selected by `e`, in the same time and with the same
space, up to the one cell that every one of the `k'` heads visits. The tapes outside the image of
`e` are untouched, which is already part of `TransformsCfg`. -/
proof_wanted exists_transformsCfg_liftTapes {tm : MultiTapeTM k Symbol State} {S : Finset (Fin k)}
    {P : (input : List Symbol) → Tapes k Symbol input → Prop}
    {Q : (input : List Symbol) → Tapes k Symbol input → Tapes k Symbol input → Prop} {t s : ℕ}
    (e : Fin k ↪ Fin k') (h : TransformsCfg tm S P Q t s) :
    ∃ tm' : MultiTapeTM k' Symbol State, TransformsCfg tm' (S.map e)
      (fun input tp => P input (tp.restrict e))
      (fun input tp tp' => Q input (tp.restrict e) (tp'.restrict e)) t (s + k')

end Turing.MultiTapeTM
