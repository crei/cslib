<pre>
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Plumbing for multi-tape Turing machines

The [Combinators](../Combinators) directory builds machines that compute functions built from
other functions (constants, sequential composition of functions, loops, ...). Almost all of the
work in these constructions is not about the function being computed, but about *plumbing*: moving
data between tapes, running a machine on tapes other than the ones it was written for, adding tapes
that a machine does not use, and making sure that a machine leaves the machinery in a state in
which the next machine can be started.

This directory collects that plumbing, so that the combinators can be assembled from
function-level statements and a small number of normal forms.

## Design principles

* **Machines, not functions.** The results here are about `runFrom` and configurations, not about
  `ComputesFunInTimeAndSpace`. The bridge to the function level is made once, in `OnTape`.
* **Normal forms instead of state surgery.** Rather than reaching into the state space of a given
  machine, we first bring it into a normal form (halting cleanly, see `Clean`) and then treat it as
  a black box. This keeps the combinators free of assumptions about the machines they combine.
* **Costs are constant factors.** Every construction here may cost a constant factor in time and
  space; this is absorbed by the existential constant of `ComputableInTimeAndSpace`.
* **As few machine-level results as possible.** The plumbing exists only to prove a handful of
  function-level combinators, which are the reusable interface:
  `computableInTimeAndSpace_ite` (from `exists_branchOnTape`), the composition of functions (from
  `seq` and `onTape`), and the loop combinator `computableInTimeAndSpace_loopFunction`. Everything
  else, in particular the whole `while` result, is derived from those without mentioning tapes.
  The loop is the only combinator that genuinely needs a machine-level branch, since it chooses
  between continuing the loop and leaving it, which is not a choice between two functions.

## Components

Each file contains the statements of its results as `proof_wanted`s, together with the definitions
that are needed to state them. The constructions themselves are still missing.

### `Basic.lean`

The vocabulary shared by all of the following: `Cfg.withState`, `Tapes` (the state-erased part of a
configuration, needed because the machines that are combined all have different state types),
`Cfg.AgreesOutside` and `TransformsCfg`, the specification format of a plumbing machine: started in
its initial state from a configuration satisfying a precondition, it halts within given time and
space bounds in a configuration related to the initial one by a postcondition, touching only a
given set of work tapes.

### `Sequential.lean` (construction done)

`seq tm₁ tm₂` runs `tm₁` and, when `tm₁` would halt, continues with `tm₂` from the reached
configuration: input head, work tapes, work-tape heads and the output produced so far are handed
over unchanged. This is composition of machines as configuration transformers, not composition of
the computed functions.

* `runFrom_seq` splits a run of `seq tm₁ tm₂` into the two phases (proved),
* `transformsCfg_seq` composes two `TransformsCfg` statements.

### `LiftTapes.lean`

`exists_transformsCfg_liftTapes`: for an injection `e : Fin k ↪ Fin k'`, a transformation performed
by a `k`-tape machine can be performed by a `k'`-tape machine on the tapes selected by `e`, leaving
all other tapes and their heads untouched. Every machine that is combined with another one goes
through this, since the combined machine has more tapes than its parts. Time is preserved; the
space bound grows by `k'`, since each of the `k'` heads visits at least one cell.

### `Clean.lean`

`Cfg.IsClean` (all work tapes blank, all work tape heads at `0`) and `HaltsClean` (started clean,
the machine halts clean). The input head position and the output are not constrained: they belong
to the specification of the machine, not to the plumbing.

`exists_haltsClean_computesFun` is the normal form: every machine can be replaced by one that
computes the same function, halts cleanly, and stays within a constant factor of its time and space
bounds. The construction uses one *shadow tape per work tape* (`k → 2 * k`): writing to a work tape
also marks the corresponding cell of its shadow tape, and the clean-up walks the marked region and
erases it. Note that:

* naively erasing "until a blank is found" is unsound, since a machine may write blanks inside the
  region it has used;
* a single global shadow tape does not work, since the heads of different tapes are at different
  positions; with one shadow tape per work tape the head positions stay in bijection, which keeps
  the simulation lemma cheap;
* the clean-up must run on all tapes *in parallel*, otherwise the total time is `k * s` rather
  than `s` per tape.

### `TapeContents.lean`

`TapeHolds i w cfg`: work tape `i` contains exactly `w`, starting at position `0`, blank elsewhere,
with the head at `0`. In particular `TapeHolds i []` says that the tape is blank and rewound.
Since the contents are a `List Symbol`, they are blank-free, so a machine can find their end by
scanning for the first blank.

* `exists_clearTape`: blank a tape and rewind it,
* `exists_moveTapeTail`: move the contents of a tape, without its first symbol, to a blank tape,
* `exists_branchOnTape`: behave like one of two machines depending on the symbol under a tape head.
  Its function-level face is `computableInTimeAndSpace_ite`; it is used directly only by the loop
  combinator, for the continue flag of a fused loop body.

All of these are linear in the length of the contents and touch only the tapes they are given.

### `OnTape.lean`

The bridge between the machine level and the function level.

* `exists_outputToTape`: run a machine computing `f` on the real input tape, with its output
  written to a work tape,
* `exists_onTape`: run it with a work tape in place of the input tape and a work tape in place of
  the output tape,
* `exists_tapeToOutput`: emit the contents of a work tape as the output.

There is deliberately no `inputToTape`: the input tape is read-only, so the first machine that is
run on the input reads it there, and only the results of intermediate computations ever live on
work tapes.

The delicate point in `onTape` is the input head of the simulated machine, which the machine
believes to be a clamped position in `Fin (n + 2)`, while the head of a work tape is an
unrestricted integer position. The simulation therefore has to clamp the outward moves itself.
Reading a blank already means "outside the input", so the finite control only has to remember which
of the two boundaries the head is parked on: a `left | right` flag suffices and the alphabet does
not have to be extended. Note also the off-by-one: the input head starts at position `1`, a work
tape head at `0`, so the correspondence is `inputPos = workPos + 1`.

## Dependencies

```
Deterministic, TapeLemmas
  └── Basic
        ├── Sequential
        ├── LiftTapes
        ├── Clean
        └── TapeContents
              └── OnTape   (also needs Clean)
```

The combinators use only `Sequential`, `LiftTapes`, `Clean`, `TapeContents` and `OnTape`.
