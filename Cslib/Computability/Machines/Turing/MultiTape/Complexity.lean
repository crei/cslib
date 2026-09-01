/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Data
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Bounds
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.BoundsAttr
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.BoundsTactic
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.While
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.DepthRec
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Cnf
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Reach
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.ListIndex
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.ListMap
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.ListUpdate
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.NatMul
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Lookup
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.LookupTable
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.MachineDesc
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Tape
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Synthesis
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeView
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeStep
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SimConfig
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SimSpace
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.InputCursor
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SpaceBound
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Universal
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.NatArith

/-!
# Complexity of multi-tape Turing machines (draft)

**STATUS: draft.** Not listed in `Cslib.lean`, because 18 statements are `sorry`-ed. They fall
into exactly two groups:

* **Machine constructions** (17). The `Bounds.computes` field of every primitive in
  `Primitives.lean`, of `Bounds.fold` and of `Bounds.while`, together with
  `ComputableUpTo.comp` and `foldl_computableUpTo`. No concrete multi-tape Turing machine is built
  anywhere in this development, so every one of these is assumed.
* **`ComputableUpTo.absorb`** (1), routine `Nat.pow` arithmetic (proof sketch in its docstring).

Everything else is proved, and the split is checkable with `#print axioms`: the correctness of
every example's fold, all of the size bookkeeping, and the whole simulation stack come out free of
`sorryAx`.

## The main results

* `foldl_computableUpTo` / `Bounds.fold` — the cost of a `List.foldl`, from the cost of its parts.
* `Bounds.while` — the same for unbounded iteration; note the time bound carries the trip count
  and the space bound does not, because iterations reuse tapes.
* `Simulation.simulates` — a finite, *encodable* configuration reproduces a genuine
  `Turing.MultiTapeTM` run, for every number of tapes, alphabet size and state count. `Cfg` itself
  is not encodable: its `workTapes` field is a family of functions `ℤ → Option Symbol`.
* `Simulation.zipper_length_le_spaceUsed` — that simulation's storage is bounded by the simulated
  machine's `spaceUsedByTape`, *not* by its running time.
* `Cnf.formulaSat_polyTimeLinSpace` — **verifying a CNF assignment is polynomial time and linear
  space**, the `SAT ∈ NP` verifier. It takes no hypotheses: the certificate chain behind it rests
  only on the assumed primitives above. Seven of its ten certificates are synthesised by the
  `bounds` tactic; the three that are not are exactly the folds, whose accumulator bounds a tactic
  cannot invent.
* The `bounds` tactic (`Complexity/BoundsTactic.lean`) — synthesises a `Bounds` certificate for a
  Lean function by recursing on its definition, using `@[bounds]`-tagged certificates as leaves.

## Layout

| file | contents |
| --- | --- |
| `Complexity/Data.lean` | the rose-tree type, its size measure and bit encoding |
| `Complexity/Encoding.lean` | `DataEncode` and the encoded-size lemmas |
| `Complexity/Defs.lean` | `DataComputableInTimeAndSpace`, `ComputableUpTo`, `PolyTimeLinSpace` |
| `Complexity/Bounds.lean` | `Bounds`, the resource certificate, and its coarse views |
| `Complexity/Primitives.lean` | the elementary building blocks (machines assumed) |
| `Complexity/Fold.lean` | `foldl_computableUpTo` and `Bounds.fold` |
| `Complexity/While.lean` | `Bounds.while`, unbounded iteration |
| `Complexity/DepthRec.lean` | `Bounds.depthRec`, recursion whose depth depends on the input |
| `Complexity/BoundsAttr.lean`, `BoundsTactic.lean` | `@[bounds]` and the `bounds` tactic |

Worked examples of the fold theorem:

| file | contents |
| --- | --- |
| `Examples/ListIndex.lean`, `ListMap.lean`, `ListUpdate.lean` | indexing, `map`, update |
| `Examples/NatArith.lean`, `NatMul.lean` | `succ`, `add`, `mul` on binary numerals |
| `Examples/Lookup.lean`, `LookupTable.lean` | association-list lookup and its faithfulness |

The simulation stack, culminating in a result about `Turing.MultiTapeTM` itself:

| file | contents |
| --- | --- |
| `Examples/Tape.lean`, `TapeView.lean` | tapes as zippers; `tapeFun`; `Extent` |
| `Examples/TapeStep.lean` | one work-tape action vs `step`'s tape update |
| `Examples/InputCursor.lean` | the input head, including `moveInputPos`'s clamping |
| `Examples/SpaceBound.lean` | discrete IVT; head span ≤ `spaceUsedByTape` |
| `Examples/MachineDesc.lean` | untyped machine descriptions, for any `k`/alphabet/states |
| `Examples/SimConfig.lean` | `SimCfg`, `Represents`, and the step commutation |
| `Examples/SimSpace.lean` | the simulation's storage, bounded by simulated space |
| `Examples/Universal.lean` | a universal machine over encoded transition tables |

## References

* [issue #611, *Plan for complexity theory*](https://github.com/leanprover/cslib/issues/611)
* [issue #590, *Framework for encoding arbitrary types on Turing machines*](https://github.com/leanprover/cslib/issues/590)
-/
