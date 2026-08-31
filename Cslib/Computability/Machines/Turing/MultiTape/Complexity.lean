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
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.While
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.ListIndex
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.ListMap
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.ListUpdate
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.NatMul
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Lookup
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.LookupTable
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.MachineDesc
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Tape
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeView
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeStep
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SimConfig
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.InputCursor
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.SpaceBound
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Universal
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.NatArith

/-!
# Complexity of multi-tape Turing machines (draft)

**STATUS: draft.** Not listed in `Cslib.lean`, because a number of statements are `sorry`-ed. They
fall into exactly two groups:

* **Machine constructions.** `Bounds.computes` for every primitive in `Primitives.lean`,
  `Bounds.fold`, `ComputableUpTo.comp` and `foldl_computableUpTo`. No concrete multi-tape Turing
  machine is built anywhere in this development, so every one of these is assumed.
* **`ComputableUpTo.absorb`**, routine `Nat.pow` arithmetic (proof sketch in its docstring).

Everything else is proved, and the split is checkable with `#print axioms`: the correctness of
each example's fold and all of the size bookkeeping come out free of `sorryAx`.

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
| `Complexity/Examples/` | `List.map`, indexing, `Nat` arithmetic, lookup, a universal machine |

## References

* [issue #611, *Plan for complexity theory*](https://github.com/leanprover/cslib/issues/611)
* [issue #590, *Framework for encoding arbitrary types on Turing machines*](https://github.com/leanprover/cslib/issues/590)
-/
