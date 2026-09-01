/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.BoundsTactic
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Tape
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Lookup

/-!
# Certificates, synthesised

The `bounds` tactic applied to real functions. Each of the tape operations below already has a
hand-written certificate in `Examples/Tape.lean`; here the same certificates are produced from the
function definitions alone.

The last section shows the point of `@[bounds]`: a loop's certificate cannot be synthesised — the
accumulator bound is a human's job — but once proved and registered, the tactic uses it as a leaf
and keeps going through everything built on top.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine Simulation

/-! ### Tape operations, from their definitions -/

example (S : Type) [DataEncode S] : Bounds (Simulation.write : Tape S × S → Tape S) := by bounds

example (S : Type) [DataEncode S] (blank : S) : Bounds (Simulation.moveR blank) := by bounds

example (S : Type) [DataEncode S] (blank : S) : Bounds (Simulation.moveL blank) := by bounds

example (S : Type) [DataEncode S] (blank : S) : Bounds (Simulation.read blank) := by bounds

/-! ### Functions that never had a certificate -/

example (α : Type) [DataEncode α] :
    Bounds (fun p : α × α × α => (p.2.2, (p.1, p.2.1))) := by bounds

example (α : Type) [DataEncode α] :
    Bounds (fun p : Bool × α × α => cond p.1 p.2.1 p.2.2) := by bounds

example (α : Type) [DataEncode α] :
    Bounds (fun p : List α × List α => (p.2.tail, p.1)) := by bounds

/-! ### Registered leaves

`Bounds.isEmpty` is a primitive; registering it lets the tactic resolve applications of
`List.isEmpty`, which it has no structural rule for. -/

attribute [bounds] Bounds.isEmpty

example (α : Type) [DataEncode α] :
    Bounds (fun p : List α × List α => (p.1.isEmpty, p.2.isEmpty)) := by bounds

/-! ### A fold's certificate, registered

`Lookup.lookupBounds` is built with `Bounds.fold`: its accumulator bound is supplied by hand,
which is exactly what a tactic cannot invent. Registering it turns it into a leaf, and everything
built on top is synthesised again. -/

attribute [bounds] Lookup.lookupBounds

example (K V : Type) [DataEncode K] [DataEncode V] [BEq K] [Fintype K] [Fintype V] :
    Bounds (fun p : (Lookup.Table K V × K) × (Lookup.Table K V × K) =>
      (Lookup.lookupFn p.2, Lookup.lookupFn p.1)) := by bounds

end MultiTapeTM

end Turing
