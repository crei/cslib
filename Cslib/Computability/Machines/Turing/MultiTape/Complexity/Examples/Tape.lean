/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives

/-!
# Towards a universal machine: tapes and one simulated step

A first step towards costing a universal machine: represent the tape of the *simulated* machine,
and give resource certificates for the tape operations and for one step of the simulation.

## The tape

A tape is a zipper: `Tape S = List S × List S`, the cells strictly left of the head in reverse
order, and the cells from the head rightwards. Cells beyond either end are the blank symbol, so
only finitely many cells are ever represented and a tape is an ordinary finite value. It therefore
**inherits `DataEncode` from the `List` and `Prod` instances with no new instance and no new
assumption** — which is the point of choosing a zipper over, say, a function `ℤ → S`.

## What is proved here

Everything in this file is *derived*: `read`, `write`, `moveL`, `moveR` and finally `simStep` all
get their certificates by composing `Bounds.fst`, `Bounds.snd`, `Bounds.cons`, `Bounds.pair`,
`Bounds.comp`, `Bounds.headD`, `Bounds.tail`, `Bounds.ite` and `Bounds.ofFintype`. **No new `sorry`
is introduced.** One step of a simulated single-tape machine costs no more than the primitives it
is built from, and the bound is computed rather than asserted.

## Where this leads

`simStep` takes its transition function as a *fixed* function on finite types, so
`Bounds.ofFintype` covers it. A genuinely universal machine reads its transition table off the
input instead; that search is `Examples/Lookup.lean`, and the machine built on it is
`Examples/Universal.lean`. What remains missing is only the machines themselves — see the status
note in `Complexity.lean`.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

namespace Simulation

variable {S Q : Type} [DataEncode S] [DataEncode Q]

/-- The tape of a simulated machine, as a zipper: the cells strictly left of the head in reverse
order, and the cells from the head rightwards. Everything beyond either end is blank, so only
finitely many cells are represented. -/
abbrev Tape (S : Type) := List S × List S

/-- The symbol under the head. -/
def read (blank : S) (t : Tape S) : S := t.2.head?.getD blank

/-- Overwrite the symbol under the head. -/
def write (p : Tape S × S) : Tape S := (p.1.1, p.2 :: p.1.2.tail)

/-- Move the head one cell to the right. -/
def moveR (blank : S) (t : Tape S) : Tape S := (t.2.head?.getD blank :: t.1, t.2.tail)

/-- Move the head one cell to the left. -/
def moveL (blank : S) (t : Tape S) : Tape S := (t.1.tail, t.1.head?.getD blank :: t.2)

/-! ### Certificates for the tape operations, derived from the primitives -/

/-- Reading is the head of the right-hand list. -/
def readBounds (blank : S) : Bounds (read (S := S) blank) :=
  (Bounds.comp (Bounds.headD blank) Bounds.snd).congr rfl

/-- Writing replaces the head of the right-hand list. -/
def writeBounds : Bounds (write : Tape S × S → Tape S) :=
  (Bounds.pair (Bounds.comp Bounds.fst Bounds.fst)
    (Bounds.cons Bounds.snd (Bounds.comp Bounds.tail (Bounds.comp Bounds.snd Bounds.fst)))).congr
    rfl

/-- Moving right pops the right-hand list and pushes onto the left-hand one. -/
def moveRBounds (blank : S) : Bounds (moveR (S := S) blank) :=
  (Bounds.pair (Bounds.cons (Bounds.comp (Bounds.headD blank) Bounds.snd) Bounds.fst)
    (Bounds.comp Bounds.tail Bounds.snd)).congr rfl

/-- Moving left pops the left-hand list and pushes onto the right-hand one. -/
def moveLBounds (blank : S) : Bounds (moveL (S := S) blank) :=
  (Bounds.pair (Bounds.comp Bounds.tail Bounds.fst)
    (Bounds.cons (Bounds.comp (Bounds.headD blank) Bounds.fst) Bounds.snd)).congr rfl

/-! ### How much the tape can grow

One step changes the tape by a bounded amount. These are the lemmas the universal machine's space
bound is built from: writing costs at most the written symbol, and a move costs at most one blank
(only when the head runs off the represented part of the tape). -/

lemma size_write_le (p : Tape S × S) :
    (DataEncode.encode (write p)).size
      ≤ (DataEncode.encode p.1).size + (DataEncode.encode p.2).size := by
  obtain ⟨⟨l, r⟩, s⟩ := p
  have h1 : (DataEncode.encode (write ((l, r), s))).size
      = (DataEncode.encode l).size + ((DataEncode.encode s).size
        + (DataEncode.encode r.tail).size) + 2 := by
    rw [show write ((l, r), s) = (l, s :: r.tail) from rfl, DataEncode.size_pair,
      DataEncode.size_cons]
  have h2 : (DataEncode.encode ((l, r) : Tape S)).size
      = (DataEncode.encode l).size + (DataEncode.encode r).size + 2 := DataEncode.size_pair _ _
  have h3 := DataEncode.size_tail_le r
  simp only []
  omega

lemma size_moveR_le (blank : S) (t : Tape S) :
    (DataEncode.encode (moveR blank t)).size
      ≤ (DataEncode.encode t).size + (DataEncode.encode blank).size := by
  obtain ⟨l, r⟩ := t
  have h2 : (DataEncode.encode ((l, r) : Tape S)).size
      = (DataEncode.encode l).size + (DataEncode.encode r).size + 2 := DataEncode.size_pair _ _
  cases r with
  | nil =>
    have h1 : (DataEncode.encode (moveR blank ((l, []) : Tape S))).size
        = ((DataEncode.encode blank).size + (DataEncode.encode l).size)
          + (DataEncode.encode ([] : List S)).size + 2 := by
      rw [show moveR blank ((l, []) : Tape S) = (blank :: l, []) from rfl,
        DataEncode.size_pair, DataEncode.size_cons]
    omega
  | cons x xs =>
    have h1 : (DataEncode.encode (moveR blank ((l, x :: xs) : Tape S))).size
        = ((DataEncode.encode x).size + (DataEncode.encode l).size)
          + (DataEncode.encode xs).size + 2 := by
      rw [show moveR blank ((l, x :: xs) : Tape S) = (x :: l, xs) from rfl,
        DataEncode.size_pair, DataEncode.size_cons]
    have h4 := DataEncode.size_cons x xs
    omega

lemma size_moveL_le (blank : S) (t : Tape S) :
    (DataEncode.encode (moveL blank t)).size
      ≤ (DataEncode.encode t).size + (DataEncode.encode blank).size := by
  obtain ⟨l, r⟩ := t
  have h2 : (DataEncode.encode ((l, r) : Tape S)).size
      = (DataEncode.encode l).size + (DataEncode.encode r).size + 2 := DataEncode.size_pair _ _
  cases l with
  | nil =>
    have h1 : (DataEncode.encode (moveL blank (([], r) : Tape S))).size
        = (DataEncode.encode ([] : List S)).size
          + ((DataEncode.encode blank).size + (DataEncode.encode r).size) + 2 := by
      rw [show moveL blank (([], r) : Tape S) = ([], blank :: r) from rfl,
        DataEncode.size_pair, DataEncode.size_cons]
    omega
  | cons x xs =>
    have h1 : (DataEncode.encode (moveL blank ((x :: xs, r) : Tape S))).size
        = (DataEncode.encode xs).size
          + ((DataEncode.encode x).size + (DataEncode.encode r).size) + 2 := by
      rw [show moveL blank ((x :: xs, r) : Tape S) = (xs, x :: r) from rfl,
        DataEncode.size_pair, DataEncode.size_cons]
    have h4 := DataEncode.size_cons x xs
    omega

/-! ### Carrying out an instruction -/

/-- The instruction a transition produces: the new state, the symbol to write, and the direction
to move (`true` for right). -/
abbrev Instr (Q S : Type) := Q × S × Bool

/-- Carry out an instruction on a configuration: adopt the new state, write the symbol under the
head, and move. Factored out of `simStep` so that the universal machine, whose instruction comes
from a table lookup rather than a fixed function, can reuse it. -/
def applyInstr (blank : S) (p : Instr Q S × (Q × Tape S)) : Q × Tape S :=
  (p.1.1,
    cond p.1.2.2
      (moveR blank (write (p.2.2, p.1.2.1)))
      (moveL blank (write (p.2.2, p.1.2.1))))

/-- A certificate for `applyInstr`, composed from the tape operations and `Bounds.ite`. -/
def applyInstrBounds (blank : S) : Bounds (applyInstr (Q := Q) blank) :=
  let i : Bounds (fun p : Instr Q S × (Q × Tape S) => p.1) := Bounds.fst
  let st : Bounds (fun p : Instr Q S × (Q × Tape S) => p.1.1) :=
    (Bounds.comp (Bounds.fst : Bounds (Prod.fst : Instr Q S → Q)) i).congr rfl
  let sym : Bounds (fun p : Instr Q S × (Q × Tape S) => p.1.2.1) :=
    (Bounds.comp (Bounds.comp (Bounds.fst : Bounds (Prod.fst : S × Bool → S))
      (Bounds.snd : Bounds (Prod.snd : Instr Q S → S × Bool))) i).congr rfl
  let dir : Bounds (fun p : Instr Q S × (Q × Tape S) => p.1.2.2) :=
    (Bounds.comp (Bounds.comp (Bounds.snd : Bounds (Prod.snd : S × Bool → Bool))
      (Bounds.snd : Bounds (Prod.snd : Instr Q S → S × Bool))) i).congr rfl
  let tp : Bounds (fun p : Instr Q S × (Q × Tape S) => p.2.2) :=
    (Bounds.comp (Bounds.snd : Bounds (Prod.snd : Q × Tape S → Tape S))
      (Bounds.snd : Bounds (Prod.snd : Instr Q S × (Q × Tape S) → Q × Tape S))).congr rfl
  let written : Bounds (fun p : Instr Q S × (Q × Tape S) => write (p.2.2, p.1.2.1)) :=
    (Bounds.comp writeBounds (Bounds.pair tp sym)).congr rfl
  (Bounds.pair st
    (Bounds.ite dir
      (Bounds.comp (moveRBounds blank) written)
      (Bounds.comp (moveLBounds blank) written))).congr rfl

/-! ### One step of a simulated machine with a fixed transition function -/

/-- One step of a simulated single-tape machine with transition function `tr`. -/
def simStep (blank : S) (tr : Q × S → Instr Q S) (c : Q × Tape S) : Q × Tape S :=
  applyInstr blank (tr (c.1, read blank c.2), c)

/-- **A resource certificate for one simulated step**, composed entirely from the primitives:
`ofFintype` for the transition, the tape operations for the rest. Nothing new is assumed. -/
def simStepBounds [Fintype Q] [Fintype S] (blank : S) (tr : Q × S → Instr Q S) :
    Bounds (simStep blank tr) :=
  let rd : Bounds (fun c : Q × Tape S => read blank c.2) :=
    (Bounds.comp (readBounds blank)
      (Bounds.snd : Bounds (Prod.snd : Q × Tape S → Tape S))).congr rfl
  let instr : Bounds (fun c : Q × Tape S => tr (c.1, read blank c.2)) :=
    (Bounds.comp (Bounds.ofFintype tr)
      (Bounds.pair (Bounds.fst : Bounds (Prod.fst : Q × Tape S → Q)) rd)).congr rfl
  (Bounds.comp (applyInstrBounds blank)
    (Bounds.pair instr (Bounds.id : Bounds (id : Q × Tape S → Q × Tape S)))).congr rfl

end Simulation

end MultiTapeTM

end Turing
