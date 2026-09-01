/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Lookup
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Tape
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.While

/-!
# A universal machine

The pieces assembled. A configuration of the universal machine is the transition table it is
interpreting together with the simulated machine's state and tape. One step looks the current
(state, symbol) pair up in that table — a fold, `Lookup.lookupFn` — and carries out the resulting
instruction — `Simulation.applyInstr`. Running the machine is `Bounds.while` over that step, with
the simulated machine's halting states as the test.

Unlike `Simulation.simStep`, the transition function is *not* fixed: it arrives on the input, so
`Bounds.ofFintype` does not apply to it and the table has to be searched. That search is the only
genuinely new ingredient, and it is a fold.

## The space bound

`uRunBounds` computes `outSize n = n + N n * stepGrowth blank`: linear in the input plus the
number of simulated steps. This is the textbook bound, and it comes out of `Bounds.while`'s
asymmetry — the time bound carries the factor `N`, the space bound does not, because iterations
reuse tapes. The content behind it is `uStep_size_le`: one step grows the configuration by at
most a constant (a new state, a written symbol, and at most one fresh blank cell).

`N` is supplied by the caller, as it must be: bounding the number of steps of the simulated
machine is exactly what a caller doing complexity theory knows and this file cannot.

## No new assumptions

Every certificate here is composed from the primitives and the two loop combinators. The file
introduces no `sorry` of its own.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine Simulation Lookup

namespace Universal

variable {Q S : Type} [DataEncode Q] [DataEncode S] [BEq (Q × S)]

/-- The transition table a universal machine interprets. -/
abbrev UTable (Q S : Type) := Lookup.Table (Q × S) (Instr Q S)

/-- A configuration of the universal machine: the table it is interpreting, together with the
simulated machine's state and tape. -/
abbrev UCfg (Q S : Type) := UTable Q S × Q × Tape S

/-- One step of the universal machine: look the current (state, symbol) pair up in the table being
carried, then carry out the instruction found, or `dflt` if the pair is absent. -/
def uStep (blank : S) (dflt : Instr Q S) (c : UCfg Q S) : UCfg Q S :=
  (c.1, applyInstr blank ((lookupFn (c.1, (c.2.1, read blank c.2.2))).getD dflt, c.2))

/-- The universal machine stops when the simulated state is a halting one. -/
def uHalt (halting : Q → Bool) (c : UCfg Q S) : Bool := halting c.2.1

/-- A certificate for the halting test. -/
def uHaltBounds [Fintype Q] (halting : Q → Bool) : Bounds (uHalt (S := S) halting) :=
  (Bounds.comp (Bounds.ofFintype halting)
    (Bounds.comp Bounds.fst
      Bounds.snd))

/-- **A certificate for one universal step**, composed from the table lookup and the tape
operations. -/
def uStepBounds [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S) :
    Bounds (uStep blank dflt) :=
  let tbl : Bounds (fun c : UCfg Q S => c.1) :=
    Bounds.fst
  let cfg : Bounds (fun c : UCfg Q S => c.2) :=
    Bounds.snd
  let st : Bounds (fun c : UCfg Q S => c.2.1) :=
    (Bounds.comp Bounds.fst cfg)
  let tp : Bounds (fun c : UCfg Q S => c.2.2) :=
    (Bounds.comp Bounds.snd cfg)
  let rd : Bounds (fun c : UCfg Q S => read blank c.2.2) :=
    (Bounds.comp (readBounds blank) tp)
  let look : Bounds (fun c : UCfg Q S => lookupFn (c.1, (c.2.1, read blank c.2.2))) :=
    Bounds.comp' _ lookupBounds (Bounds.pair tbl (Bounds.pair st rd))
  let instr : Bounds (fun c : UCfg Q S =>
      (lookupFn (c.1, (c.2.1, read blank c.2.2))).getD dflt) :=
    (Bounds.comp (Bounds.optionGetD dflt) look)
  (Bounds.pair tbl (Bounds.comp (applyInstrBounds blank) (Bounds.pair instr cfg)))

/-! ### How fast a configuration can grow -/

/-- How much one universal step can grow the encoded configuration: a new state, a written symbol,
and at most one fresh blank cell. All three are bounded by constants of the types. -/
def stepGrowth [Fintype Q] [Fintype S] (blank : S) : ℕ :=
  (Finset.univ.sup fun q : Q => (DataEncode.encode q).size)
    + (Finset.univ.sup fun s : S => (DataEncode.encode s).size)
    + (DataEncode.encode blank).size

/-- **One step grows the configuration by at most a constant.** The table is carried unchanged,
the state is replaced by another element of a finite type, and the tape gains at most the written
symbol and one blank cell. -/
lemma uStep_size_le [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S) (c : UCfg Q S) :
    (DataEncode.encode (uStep blank dflt c)).size
      ≤ (DataEncode.encode c).size + stepGrowth (Q := Q) blank := by
  obtain ⟨tbl, qt⟩ := c
  set i : Instr Q S := (lookupFn (tbl, (qt.1, read blank qt.2))).getD dflt with hi
  have hstep : (DataEncode.encode (uStep blank dflt (tbl, qt))).size
      = (DataEncode.encode tbl).size
        + (DataEncode.encode (applyInstr blank (i, qt))).size + 2 :=
    DataEncode.size_pair _ _
  have hc : (DataEncode.encode ((tbl, qt) : UCfg Q S)).size
      = (DataEncode.encode tbl).size + (DataEncode.encode qt).size + 2 :=
    DataEncode.size_pair _ _
  have hqt : (DataEncode.encode qt).size
      = (DataEncode.encode qt.1).size + (DataEncode.encode qt.2).size + 2 :=
    DataEncode.size_pair _ _
  -- the applied instruction
  have happ : (DataEncode.encode (applyInstr blank (i, qt))).size
      = (DataEncode.encode i.1).size
        + (DataEncode.encode (cond i.2.2
            (moveR blank (write (qt.2, i.2.1))) (moveL blank (write (qt.2, i.2.1))))).size + 2 :=
    DataEncode.size_pair _ _
  have hwrite : (DataEncode.encode (write (qt.2, i.2.1))).size
      ≤ (DataEncode.encode qt.2).size + (DataEncode.encode i.2.1).size :=
    size_write_le (qt.2, i.2.1)
  have hmove : (DataEncode.encode (cond i.2.2
      (moveR blank (write (qt.2, i.2.1))) (moveL blank (write (qt.2, i.2.1))))).size
      ≤ (DataEncode.encode (write (qt.2, i.2.1))).size + (DataEncode.encode blank).size := by
    cases i.2.2
    · simpa using size_moveL_le blank (write (qt.2, i.2.1))
    · simpa using size_moveR_le blank (write (qt.2, i.2.1))
  -- the finite parts
  have hq : (DataEncode.encode i.1).size
      ≤ Finset.univ.sup fun q : Q => (DataEncode.encode q).size :=
    Finset.le_sup (f := fun q : Q => (DataEncode.encode q).size) (Finset.mem_univ _)
  have hs : (DataEncode.encode i.2.1).size
      ≤ Finset.univ.sup fun s : S => (DataEncode.encode s).size :=
    Finset.le_sup (f := fun s : S => (DataEncode.encode s).size) (Finset.mem_univ _)
  unfold stepGrowth
  omega

/-! ### Running to completion -/

/-- **The universal machine run to completion.**

Given `N` bounding the number of steps the simulated machine takes, this computes a certificate
for the whole run. Its `outSize` is `n + N n * stepGrowth blank` — linear in the input plus the
number of simulated steps. -/
def uRunBounds [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S) (halting : Q → Bool)
    (out : UCfg Q S → UCfg Q S) (steps : UCfg Q S → ℕ)
    (h_out : ∀ c, out c = (uStep blank dflt)^[steps c] c)
    (h_halt : ∀ c, uHalt halting ((uStep blank dflt)^[steps c] c) = true)
    (h_first : ∀ c j, j < steps c → uHalt halting ((uStep blank dflt)^[j] c) = false)
    (N : ℕ → ℕ) (hN_mono : Monotone N)
    (hN : ∀ c, steps c ≤ N (DataEncode.encode c).size) :
    Bounds out :=
  Bounds.while Bounds.id
    (uHaltBounds halting) (uStepBounds blank dflt) steps
    h_out h_halt h_first
    N (fun n => n + N n * stepGrowth (Q := Q) blank) hN_mono
    (fun _ _ h => Nat.add_le_add h (Nat.mul_le_mul (hN_mono h) (le_refl _)))
    hN
    (fun c j hj => by
      have h1 := size_iterate_le (f := uStep blank dflt) (stepGrowth (Q := Q) blank)
        (uStep_size_le blank dflt) j c
      have h2 : j * stepGrowth (Q := Q) blank
          ≤ N (DataEncode.encode c).size * stepGrowth (Q := Q) blank :=
        Nat.mul_le_mul_right _ (le_trans hj (hN c))
      simpa using by omega)

/-! ## Variant 1: running under a step budget

Instead of a bound `N` supplied by the caller, the budget arrives *on the input* as a unary list:
the machine takes one step per cell and stops early once the simulated machine halts. This is a
`Bounds.fold` rather than a `Bounds.while` — the trip count is a list — and it needs no
termination hypothesis at all, because the budget makes the run total. -/

/-- One step under a budget: do nothing once the simulated machine has halted. -/
def budgetStep (blank : S) (dflt : Instr Q S) (halting : Q → Bool) (c : UCfg Q S) : UCfg Q S :=
  cond (uHalt halting c) c (uStep blank dflt c)

/-- The list folded over: the step budget, in unary. -/
def budgetList (p : List Unit × UCfg Q S) : List Unit := p.1

/-- The initial accumulator: the configuration to run. -/
def budgetInit (p : List Unit × UCfg Q S) : UCfg Q S := p.2

/-- The fold's step ignores the budget cell; it only supplies a trip count. -/
def budgetFoldStep (blank : S) (dflt : Instr Q S) (halting : Q → Bool)
    (c : UCfg Q S) (_ : Unit) : UCfg Q S :=
  budgetStep blank dflt halting c

omit [DataEncode Q] [DataEncode S] in
/-- **Running under a budget is iterating the budgeted step.** -/
lemma foldFun_budget (blank : S) (dflt : Instr Q S) (halting : Q → Bool)
    (fuel : List Unit) (c : UCfg Q S) :
    foldFun budgetList budgetInit (budgetFoldStep blank dflt halting) (fuel, c)
      = (budgetStep blank dflt halting)^[fuel.length] c :=
  foldl_const_iterate _ _ _

omit [DataEncode Q] [DataEncode S] in
lemma foldAcc_budget (blank : S) (dflt : Instr Q S) (halting : Q → Bool)
    (fuel : List Unit) (c : UCfg Q S) (j : ℕ) :
    foldAcc budgetList budgetInit (budgetFoldStep blank dflt halting) (fuel, c) j
      = (budgetStep blank dflt halting)^[(fuel.take j).length] c :=
  foldl_const_iterate _ _ _

/-- The budgeted step grows the configuration by at most the same constant as a plain step: when
the machine has halted it grows by nothing at all. -/
lemma budgetStep_size_le [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S)
    (halting : Q → Bool) (c : UCfg Q S) :
    (DataEncode.encode (budgetStep blank dflt halting c)).size
      ≤ (DataEncode.encode c).size + stepGrowth (Q := Q) blank := by
  unfold budgetStep
  cases uHalt halting c
  · simpa using uStep_size_le blank dflt c
  · simp

omit [BEq (Q × S)] in
lemma budgetListSize (p : List Unit × UCfg Q S) :
    (DataEncode.encode (budgetList p)).size ≤ (DataEncode.encode p).size := by
  obtain ⟨fuel, c⟩ := p
  have h : (DataEncode.encode ((fuel, c) : List Unit × UCfg Q S)).size
      = (DataEncode.encode fuel).size + (DataEncode.encode c).size + 2 :=
    DataEncode.size_pair _ _
  change (DataEncode.encode fuel).size ≤ _
  omega

/-- **A certificate for a budgeted run.** No termination hypothesis is needed: the budget on the
input bounds the trip count, so the accumulator bound `n + n * stepGrowth blank` follows from the
per-step growth alone. -/
def uRunBudgetBounds [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S)
    (halting : Q → Bool) :
    Bounds (foldFun budgetList budgetInit (budgetFoldStep blank dflt halting)) :=
  Bounds.fold
    (Bounds.fst)
    (Bounds.snd)
    ((Bounds.comp
      (Bounds.ite (uHaltBounds halting) Bounds.id
        (uStepBounds blank dflt))
      Bounds.fst))
    (fun n => n + n * stepGrowth (Q := Q) blank)
    (fun _ _ h => Nat.add_le_add h (Nat.mul_le_mul h (le_refl _)))
    (fun p j => by
      obtain ⟨fuel, c⟩ := p
      rw [foldAcc_budget]
      have hp : (DataEncode.encode ((fuel, c) : List Unit × UCfg Q S)).size
          = (DataEncode.encode fuel).size + (DataEncode.encode c).size + 2 :=
        DataEncode.size_pair _ _
      have hlen := DataEncode.length_le_size fuel
      have h1 := size_iterate_le (f := budgetStep blank dflt halting)
        (stepGrowth (Q := Q) blank) (budgetStep_size_le blank dflt halting)
        (fuel.take j).length c
      have h2 : (fuel.take j).length
          ≤ (DataEncode.encode ((fuel, c) : List Unit × UCfg Q S)).size := by
        rw [List.length_take]
        omega
      have h3 : (fuel.take j).length * stepGrowth (Q := Q) blank
          ≤ (DataEncode.encode ((fuel, c) : List Unit × UCfg Q S)).size
            * stepGrowth (Q := Q) blank :=
        Nat.mul_le_mul_right _ h2
      omega)

/-! ## Variant 2: returning the number of steps

The same loop, but the accumulator carries a counter alongside the configuration, so the result
reports how many steps were taken. The counter is kept in **unary** — a `List Unit` — which is
what makes incrementing it a `Bounds.cons` and so keeps this file free of new assumptions. A
binary counter would need a `Bounds` certificate for `Nat.succ`; `NatSucc` is that example, but
its certificate is a `Prop`-level `PolyTimeLinSpace` and would have to be strengthened to
`Bounds` first. -/

/-- A configuration together with the number of steps taken so far, in unary. -/
abbrev CCfg (Q S : Type) := List Unit × UCfg Q S

/-- The counting step: tick the counter and take one universal step. -/
def countStep (blank : S) (dflt : Instr Q S) (x : CCfg Q S) : CCfg Q S :=
  (() :: x.1, uStep blank dflt x.2)

/-- The counting loop stops exactly when the underlying one does. -/
def countHalt (halting : Q → Bool) (x : CCfg Q S) : Bool := uHalt halting x.2

/-- Start with an empty counter. -/
def countInit (c : UCfg Q S) : CCfg Q S := ([], c)

/-- How much a counting step can grow the encoding: the configuration's growth, plus the two
cells of one more unary tick. -/
def countGrowth [Fintype Q] [Fintype S] (blank : S) : ℕ := stepGrowth (Q := Q) blank + 2

lemma countStep_size_le [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S) (x : CCfg Q S) :
    (DataEncode.encode (countStep blank dflt x)).size
      ≤ (DataEncode.encode x).size + countGrowth (Q := Q) blank := by
  obtain ⟨cnt, c⟩ := x
  have h1 : (DataEncode.encode (countStep blank dflt (cnt, c))).size
      = ((DataEncode.encode (() : Unit)).size + (DataEncode.encode cnt).size)
        + (DataEncode.encode (uStep blank dflt c)).size + 2 := by
    rw [show countStep blank dflt (cnt, c) = (() :: cnt, uStep blank dflt c) from rfl,
      DataEncode.size_pair, DataEncode.size_cons]
  have h2 : (DataEncode.encode ((cnt, c) : CCfg Q S)).size
      = (DataEncode.encode cnt).size + (DataEncode.encode c).size + 2 :=
    DataEncode.size_pair _ _
  have h3 := uStep_size_le blank dflt c
  have h4 := DataEncode.size_unit ()
  unfold countGrowth
  omega

/-- A certificate for the counting step: tick the counter and take one universal step. -/
def countStepBounds [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S) :
    Bounds (countStep blank dflt) :=
  (Bounds.pair
    (Bounds.cons (Bounds.const (() : Unit))
      Bounds.fst)
    (Bounds.comp (uStepBounds blank dflt)
      Bounds.snd))

/-- A certificate for the counting loop's halting test. -/
def countHaltBounds [Fintype Q] (halting : Q → Bool) : Bounds (countHalt (S := S) halting) :=
  (Bounds.comp (uHaltBounds halting)
    Bounds.snd)

/-- A certificate for the counting loop's initial accumulator. -/
def countInitBounds : Bounds (countInit : UCfg Q S → CCfg Q S) :=
  (Bounds.pair (Bounds.const ([] : List Unit))
    Bounds.id)

/-- **A certificate for a run that reports its own step count.** The output is the pair of the
step count, in unary, and the halting configuration. -/
def uRunCountBounds [Fintype Q] [Fintype S] (blank : S) (dflt : Instr Q S) (halting : Q → Bool)
    (out : UCfg Q S → CCfg Q S) (steps : UCfg Q S → ℕ)
    (h_out : ∀ c, out c = (countStep blank dflt)^[steps c] (countInit c))
    (h_halt : ∀ c, countHalt halting ((countStep blank dflt)^[steps c] (countInit c)) = true)
    (h_first : ∀ c j, j < steps c →
      countHalt halting ((countStep blank dflt)^[j] (countInit c)) = false)
    (N : ℕ → ℕ) (hN_mono : Monotone N)
    (hN : ∀ c, steps c ≤ N (DataEncode.encode c).size) :
    Bounds out :=
  Bounds.while countInitBounds (countHaltBounds halting) (countStepBounds blank dflt) steps
    h_out h_halt h_first
    N (fun n => n + 4 + N n * countGrowth (Q := Q) blank) hN_mono
    (fun _ _ h => Nat.add_le_add (Nat.add_le_add h (le_refl 4))
      (Nat.mul_le_mul (hN_mono h) (le_refl _)))
    hN
    (fun c j hj => by
      have hinit : (DataEncode.encode (countInit c)).size
          = (DataEncode.encode ([] : List Unit)).size + (DataEncode.encode c).size + 2 :=
        DataEncode.size_pair _ _
      have hnil : (DataEncode.encode ([] : List Unit)).size = 2 := by
        change (Data.l []).size = 2
        simp [Data.size]
      have h1 := size_iterate_le (f := countStep blank dflt) (countGrowth (Q := Q) blank)
        (countStep_size_le blank dflt) j (countInit c)
      have h2 : j * countGrowth (Q := Q) blank
          ≤ N (DataEncode.encode c).size * countGrowth (Q := Q) blank :=
        Nat.mul_le_mul_right _ (le_trans hj (hN c))
      omega)

end Universal

end MultiTapeTM

end Turing
