/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Tape

/-!
# The zipper really is a Turing machine tape

`Turing.MultiTapeTM.Cfg` stores each work tape as a *function* `ℤ → Option Symbol`, which is not a
finite value and so cannot be encoded on a tape. This file discharges the gap: a zipper together
with a head position denotes such a function, and the finite tape operations of `Simulation`
implement the real ones exactly.

`tapeFun blank t p` is the bi-infinite tape denoted by the zipper `t` with its head at `p`. The
four lemmas below say that under this reading

* `read` is evaluation at the head,
* `write` is `Function.update` at the head — the very operation `MultiTapeTM.step` performs,
* `moveR`/`moveL` shift the head by one and leave the denoted function alone.

That is the "only finitely many cells are used" assumption, discharged rather than assumed: every
configuration reachable from a finite starting tape is denoted by some zipper.

## What this does *not* do

It does not build a universal `MultiTapeTM`. Two things are still missing, and they are of very
different kinds:

1. **Configuration-level simulation.** Lifting these lemmas from one tape to a whole
   `MultiTapeTM.Cfg` — `k` work tapes (a `Fin k`-indexed family, so its finite stand-in is a
   vector), the input head's `Fin (n + 2)` position, and the output list — and proving the finite
   step commutes with `MultiTapeTM.step`. This is ordinary work: provable, just long.
2. **Existence of the machine.** A statement of the form "there is a `MultiTapeTM` that simulates
   every `MultiTapeTM`" cannot be proved from anything in this development, because *no* concrete
   multi-tape machine is constructed anywhere in it. It reduces to the same assumed primitives as
   every other example — see the status note in `Complexity.lean`. Building one is the real
   remaining task, and nothing here shortens it.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine Simulation

namespace Simulation

variable {S : Type}

/-- The bi-infinite tape denoted by a zipper whose head sits at position `p`: the first component
holds the cells strictly left of `p`, nearest first, and the second the cells from `p` rightwards.
Everything beyond either end reads as `blank`. -/
def tapeFun (blank : S) (t : Tape S) (p : ℤ) : ℤ → S := fun z =>
  if z < p then (t.1[(p - z - 1).toNat]?).getD blank
  else (t.2[(z - p).toNat]?).getD blank

/-- Reading the zipper is evaluating the denoted tape at the head. -/
@[simp]
lemma tapeFun_self (blank : S) (t : Tape S) (p : ℤ) :
    tapeFun blank t p p = read blank t := by
  simp [tapeFun, read, List.head?_eq_getElem?]

/-- Writing to the zipper is `Function.update` of the denoted tape at the head — which is exactly
what `MultiTapeTM.step` does to `Cfg.workTapes`. -/
lemma tapeFun_write (blank : S) (t : Tape S) (p : ℤ) (s : S) :
    tapeFun blank (write (t, s)) p = Function.update (tapeFun blank t p) p s := by
  funext z
  rcases lt_trichotomy z p with h | h | h
  · have hne : z ≠ p := by omega
    simp [tapeFun, write, hne, h]
  · subst h
    simp [tapeFun, write]
  · have hne : z ≠ p := by omega
    have hz : ¬ z < p := by omega
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (z - p).toNat = n + 1 := ⟨(z - p).toNat - 1, by omega⟩
    simp [tapeFun, write, hne, hz, hn, List.getElem?_tail]

/-- Moving the head right shifts the position and leaves the denoted tape unchanged. -/
lemma tapeFun_moveR (blank : S) (t : Tape S) (p : ℤ) :
    tapeFun blank (moveR blank t) (p + 1) = tapeFun blank t p := by
  funext z
  rcases lt_trichotomy z p with h | h | h
  · have h1 : z < p + 1 := by omega
    have h2 : (p + 1 - z - 1).toNat = (p - z - 1).toNat + 1 := by omega
    simp [tapeFun, moveR, h, h1, h2]
  · subst h
    have h1 : z < z + 1 := by omega
    simp [tapeFun, moveR, h1, List.head?_eq_getElem?]
  · have h1 : ¬ z < p := by omega
    have h2 : ¬ z < p + 1 := by omega
    have h3 : (z - p).toNat = (z - (p + 1)).toNat + 1 := by omega
    simp [tapeFun, moveR, h1, h2, h3, List.getElem?_tail]

/-- Moving the head left shifts the position and leaves the denoted tape unchanged. -/
lemma tapeFun_moveL (blank : S) (t : Tape S) (p : ℤ) :
    tapeFun blank (moveL blank t) (p - 1) = tapeFun blank t p := by
  funext z
  rcases lt_trichotomy z (p - 1) with h | h | h
  · have h1 : z < p := by omega
    have h3 : (p - z - 1).toNat = (p - 1 - z - 1).toNat + 1 := by omega
    simp [tapeFun, moveL, h, h1, h3, List.getElem?_tail]
  · have h1 : ¬ z < p - 1 := by omega
    have h2 : z < p := by omega
    have h3 : (z - (p - 1)).toNat = 0 := by omega
    have h4 : (p - z - 1).toNat = 0 := by omega
    simp [tapeFun, moveL, h1, h2, h3, h4, List.head?_eq_getElem?]
  · have h1 : ¬ z < p - 1 := by omega
    have h2 : ¬ z < p := by omega
    have h3 : (z - (p - 1)).toNat = (z - p).toNat + 1 := by omega
    simp [tapeFun, moveL, h1, h2, h3]

/-! ### How wide a zipper gets

A simulation's space bound should be the simulated machine's *space*, not its running time.
`Extent` is what makes that possible: a zipper stores exactly the cells spanned by the positions
its head has occupied, so it grows only when the head reaches ground it has not been on before.
Contrast the crude bound in `Universal`, where the accumulator is charged one growth per step.
-/

/-- `Extent t lo p hi` says the zipper `t` has its head at `p` and stores exactly the cells from
`lo` to `hi` inclusive. -/
def Extent (t : Tape S) (lo p hi : ℤ) : Prop :=
  lo ≤ p ∧ p ≤ hi ∧ t.1.length = (p - lo).toNat ∧ t.2.length = (hi - p).toNat

/-- A fresh zipper covers the single cell under the head. -/
lemma Extent.init : Extent (([], []) : Tape S) 0 0 0 := by
  refine ⟨le_refl _, le_refl _, ?_, ?_⟩ <;> simp

/-- **The number of cells a zipper stores is the span of its extent** — not the number of steps
taken to get there. -/
lemma Extent.length_eq {t : Tape S} {lo p hi : ℤ} (h : Extent t lo p hi) :
    t.1.length + t.2.length = (hi - lo).toNat := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- Moving right extends the span only if the head was already at its right edge. -/
lemma Extent.moveR (blank : S) {t : Tape S} {lo p hi : ℤ} (h : Extent t lo p hi) :
    Extent (Simulation.moveR blank t) lo (p + 1) (max hi (p + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have e : (Simulation.moveR blank t).1.length = t.1.length + 1 := by simp [Simulation.moveR]
    omega
  · cases hr : t.2 with
    | nil =>
      have e : (Simulation.moveR blank t).2.length = 0 := by simp [Simulation.moveR, hr]
      rw [hr] at h4
      simp only [List.length_nil] at h4
      omega
    | cons x rest =>
      have e : (Simulation.moveR blank t).2.length = rest.length := by simp [Simulation.moveR, hr]
      rw [hr] at h4
      simp only [List.length_cons] at h4
      omega

/-- Moving left extends the span only if the head was already at its left edge. -/
lemma Extent.moveL (blank : S) {t : Tape S} {lo p hi : ℤ} (h : Extent t lo p hi) :
    Extent (Simulation.moveL blank t) (min lo (p - 1)) (p - 1) hi := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, ?_, ?_⟩
  · cases hl : t.1 with
    | nil =>
      have e : (Simulation.moveL blank t).1.length = 0 := by simp [Simulation.moveL, hl]
      rw [hl] at h3
      simp only [List.length_nil] at h3
      omega
    | cons x l' =>
      have e : (Simulation.moveL blank t).1.length = l'.length := by simp [Simulation.moveL, hl]
      rw [hl] at h3
      simp only [List.length_cons] at h3
      omega
  · have e : (Simulation.moveL blank t).2.length = t.2.length + 1 := by simp [Simulation.moveL]
    omega

/-- Writing materialises the cell under the head, so it extends the span by at most that one
cell — and never by more, however long the machine runs. -/
lemma Extent.write {t : Tape S} {lo p hi : ℤ} (s : S) (h : Extent t lo p hi) :
    Extent (Simulation.write (t, s)) lo p (max hi (p + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have e : (Simulation.write ((t, s) : Tape S × S)).1.length
        = t.1.length := by simp [Simulation.write]
    omega
  · cases hr : t.2 with
    | nil =>
      have e : (Simulation.write ((t, s) : Tape S × S)).2.length = 1 := by
        simp [Simulation.write, hr]
      rw [hr] at h4
      simp only [List.length_nil] at h4
      omega
    | cons x rest =>
      have e : (Simulation.write ((t, s) : Tape S × S)).2.length
          = rest.length + 1 := by simp [Simulation.write, hr]
      rw [hr] at h4
      simp only [List.length_cons] at h4
      omega

/-! ### The shape `MultiTapeTM.Cfg` expects -/

/-- A finite stand-in for one work tape of `Turing.MultiTapeTM.Cfg`: a zipper together with the
head position. `workTapeFun` turns it into exactly the `ℤ → Option Symbol` that
`Cfg.workTapes i` is. -/
abbrev WorkTape (Symbol : Type) := Tape (Option Symbol) × ℤ

/-- The bi-infinite work tape denoted by a finite stand-in. -/
def workTapeFun {Symbol : Type} (w : WorkTape Symbol) : ℤ → Option Symbol :=
  tapeFun none w.1 w.2

/-- **A real `MultiTapeTM.Cfg` built entirely from finite data.**

Every field of `Cfg` except `workTapes` is already a finite value — an `Option State`, a
`Fin (n + 2)`, a `List Symbol`. Only the work tapes are functions, and `workTapeFun` supplies
them from zippers. So a configuration of a genuine multi-tape machine *is* encodable, and this
definition is the witness. -/
def toCfg {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (state : Option State) (inputPos : Fin (input.length + 2))
    (ws : Fin k → WorkTape Symbol) (output : List Symbol) :
    Cfg k Symbol State input where
  state := state
  inputPos := inputPos
  workTapes i := workTapeFun (ws i)
  workTapePos i := (ws i).2
  output := output

@[simp]
lemma toCfg_workTapes {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (state : Option State) (inputPos : Fin (input.length + 2))
    (ws : Fin k → WorkTape Symbol) (output : List Symbol) (i : Fin k) :
    (toCfg (State := State) (input := input) state inputPos ws output).workTapes i
      = tapeFun none (ws i).1 (ws i).2 := rfl

/-- Under the denotation, reading a work tape of the built configuration is reading the zipper —
`Cfg.workTapeSymbols` agrees with `Simulation.read`. -/
lemma toCfg_workTapeSymbols {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (state : Option State) (inputPos : Fin (input.length + 2))
    (ws : Fin k → WorkTape Symbol) (output : List Symbol) (i : Fin k) :
    (toCfg (State := State) (input := input) state inputPos ws output).workTapeSymbols i
      = read none (ws i).1 := by
  simp [Cfg.workTapeSymbols, toCfg, workTapeFun]

end Simulation

end MultiTapeTM

end Turing
