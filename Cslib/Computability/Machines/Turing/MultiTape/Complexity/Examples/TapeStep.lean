/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeView

/-!
# One work-tape action

`MultiTapeTM.step` acts on each work tape by optionally writing under the head and then moving:

```
workTapes i := match (workActions i).1 with
  | none   => cfg.workTapes i
  | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
workTapePos i := cfg.workTapePos i + (workActions i).2
```

`stepTape` is that update, and `applyAction` is the same thing on a finite zipper.
`tapeFun_applyAction` proves the two agree under the denotation of `TapeView` — the work-tape half
of a configuration-level simulation.

The `Extent` lemmas at the end record what the action costs in stored cells: at most one new cell
on the side the head moves towards, and none at all for a write that stays inside the represented
region. That is what keeps a simulation's space tied to the simulated machine's space rather than
to its running time.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace Simulation

variable {S : Type}

/-- The update `MultiTapeTM.step` performs on one work tape: write under the head, or leave the
tape alone. -/
def stepTape (f : ℤ → S) (p : ℤ) (a : Option S) : ℤ → S :=
  match a with
  | none => f
  | some s => Function.update f p s

/-- One work-tape action on a finite zipper: optionally write under the head, then move. -/
def applyAction (blank : S) (a : Option S × SignType) (t : Tape S) : Tape S :=
  let t' := match a.1 with
    | none => t
    | some s => write (t, s)
  match a.2 with
  | .zero => t'
  | .neg => moveL blank t'
  | .pos => moveR blank t'

@[simp] lemma signCast_zero : ((SignType.zero : SignType) : ℤ) = 0 := rfl
@[simp] lemma signCast_neg : ((SignType.neg : SignType) : ℤ) = -1 := rfl
@[simp] lemma signCast_pos : ((SignType.pos : SignType) : ℤ) = 1 := rfl

@[simp] lemma applyAction_none_zero (blank : S) (t : Tape S) :
    applyAction blank (none, SignType.zero) t = t := rfl

@[simp] lemma applyAction_none_neg (blank : S) (t : Tape S) :
    applyAction blank (none, SignType.neg) t = moveL blank t := rfl

@[simp] lemma applyAction_none_pos (blank : S) (t : Tape S) :
    applyAction blank (none, SignType.pos) t = moveR blank t := rfl

@[simp] lemma applyAction_some_zero (blank : S) (s : S) (t : Tape S) :
    applyAction blank (some s, SignType.zero) t = write (t, s) := rfl

@[simp] lemma applyAction_some_neg (blank : S) (s : S) (t : Tape S) :
    applyAction blank (some s, SignType.neg) t = moveL blank (write (t, s)) := rfl

@[simp] lemma applyAction_some_pos (blank : S) (s : S) (t : Tape S) :
    applyAction blank (some s, SignType.pos) t = moveR blank (write (t, s)) := rfl

/-- **A work-tape action on the zipper implements the one `MultiTapeTM.step` performs.** -/
lemma tapeFun_applyAction (blank : S) (a : Option S × SignType) (t : Tape S) (p : ℤ) :
    tapeFun blank (applyAction blank a t) (p + (a.2 : ℤ))
      = stepTape (tapeFun blank t p) p a.1 := by
  obtain ⟨w, m⟩ := a
  cases w with
  | none =>
    cases m with
    | zero => simp [applyAction, stepTape]
    | neg =>
      have : p + (-1 : ℤ) = p - 1 := by ring
      simp only [applyAction, stepTape, signCast_neg, this]
      exact tapeFun_moveL blank t p
    | pos =>
      simp only [applyAction, stepTape, signCast_pos]
      exact tapeFun_moveR blank t p
  | some s =>
    cases m with
    | zero =>
      simp only [applyAction, stepTape, signCast_zero, add_zero]
      exact tapeFun_write blank t p s
    | neg =>
      have h : p + (-1 : ℤ) = p - 1 := by ring
      simp only [applyAction, stepTape, signCast_neg, h]
      rw [tapeFun_moveL blank (write (t, s)) p]
      exact tapeFun_write blank t p s
    | pos =>
      simp only [applyAction, stepTape, signCast_pos]
      rw [tapeFun_moveR blank (write (t, s)) p]
      exact tapeFun_write blank t p s

/-! ### What an action costs in stored cells -/

/-- **One action stores at most one more cell on each side.**

The exact new extent depends on the action — a no-op widens nothing, a write covers the cell under
the head, a move covers the cell it steps onto — so the statement is existential in `lo'` and `hi'`
with the widening bounded. That bound is what keeps a simulation's space proportional to the
simulated machine's space rather than to its running time. -/
lemma Extent.applyAction (blank : S) (a : Option S × SignType) {t : Tape S} {lo p hi : ℤ}
    (h : Extent t lo p hi) :
    ∃ lo' hi', Extent (Simulation.applyAction blank a t) lo' (p + (a.2 : ℤ)) hi'
      ∧ min lo (p - 1) ≤ lo' ∧ lo' ≤ lo ∧ hi ≤ hi' ∧ hi' ≤ max hi (p + 1) := by
  obtain ⟨h1, h2, _, _⟩ := id h
  obtain ⟨w, m⟩ := a
  have hz : p + ((SignType.zero : SignType) : ℤ) = p := by rw [signCast_zero]; ring
  have hn : p + ((SignType.neg : SignType) : ℤ) = p - 1 := by rw [signCast_neg]; ring
  have hp : p + ((SignType.pos : SignType) : ℤ) = p + 1 := by rw [signCast_pos]
  cases w with
  | none =>
    cases m with
    | zero =>
      refine ⟨lo, hi, ?_, by omega, by omega, by omega, by omega⟩
      rw [hz, applyAction_none_zero]
      exact h
    | neg =>
      refine ⟨min lo (p - 1), hi, ?_, by omega, by omega, by omega, by omega⟩
      rw [hn, applyAction_none_neg]
      exact Extent.moveL blank h
    | pos =>
      refine ⟨lo, max hi (p + 1), ?_, by omega, by omega, by omega, by omega⟩
      rw [hp, applyAction_none_pos]
      exact Extent.moveR blank h
  | some s =>
    have hw : Extent (Simulation.write (t, s)) lo p (max hi (p + 1)) := Extent.write s h
    cases m with
    | zero =>
      refine ⟨lo, max hi (p + 1), ?_, by omega, by omega, by omega, by omega⟩
      rw [hz, applyAction_some_zero]
      exact hw
    | neg =>
      refine ⟨min lo (p - 1), max hi (p + 1), ?_, by omega, by omega, by omega, by omega⟩
      rw [hn, applyAction_some_neg]
      exact Extent.moveL blank hw
    | pos =>
      refine ⟨lo, max hi (p + 1), ?_, by omega, by omega, by omega, by omega⟩
      have hm := Extent.moveR blank hw
      have hmax : max (max hi (p + 1)) (p + 1) = max hi (p + 1) := by omega
      rw [hmax] at hm
      rw [hp, applyAction_some_pos]
      exact hm

/-- The stored span grows by at most two cells per action. -/
lemma Extent.applyAction_span {lo p hi lo' hi' : ℤ}
    (h1 : min lo (p - 1) ≤ lo') (h2 : lo' ≤ lo) (h3 : hi ≤ hi') (h4 : hi' ≤ max hi (p + 1))
    (hlo : lo ≤ p) (hhi : p ≤ hi) :
    (hi' - lo').toNat ≤ (hi - lo).toNat + 2 := by
  omega

end Simulation

end MultiTapeTM

end Turing
