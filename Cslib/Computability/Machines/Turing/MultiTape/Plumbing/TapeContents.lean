/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic

/-!
# The contents of a work tape

This file provides the vocabulary for talking about the contents of a single work tape, and the
machines that manipulate it: clearing a tape, moving the contents of one tape to another, and
branching on the symbol under a tape head.

## Main definitions

* `Turing.MultiTapeTM.TapeHolds`: work tape `i` contains the word `w` starting at position `0`,
  is blank everywhere else, and its head is at position `0`. Note that `TapeHolds i []` says that
  the tape is blank with its head at position `0`.

## Main results

* `Turing.MultiTapeTM.exists_clearTape`: a tape can be blanked in time linear in its contents.
* `Turing.MultiTapeTM.exists_moveTapeTail`: the contents of a tape, without its first symbol, can
  be moved to a blank tape in time linear in its contents.
* `Turing.MultiTapeTM.exists_branchOnTape`: two machines can be combined into one that behaves like
  the first one if the head of a given tape reads a given symbol, and like the second one
  otherwise.

Since the contents of a tape are a `List Symbol`, they are blank-free, so the machines can find the
end of the contents by scanning for the first blank.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State₁ State₂ : Type*} {input : List Symbol}

/-- Work tape `i` of `cfg` holds the word `w`: the cells `0, …, w.length - 1` contain the symbols
of `w`, all other cells are blank, and the head is at position `0`. -/
public def TapeHolds (i : Fin k) (w : List Symbol) (cfg : Cfg k Symbol State input) : Prop :=
  (∀ (j : ℕ) (h : j < w.length), cfg.workTapes i (j : ℤ) = some (w[j]'h)) ∧
  (∀ z : ℤ, z < 0 ∨ (w.length : ℤ) ≤ z → cfg.workTapes i z = none) ∧
  cfg.workTapePos i = 0

/-- **Clearing a tape.** There is a machine that blanks a work tape and returns its head to
position `0`, in time linear in the contents of the tape. -/
proof_wanted exists_clearTape (i : Fin k) :
    ∃ (c : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Symbol State),
      ∀ w : List Symbol, TransformsCfg tm {i}
        (fun _ tp => TapeHolds i w tp) (fun _ _ tp' => TapeHolds i [] tp')
        (c * (w.length + 1)) (w.length + 1)

/-- **Moving the tail of a tape to another tape.** There is a machine that moves the contents of
tape `src`, without its first symbol, to the blank tape `dst`, clearing `src`, in time linear in
the contents of `src`. -/
proof_wanted exists_moveTapeTail {src dst : Fin k} (h : src ≠ dst) :
    ∃ (c : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Symbol State),
      ∀ (x : Symbol) (w : List Symbol), TransformsCfg tm {src, dst}
        (fun _ tp => TapeHolds src (x :: w) tp ∧ TapeHolds dst [] tp)
        (fun _ _ tp' => TapeHolds src [] tp' ∧ TapeHolds dst w tp')
        (c * (w.length + 1)) (w.length + 2)

/-- **Branching on the symbol under a tape head.** Two machines performing the same transformation
under different preconditions can be combined into a machine that behaves like the first one if the
head of tape `i` reads `x`, and like the second one otherwise. The combined machine needs one extra
step to read the symbol.

This is the only place where a branch is taken on the contents of a tape. Its function-level face
is `computableInTimeAndSpace_ite`, which is what should be used everywhere; the branch itself is
needed here only because the loop combinator branches between continuing the loop and leaving it,
which is not a choice between two functions. -/
proof_wanted exists_branchOnTape [DecidableEq Symbol] (i : Fin k) (x : Symbol)
    {tm₁ : MultiTapeTM k Symbol State₁} {tm₂ : MultiTapeTM k Symbol State₂} {S : Finset (Fin k)}
    {P₁ P₂ : (input : List Symbol) → Tapes k Symbol input → Prop}
    {Q : (input : List Symbol) → Tapes k Symbol input → Tapes k Symbol input → Prop}
    {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : TransformsCfg tm₁ S P₁ Q t₁ s₁) (h₂ : TransformsCfg tm₂ S P₂ Q t₂ s₂) :
    ∃ tm : MultiTapeTM k Symbol (Unit ⊕ State₁ ⊕ State₂), TransformsCfg tm S
      (fun input tp => if tp.workTapeSymbols i = some x then P₁ input tp else P₂ input tp) Q
      (max t₁ t₂ + 1) (max s₁ s₂)

end Turing.MultiTapeTM
