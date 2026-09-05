/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Clean
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.LiftTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OnTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeContents

/-!
# Machines as transformers of tape words

This file is the interface the combinators use. A combinator never talks about individual cells,
head positions or the set of tapes a machine has touched: it composes machines that read words
from some work tapes and write words to others.

`TransformsTapes` is `TransformsCfg` specialised to configurations in which *every* work tape
holds a word (`TapesHold`), the input head sits at position `1` and the output is left unchanged.
The specialisation is what makes the combinators cheap to assemble:

* the tapes a machine did not touch are described by the postcondition (`ws' l = ws l`) instead of
  by a set of tape indices, so `Cfg.AgreesOutside` disappears;
* the input head and the output are normalised, so sequential composition needs no side
  conditions;
* the configuration is determined by the words on the tapes, so two machines can be composed by
  reasoning about words only.

The bounds `t` and `s` are numbers, as in `TransformsCfg`; a specification whose bounds depend on
the data is a *family* `∀ j, TransformsTapes tm (P j) (Q j) (t j) (s j)` over one fixed machine.
This is why `exists_transformsTapes_branch` and `exists_transformsTapes_repeat` are stated over an
arbitrary index type: the machine has to be built once and specified once per index.

## Scratch tapes

A machine that is run inside a bigger machine needs work tapes of its own. Rather than exposing
them, the results here quantify over the ambient number of tapes: `∃ m c, ∀ k i o keep, …` says
that `m` scratch tapes suffice, so the caller may use *any* machine with enough tapes, designating
an input tape `i`, an output tape `o` and a set `keep` of tapes that have to survive the call. All
tapes outside `keep` are blank before and after; which of them the machine uses is not observable.

## Main definitions

* `Turing.MultiTapeTM.TapesHold`: every work tape holds a given word.
* `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.transformsTapes_seq`: sequential composition.
* `Turing.MultiTapeTM.exists_transformsTapes_branch`: branching on the first symbol of a tape.
* `Turing.MultiTapeTM.exists_transformsTapes_repeat`: repeating a machine until the first symbol
  of a tape signals that the loop is over. This is the loop-back that `seq` cannot express, and
  the only reason the loop combinator needs the machine level at all.
* `Turing.MultiTapeTM.exists_transformsTapes_nop` and
  `Turing.MultiTapeTM.exists_transformsTapes_clear`:
  the two trivial machines.
* `Turing.MultiTapeTM.exists_transformsTapes_ofComputable`,
  `Turing.MultiTapeTM.exists_transformsTapes_ofComputableInput`: evaluating a computable function
  on work tapes, reading its argument from a work tape resp. from the real input tape.
* `Turing.MultiTapeTM.computableInTimeAndSpace_of_transformsTapes`: emitting a work tape as the
  output, which turns a tape transformation back into a computation.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Every work tape of `cfg` holds a word: tape `i` contains `ws i` starting at position `0`, is
blank everywhere else, and its head is at position `0`. -/
public def TapesHold (ws : Fin k → List Symbol) (cfg : Cfg k Symbol State input) : Prop :=
  ∀ i, TapeHolds i (ws i) cfg

/-- `TransformsTapes tm P Q t s` states that, started in its initial state from a configuration
whose input head is at position `1` and whose work tapes hold words `ws` satisfying `P`, the
machine `tm` halts after at most `t` steps and using at most `s` space, in a configuration whose
work tapes hold words `ws'` with `Q input ws ws'`, whose input head is again at position `1` and
whose output is unchanged. -/
public def TransformsTapes (tm : MultiTapeTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (cfg : Cfg k Symbol State input),
    cfg.state = some tm.q₀ → cfg.inputPos = 1 → TapesHold ws cfg → P input ws →
      ∃ τ ≤ t, ∃ ws', (tm.runFrom cfg τ).state = none ∧
        Q input ws ws' ∧
        TapesHold ws' (tm.runFrom cfg τ) ∧
        (tm.runFrom cfg τ).inputPos = 1 ∧
        (tm.runFrom cfg τ).output = cfg.output ∧
        tm.spaceUsed cfg τ ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws', P' input ws → Q input ws ws' → Q' input ws ws')
    (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P' Q' t' s' := by
  intro input ws cfg hstate hpos hholds hP'
  obtain ⟨τ, hτ, ws', hhalt, hQ', hholds', hpos', hout, hspace⟩ :=
    h input ws cfg hstate hpos hholds (hP input ws hP')
  exact ⟨τ, hτ.trans ht, ws', hhalt, hQ input ws ws' hP' hQ', hholds', hpos', hout,
    hspace.trans hs⟩

/-- **Sequential composition.** `seq tm₁ tm₂` performs the transformation of `tm₁` and then the one
of `tm₂`, provided the postcondition of `tm₁` implies the precondition of `tm₂`. -/
theorem transformsTapes_seq {State₁ State₂ : Type*}
    {tm₁ : MultiTapeTM k Symbol State₁} {tm₂ : MultiTapeTM k Symbol State₂}
    {P₁ P₂ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₁ Q₂ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : TransformsTapes tm₁ P₁ Q₁ t₁ s₁) (h₂ : TransformsTapes tm₂ P₂ Q₂ t₂ s₂)
    (hmid : ∀ input ws ws', P₁ input ws → Q₁ input ws ws' → P₂ input ws') :
    TransformsTapes (tm₁.seq tm₂) P₁
      (fun input ws ws'' => ∃ ws', Q₁ input ws ws' ∧ Q₂ input ws' ws'') (t₁ + t₂) (s₁ + s₂) :=
  sorry

/-- **The machine that does nothing.** It halts in one step, leaving every tape as it was. -/
theorem exists_transformsTapes_nop (k : ℕ) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      TransformsTapes tm (fun _ _ => True) (fun _ ws ws' => ws' = ws) 1 k :=
  sorry

/-- **Clearing a tape.** A work tape can be blanked and rewound in time linear in its contents,
leaving all other tapes untouched. -/
theorem exists_transformsTapes_clear {k : ℕ} (i : Fin k) :
    ∃ (c : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ w : List Bool,
      TransformsTapes tm (fun _ ws => ws i = w)
        (fun _ ws ws' => ws' i = [] ∧ ∀ l ≠ i, ws' l = ws l)
        (c * (w.length + 1)) (w.length + 1 + k) :=
  sorry

/-- **Branching on the first symbol of a tape.** Two machines performing transformations with the
same postcondition can be combined into a machine that behaves like the first one if tape `i`
starts with the symbol `x`, and like the second one otherwise. One step is spent reading the
symbol.

The specifications are families over an arbitrary index type, since a single machine has to be
specified once for every value its bounds depend on. -/
theorem exists_transformsTapes_branch {J : Type*} {k : ℕ} (i : Fin k) (x : Bool)
    {State₁ State₂ : Type} [Finite State₁] [Finite State₂]
    {tm₁ : MultiTapeTM k Bool State₁} {tm₂ : MultiTapeTM k Bool State₂}
    {P₁ P₂ : J → (input : List Bool) → (Fin k → List Bool) → Prop}
    {Q : J → (input : List Bool) → (Fin k → List Bool) → (Fin k → List Bool) → Prop}
    {t₁ s₁ t₂ s₂ : J → ℕ}
    (h₁ : ∀ j, TransformsTapes tm₁ (P₁ j) (Q j) (t₁ j) (s₁ j))
    (h₂ : ∀ j, TransformsTapes tm₂ (P₂ j) (Q j) (t₂ j) (s₂ j)) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ j : J,
      TransformsTapes tm
        (fun input ws => if (ws i).head? = some x then P₁ j input ws else P₂ j input ws)
        (Q j) (max (t₁ j) (t₂ j) + 1) (max (s₁ j) (s₂ j) + k) :=
  sorry

/-- **Repeating a machine.** `tm` is run over and over; after each run the first symbol of tape `i`
is inspected, and the machine halts as soon as it is `x`. This is the loop-back that `seq` cannot
express: `seq` sends the halting state of one machine to the initial state of the *next* one,
whereas here it is sent back to the initial state of the *same* one.

The loop is specified by an invariant `P j n` holding at the start of round `n`: rounds
`0, …, N j - 1` re-establish the invariant and leave the flag unset, and round `N j` establishes
the postcondition `R j` and sets the flag. Each round costs at most `t j` steps, plus one step for
the inspection.

The space bound is `2 * k * s j + k` rather than `s j`: a round starts with all heads at `0` and
heads move by at most one cell per step, so the cells it visits form an interval around `0` of
length at most `s j`; the cells visited by *all* rounds therefore lie within distance `s j` of `0`
on each of the `k` tapes. -/
theorem exists_transformsTapes_repeat {J : Type*} {k : ℕ} (i : Fin k) (x : Bool)
    {State₀ : Type} [Finite State₀] {tm : MultiTapeTM k Bool State₀}
    {P : J → ℕ → (input : List Bool) → (Fin k → List Bool) → Prop}
    {R : J → (input : List Bool) → (Fin k → List Bool) → Prop}
    {N : J → ℕ} {t s : J → ℕ}
    (hround : ∀ (j : J) (n : ℕ), n < N j → TransformsTapes tm (P j n)
      (fun input _ ws' => P j (n + 1) input ws' ∧ (ws' i).head? ≠ some x) (t j) (s j))
    (hstop : ∀ j : J, TransformsTapes tm (P j (N j))
      (fun input _ ws' => R j input ws' ∧ (ws' i).head? = some x) (t j) (s j)) :
    ∃ (State : Type) (_ : Finite State) (tm' : MultiTapeTM k Bool State), ∀ j : J,
      TransformsTapes tm' (P j 0) (fun input _ ws' => R j input ws')
        ((N j + 1) * (t j + 1)) (2 * k * s j + k) :=
  sorry

/-- **Evaluating a computable function on work tapes.** A function computable in time `t` and space
`s` can be evaluated inside any machine that has enough work tapes: it reads its argument from tape
`i`, writes its result to tape `o`, and uses `m` further tapes as scratch space. The tapes in
`keep` are left untouched, all other tapes are blank before and after.

The length of the argument and of the result enter the bounds because they are written to and read
from work tapes; neither is bounded by `t` or `s`, since the input tape is read-only and the output
tape is append-only. -/
theorem exists_transformsTapes_ofComputable {α β : Type*} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace g enc encOut t s) :
    ∃ m c : ℕ, ∀ (k : ℕ) (i o : Fin k) (keep : Finset (Fin k)),
      i ≠ o → i ∉ keep → o ∉ keep → m + 2 + keep.card ≤ k →
      ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ a : α,
        TransformsTapes tm
          (fun _ ws => ws i = enc a ∧ ∀ l, l ≠ i → l ∉ keep → ws l = [])
          (fun _ ws ws' => ws' i = enc a ∧ ws' o = encOut (g a) ∧
            (∀ l ∈ keep, ws' l = ws l) ∧ ∀ l, l ≠ i → l ≠ o → l ∉ keep → ws' l = [])
          (c * (t a + (enc a).length + (encOut (g a)).length + 1))
          (c * (s a + (enc a).length + (encOut (g a)).length + 1) + k) :=
  sorry

/-- **Evaluating a computable function on the input.** Like
`exists_transformsTapes_ofComputable`, except that the argument is read from the real input tape,
so it does not have to be copied onto a work tape first and its length does not enter the space
bound. -/
theorem exists_transformsTapes_ofComputableInput {α β : Type*} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace g enc encOut t s) :
    ∃ m c : ℕ, ∀ (k : ℕ) (o : Fin k) (keep : Finset (Fin k)),
      o ∉ keep → m + 1 + keep.card ≤ k →
      ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ a : α,
        TransformsTapes tm
          (fun input ws => input = enc a ∧ ∀ l, l ∉ keep → ws l = [])
          (fun _ ws ws' => ws' o = encOut (g a) ∧
            (∀ l ∈ keep, ws' l = ws l) ∧ ∀ l, l ≠ o → l ∉ keep → ws' l = [])
          (c * (t a + (encOut (g a)).length + 1))
          (c * (s a + (encOut (g a)).length + 1) + k) :=
  sorry

/-- **From a tape transformation back to a computation.** A machine that, started on blank work
tapes with the input tape holding `encIn a`, halts with tape `o` holding `encOut (g a)`, computes
`g` once the contents of `o` are emitted as the output. -/
theorem computableInTimeAndSpace_of_transformsTapes {α β : Type*} {k : ℕ} (o : Fin k)
    {State : Type} [Finite State] {tm : MultiTapeTM k Bool State}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ∀ a : α, TransformsTapes tm
      (fun input ws => input = encIn a ∧ ∀ l, ws l = [])
      (fun _ _ ws' => ws' o = encOut (g a)) (t a) (s a)) :
    ∃ c, ComputableInTimeAndSpace g encIn encOut
      (fun a => c * (t a + (encOut (g a)).length + 1))
      (fun a => c * (s a + (encOut (g a)).length + 1)) :=
  sorry

end Turing.MultiTapeTM
