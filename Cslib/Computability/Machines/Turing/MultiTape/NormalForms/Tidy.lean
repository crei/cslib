/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# The tidy normal form

A machine given by `ComputesFunInTimeAndSpace` promises nothing about the configuration it halts
in: its work tapes hold garbage — possibly with blanks embedded, so that no scan can find its
extent — and its heads are wherever the run left them. A *tidy* machine halts in the fully
normalised configuration: work tapes blank, all heads back at the start, the input head rewound —
which is exactly a `Turing.MultiTapeTM.wordsCfg`. Tidiness is what the word-transformer interface
(`Turing.MultiTapeTM.TransformsTapes`) needs of a machine before it can be run on redirected
tapes: a tidy machine ends where the next one can begin.

The normal-form theorem — every computable function has a tidy machine, at a constant-factor cost
in time and space — is the deep result of this directory. Its construction instruments the given
machine with one *footprint* tape per work tape, marking every visited cell in lockstep (the
footprint is contiguous because a head path is connected, restoring the scannability that garbage
lacks) with a distinguished anchor mark at cell `0`, and afterwards sweeps each pair clean,
outside-in towards the anchor.

## Main definitions

* `Turing.MultiTapeTM.TidyComputes`: the machine computes the function and halts tidily.
-/

namespace Turing.MultiTapeTM

variable {α β : Type*} {k : ℕ} {Symbol State : Type*}

/-- The machine computes `f` between the given encodings within the given bounds, and halts in the
fully normalised configuration: work tapes blank with heads at the start, input head rewound, the
encoded result as the output. -/
@[expose] public def TidyComputes (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ τ ≤ t a,
    tm.runFrom (tm.initCfg (encIn a)) τ =
      wordsCfg (encIn a) none (fun _ => []) (encOut (f a)) ∧
    tm.spaceUsed (tm.initCfg (encIn a)) τ ≤ s a

/-- A tidy machine computes its function in the ordinary sense: tidiness only adds constraints on
the halting configuration. -/
public theorem TidyComputes.computesFunInTimeAndSpace
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ} (h : TidyComputes tm encIn encOut f t s) :
    ComputesFunInTimeAndSpace tm encIn encOut f t s := by
  intro a
  obtain ⟨τ, hτ, hrun, hspace⟩ := h a
  exact ⟨τ, hτ, _, hspace, by rw [hrun]; rfl, by rw [hrun]; rfl, rfl⟩

end Turing.MultiTapeTM
