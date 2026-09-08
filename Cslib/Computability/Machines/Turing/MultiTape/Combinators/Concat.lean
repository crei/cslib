/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of a concatenation of two functions

If `f` and `g` are computable, then so is any function whose encoded result is the encoded result
of `f` followed by the encoded result of `g`. The bounds are the sums of the two bounds, plus one
rewind of the input tape in time and a constant in space.

The machine runs the machine for `f`, rewinds the input head, and runs the machine for `g` on fresh
work tapes. The intermediate results are never stored: both machines write straight to the output
tape, which is append-only, so their outputs end up concatenated. The rewind is what lets the
second machine read the same input as the first, and it is the reason the input length appears in
the time bound.

This is the introduction rule of a finite product, dual to the case analysis of
`Cslib.Computability.Machines.Turing.MultiTape.Combinators.Ite`, which is the elimination rule of a
finite coproduct. Both are irreducibly machine-level for the same reason: they need the input to be
presented twice, once to each of the two computations.

Note that only the *syntactic* factorisation of the encoding is required. Producing a pair asks
nothing of the encoding beyond `henc`, whereas consuming one — reading a component back out —
is a genuine computability requirement on the encoding, of the kind
`Cslib.Computability.Machines.Turing.MultiTape.Encodings.Option` collects.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_concat`: the complexity of a concatenation.
* `Turing.MultiTapeTM.computableInTimeAndSpace_pair`: the special case of a pair.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ δ : Type*}

/-- **Complexity of a concatenation.** If `f` and `g` are computable and the encoded result of `h`
is the encoded result of `f` followed by the encoded result of `g`, then `h` is computable in the
sum of the two times plus the length of the input, and in the sum of the two spaces plus a
constant.

The result is stated for an arbitrary `h` with the assumption that its encoding factors as the
concatenation, rather than for a fixed pairing, so that it covers whatever the caller happens to be
encoding — a pair, a tuple, a constructor of an inductive type — and the caller is the one who has
to know that the concatenation of the two encodings is again injective. -/
public theorem computableInTimeAndSpace_concat
    {f : α → β} {g : α → γ} {h : α → δ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {encD : δ ↪ List Bool}
    {tf sf tg sg : α → ℕ}
    (henc : ∀ x, encD (h x) = encB (f x) ++ encC (g x))
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace h encIn encD
      (fun x => tf x + tg x + (encIn x).length + 2)
      (fun x => sf x + sg x + c) :=
  sorry

/-- **Complexity of computing a pair.** The special case of `computableInTimeAndSpace_concat` in
which the two results are packed into a pair, encoded by concatenating the two encodings. It is up
to the caller to provide such an encoding; this needs the encoding of the first component to
determine where it ends. -/
public theorem computableInTimeAndSpace_pair
    {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {encPair : β × γ ↪ List Bool} {tf sf tg sg : α → ℕ}
    (henc : ∀ p : β × γ, encPair p = encB p.1 ++ encC p.2)
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn encPair
      (fun x => tf x + tg x + (encIn x).length + 2)
      (fun x => sf x + sg x + c) :=
  computableInTimeAndSpace_concat (fun x => henc (f x, g x)) hf hg

end Turing.MultiTapeTM
