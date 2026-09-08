/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Tactic.Ring
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concat

/-!
# Requirements on an encoding of a pair

A combinator that produces or consumes a pair should not prescribe how `α × β` is encoded. What it
needs is that packing and unpacking are cheap, and nothing about the shape of the encoded string —
no assumption that it *is* the concatenation of the components, which would rule out interleaved,
length-prefixed-in-the-middle or otherwise repackaged layouts.

Following `Cslib.Computability.Machines.Turing.MultiTape.Encodings.Option`, each requirement is
computability of a unary function, at the bounds a machine can actually meet: **linear time and
constant space**, that is, by streaming the input to the output with only the finite control. Zero
space, which is what suffices for `Option`, is too strong here: a single tag bit can be dropped
while streaming, but finding where a component ends may need the control to keep count.

## The one thing that is not a complexity

`cat_injective` says that the components laid out one after the other determine the pair. This is
not an assumption about `encP` — it says nothing about `encP` at all — but about `encA` and `encB`:
the first must be self-delimiting in front of the second. It is unavoidable, because without it
"the components one after the other" is not an encoding and `pack` cannot even be stated. It is
also exactly the property a parenthesis- or escape-based encoding is designed to have.

## Producing and consuming are not symmetric

`pack` is what a combinator building a pair needs, and `fst_computable`/`snd_computable` are what a
combinator taking one apart needs. With a concatenation-style layout the first is free — a machine
emitting the components one after the other has already produced the pair — while the second is
not, since the boundary has to be found. That asymmetry is why `Encodings/` has to be consulted at
all: concatenating is easier than parsing.

## Main definitions

* `Turing.MultiTapeTM.catEncoding`: the components, one after the other.
* `Turing.MultiTapeTM.IsPairEncoding`: the requirements.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_pair_of_isPairEncoding`: two computable functions
  can be paired, with no assumption on the shape of the pair's encoding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type*}

/-- The components of a pair laid out one after the other, as an encoding. That this is injective
is the self-delimitation of `encA` in front of `encB`, and has to be supplied. -/
public def catEncoding (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (h : Function.Injective fun p : α × β => encA p.1 ++ encB p.2) : α × β ↪ List Bool :=
  ⟨fun p => encA p.1 ++ encB p.2, h⟩

@[simp]
public lemma catEncoding_apply {encA : α ↪ List Bool} {encB : β ↪ List Bool} {h} (p : α × β) :
    catEncoding encA encB h p = encA p.1 ++ encB p.2 := rfl

/-- The requirements on an encoding `encP` of `α × β`, relative to encodings of the components:
the pair can be packed from its components and unpacked back into them, in linear time and constant
space. Nothing is assumed about the shape of `encP`. -/
public structure IsPairEncoding (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (encP : α × β ↪ List Bool) : Prop where
  /-- The components one after the other determine the pair. Not a condition on `encP`, but the
  self-delimitation of `encA` in front of `encB`, without which `pack` cannot be stated. -/
  cat_injective : Function.Injective fun p : α × β => encA p.1 ++ encB p.2
  /-- Packing: the components, one after the other, can be turned into the encoded pair in linear
  time and constant space. -/
  pack : ∃ c, ComputableInTimeAndSpace (fun p : α × β => p)
    (catEncoding encA encB cat_injective) encP
    (fun p => c * ((encA p.1).length + (encB p.2).length + 1)) (fun _ => c)
  /-- The first component can be read back, in linear time and constant space. -/
  fst_computable : ∃ c, ComputableInTimeAndSpace Prod.fst encP encA
    (fun p => c * ((encP p).length + 1)) (fun _ => c)
  /-- The second component can be read back, in linear time and constant space. -/
  snd_computable : ∃ c, ComputableInTimeAndSpace Prod.snd encP encB
    (fun p => c * ((encP p).length + 1)) (fun _ => c)

/-- **Complexity of computing a pair, for any encoding meeting the requirements.** Two computable
functions of the same input can be paired: run the first, rewind, run the second — which produces
the components one after the other — and then pack.

The encoded components appear in both bounds because the concatenation is handed to the packing
machine as its input, and `computableInTimeAndSpace_comp` parks an intermediate result on a work
tape. Where the packing is the identity, that is, where `encP` *is* the concatenation, the last
step disappears and `computableInTimeAndSpace_pair` gives the sharper bounds. -/
public theorem computableInTimeAndSpace_pair_of_isPairEncoding
    {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {encP : β × γ ↪ List Bool} {tf sf tg sg : α → ℕ}
    (henc : IsPairEncoding encB encC encP)
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn encP
      (fun x => c * (tf x + tg x + (encIn x).length
        + (encB (f x)).length + (encC (g x)).length + 1))
      (fun x => c * (sf x + sg x + (encB (f x)).length + (encC (g x)).length + 1)) := by
  obtain ⟨cp, hp⟩ := henc.pack
  -- run the two machines one after the other: the components land on the output tape in order
  obtain ⟨c₁, h₁⟩ := computableInTimeAndSpace_concat (h := fun x => (f x, g x))
    (encD := catEncoding encB encC henc.cat_injective) (fun _ => rfl) hf hg
  -- then pack
  obtain ⟨c₂, h₂⟩ := computableInTimeAndSpace_comp h₁ hp
  refine ⟨c₂ * (cp + c₁ + 4), h₂.mono (fun x => ?_) (fun x => ?_)⟩
  · simp only [catEncoding_apply, List.length_append]
    calc _ ≤ c₂ * ((cp + c₁ + 4) * (tf x + tg x + (encIn x).length
              + (encB (f x)).length + (encC (g x)).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : cp * ((encB (f x)).length + (encC (g x)).length + 1)
              ≤ cp * (tf x + tg x + (encIn x).length
                + (encB (f x)).length + (encC (g x)).length + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have h2 : (cp + c₁ + 4) * (tf x + tg x + (encIn x).length
                + (encB (f x)).length + (encC (g x)).length + 1)
              = cp * (tf x + tg x + (encIn x).length
                  + (encB (f x)).length + (encC (g x)).length + 1)
                + c₁ * (tf x + tg x + (encIn x).length
                  + (encB (f x)).length + (encC (g x)).length + 1)
                + 4 * (tf x + tg x + (encIn x).length
                  + (encB (f x)).length + (encC (g x)).length + 1) := by ring
          omega
      _ = c₂ * (cp + c₁ + 4) * (tf x + tg x + (encIn x).length
            + (encB (f x)).length + (encC (g x)).length + 1) := by ring
  · simp only [catEncoding_apply, List.length_append]
    calc _ ≤ c₂ * ((cp + c₁ + 4) * (sf x + sg x
              + (encB (f x)).length + (encC (g x)).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : cp ≤ cp * (sf x + sg x
              + (encB (f x)).length + (encC (g x)).length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          have h2 : c₁ ≤ c₁ * (sf x + sg x
              + (encB (f x)).length + (encC (g x)).length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          have h3 : (cp + c₁ + 4) * (sf x + sg x
                + (encB (f x)).length + (encC (g x)).length + 1)
              = cp * (sf x + sg x + (encB (f x)).length + (encC (g x)).length + 1)
                + c₁ * (sf x + sg x + (encB (f x)).length + (encC (g x)).length + 1)
                + 4 * (sf x + sg x + (encB (f x)).length + (encC (g x)).length + 1) := by ring
          omega
      _ = c₂ * (cp + c₁ + 4) * (sf x + sg x
            + (encB (f x)).length + (encC (g x)).length + 1) := by ring

end Turing.MultiTapeTM
