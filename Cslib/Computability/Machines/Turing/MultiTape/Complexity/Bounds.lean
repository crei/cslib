/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Defs
public meta import Cslib.Computability.Machines.Turing.MultiTape.Complexity.BoundsAttr

/-!
# Resource certificates

`Bounds f` bundles everything a combinator needs to know about `f`: a time bound, a work-tape
space bound, a bound on the size of its output, the monotonicity of all three, and the proofs that
they hold. Combinators then become *definitions that compute bounds* rather than theorems that
restate them, and their monotonicity side conditions discharge themselves.

## Design

* **Indexed by the function.** `Bounds f`, not a structure with an `fn` field, so that one can
  state `Bounds Nat.succ` and keep the function visible in the type.
* **Built on `DataComputableInTimeAndSpace`, not `ComputableUpTo`.** The coarse view discards
  polynomial factors in time and constant factors in space *at the point of statement*; an algebra
  built on top of it could never recover them. `Bounds.polyTimeLinSpace` takes the coarse view at
  the very end instead.
* **`outSize` is a field of its own.** It is not derivable from `space`: the output tape is
  write-only and is not charged for space, so a machine may emit far more than its work-tape
  space. (`outSize ≤ time` is always available — at most one symbol is emitted per step — but it is
  usually far too weak.)
* `Bounds` is `Type`-valued: it is a witness, not a property. Use `ComputableUpTo` when a `Prop` is
  wanted.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

variable {α β : Type} [DataEncode α] [DataEncode β]

/-- A resource certificate for `f`: bounds on its running time, its work-tape space and the size
of its output, all as functions of the encoded input size, together with their monotonicity and
the proofs that they hold. -/
structure Bounds (f : α → β) where
  /-- Bound on the number of steps, in the encoded input size. -/
  time : ℕ → ℕ
  /-- Bound on the number of work-tape cells visited, in the encoded input size. -/
  space : ℕ → ℕ
  /-- Bound on the encoded size of the output, in the encoded input size. -/
  outSize : ℕ → ℕ
  /-- Combinators evaluate `time` at an over-approximation of the true input size. -/
  time_mono : Monotone time
  /-- Combinators evaluate `space` at an over-approximation of the true input size. -/
  space_mono : Monotone space
  /-- Combinators evaluate `outSize` at an over-approximation of the true input size. -/
  outSize_mono : Monotone outSize
  /-- Some multi-tape Turing machine computes `f` within `time` and `space`. -/
  computes : DataComputableInTimeAndSpace f time space
  /-- The output really is no bigger than `outSize` says. -/
  out_le : ∀ a, (DataEncode.encode (f a)).size ≤ outSize (DataEncode.encode a).size

namespace Bounds

/-- Transport a certificate along an equality of functions. Used to turn a certificate for the
literal shape a combinator produces into one for the function actually of interest. -/
def congr {f g : α → β} (b : Bounds f) (h : f = g := by rfl) : Bounds g where
  time := b.time
  space := b.space
  outSize := b.outSize
  time_mono := b.time_mono
  space_mono := b.space_mono
  outSize_mono := b.outSize_mono
  computes := h ▸ b.computes
  out_le := h ▸ b.out_le

/-- Transport leaves the time bound alone.

`congr` copies the resource fields *verbatim* and confines `Eq.rec` to the `Prop` fields, so this
and its siblings hold by `rfl` and a transported certificate's bounds stay definitionally readable
through any chain of retargets. Transporting the whole structure instead would leave them stuck
behind `Eq.rec`, silently disabling `Bounds.polyTimeLinSpace` for every derived certificate. -/
@[simp, boundsDefs] lemma congr_time {f g : α → β} (b : Bounds f) (h : f = g) :
    (b.congr h).time = b.time := rfl

/-- Transport leaves the space bound alone. -/
@[simp, boundsDefs] lemma congr_space {f g : α → β} (b : Bounds f) (h : f = g) :
    (b.congr h).space = b.space := rfl

/-- Transport leaves the output-size bound alone. -/
@[simp, boundsDefs] lemma congr_outSize {f g : α → β} (b : Bounds f) (h : f = g) :
    (b.congr h).outSize = b.outSize := rfl


/-- Weaken all three bounds at once. Composition produces one specific closed form; this is how
one restates it more readably. -/
def weaken {f : α → β} (b : Bounds f) (t s o : ℕ → ℕ)
    (ht_mono : Monotone t) (hs_mono : Monotone s) (ho_mono : Monotone o)
    (ht : ∀ n, b.time n ≤ t n) (hs : ∀ n, b.space n ≤ s n) (ho : ∀ n, b.outSize n ≤ o n) :
    Bounds f where
  time := t
  space := s
  outSize := o
  time_mono := ht_mono
  space_mono := hs_mono
  outSize_mono := ho_mono
  computes := b.computes.mono ht hs
  out_le a := le_trans (b.out_le a) (ho _)

section Weaken
variable {f : α → β} (b : Bounds f) (t s o : ℕ → ℕ) (ht_mono : Monotone t) (hs_mono : Monotone s)
  (ho_mono : Monotone o) (ht : ∀ n, b.time n ≤ t n) (hs : ∀ n, b.space n ≤ s n)
  (ho : ∀ n, b.outSize n ≤ o n)

@[simp, boundsDefs] lemma weaken_time :
    (b.weaken t s o ht_mono hs_mono ho_mono ht hs ho).time = t := rfl

@[simp, boundsDefs] lemma weaken_space :
    (b.weaken t s o ht_mono hs_mono ho_mono ht hs ho).space = s := rfl

@[simp, boundsDefs] lemma weaken_outSize :
    (b.weaken t s o ht_mono hs_mono ho_mono ht hs ho).outSize = o := rfl

end Weaken

/-- Every certificate yields the coarse `ComputableUpTo` statement with the same bounds. -/
theorem toComputableUpTo {f : α → β} (b : Bounds f) : ComputableUpTo f b.time b.space :=
  ⟨1, b.computes.mono
    (fun n => by simp only [pow_one, one_mul]; omega)
    (fun n => by simp only [one_mul]; omega)⟩

/-- Read "polynomial time, linear space" off a certificate. This is the intended last step of an
example: build the certificate with exact bounds, then take the coarse view once. -/
theorem polyTimeLinSpace {f : α → β} (b : Bounds f) (d k e : ℕ)
    (ht : ∀ n, b.time n ≤ d * (n + n + 2) ^ k)
    (hs : ∀ n, b.space n ≤ e * (n + 1)) :
    PolyTimeLinSpace f :=
  b.toComputableUpTo.absorb d k e ht hs

end Bounds

end MultiTapeTM

end Turing
