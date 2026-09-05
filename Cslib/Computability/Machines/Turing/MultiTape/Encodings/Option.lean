/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-!
# Encodings of `Option`

A combinator that produces or consumes an `Option` should not prescribe how `Option α` is encoded.
It is enough that the encoding relates to the encoding of `α` in the way one would expect of a
tagged union: the constructor `some` and its destructor are computable in linear time and zero
space, i.e. by streaming the input to the output without using a work tape.

The constructor is stated as computability of `Option.some` itself. There is no such function for
the destructor, since a total function `Option α → α` would need a junk value at `none`. Instead,
the destructor is stated as computability of the identity of `α`, read at the encoding of `α`
induced by `encOpt` via `some` on the input side and at `enc` on the output side. This says exactly
that the encoding of `some a` can be turned into the encoding of `a`, and says nothing about
encodings of `none`.

A subtype `{o : Option α // o.isSome}` would be another way of expressing this, but it is not
needed for composability: computability only depends on the bit strings `encIn a` and
`encOut (f a)`, so by `ComputableInTimeAndSpace.congr` a machine computing `body : α → Option α`
is, on the inputs where the result is `some x`, a machine computing `x` at the encoding
`Function.Embedding.some.trans encOpt`, which is exactly the input encoding of the destructor. The
subtype would drag `Subtype.val` embeddings and `isSome` proofs through every statement without
buying anything.

Testing an encoded value for `none` is *not* a requirement: `fun o => o.isNone` is constant except
at the single argument `none`, so it is computable in constant time and zero space for every
encoding, by `computableInTimeAndSpace_of_exists_finite_ne`.

## Main definitions

* `Turing.MultiTapeTM.IsOptionEncoding`: the requirements on an encoding of `Option α` relative to
  an encoding of `α`.
* `Turing.MultiTapeTM.encOption`: the canonical encoding of `Option α`, which prefixes the encoding
  of the value with a tag bit.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_isNone`: testing for `none` is computable in
  constant time and zero space, for every encoding.
* `Turing.MultiTapeTM.isOptionEncoding_encOption`: the canonical encoding satisfies the
  requirements.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α : Type*}

/-- The requirements on an encoding `encOpt` of `Option α`, relative to an encoding `enc` of `α`:
the constructor `some` and its destructor are computable in linear time and zero space. -/
public structure IsOptionEncoding (enc : α ↪ List Bool) (encOpt : Option α ↪ List Bool) : Prop where
  /-- The constructor `some` is computable in linear time and zero space. -/
  constructor_computable : ∃ c, ComputableInTimeAndSpace (Option.some : α → Option α) enc encOpt
    (fun a => c * ((enc a).length + 1)) (fun _ => 0)
  /-- The destructor of `some` is computable in linear time and zero space. Note that this only
  constrains the encodings of values of the form `some a`. -/
  destructor_computable : ∃ c, ComputableInTimeAndSpace (id : α → α)
    (Function.Embedding.some.trans encOpt) enc
    (fun a => c * ((encOpt (some a)).length + 1)) (fun _ => 0)

/-- Testing an encoded value for `none` is computable in constant time and zero space, for every
encoding of `Option α`, since the function is constant except at the single argument `none`. -/
proof_wanted computableInTimeAndSpace_isNone {encOpt : Option α ↪ List Bool}
    {encBool : Bool ↪ List Bool} :
    ∃ c, ComputableInTimeAndSpace (fun o : Option α => o.isNone) encOpt encBool
      (fun _ => c) (fun _ => 0)

/-- The canonical encoding of `Option α`: a tag bit, followed by the encoding of the value. -/
public def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool where
  toFun
    | none => [false]
    | some a => true :: enc a
  inj' := by rintro (_ | a) (_ | b) h <;> simp_all

/-- The canonical encoding of `Option α` satisfies the requirements: the constructor emits a `true`
and then copies its input, the destructor drops the `true` and copies the rest. -/
proof_wanted isOptionEncoding_encOption {enc : α ↪ List Bool} :
    IsOptionEncoding enc (encOption enc)

end Turing.MultiTapeTM
