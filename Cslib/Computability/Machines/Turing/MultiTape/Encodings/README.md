<pre>
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Requirements on encodings

Complexity is always measured relative to encodings of the types involved. A combinator that is
proved for one particular encoding is of little use, so the combinators state which properties of
an encoding they need, and those properties are collected here, one file per type constructor.

## Principles

* **Requirements, not encodings.** A file here does not fix an encoding; it says what makes an
  encoding usable. The canonical encoding is provided as an example and is proved to satisfy the
  requirements.
* **Constructors and destructors.** The requirement for a type constructor is that its
  constructors and destructors are computable in linear time and zero space, i.e. by streaming the
  input to the output without using a work tape. This is stated directly as
  `ComputableInTimeAndSpace` of the identity function, read at the encoding of the type and at the
  encoding of the components; no separate notion is introduced for it.
* **Nothing that follows from the general results.** Deciding which constructor an encoded value
  belongs to does not have to be required if the answer is determined by finitely many exceptions:
  for `Option`, `fun o => o.isNone` is constant except at the single argument `none`, so it is
  computable in constant time and zero space for *every* encoding, by
  `computableInTimeAndSpace_of_exists_finite_ne`.

## Components

### `Option.lean`

`IsOptionEncoding enc encOpt`: the constructor `some` and its destructor are computable in linear
time and zero space. The constructor is the computability of `Option.some` itself. The destructor
is the computability of the identity of `α` from `Function.Embedding.some.trans encOpt` to `enc`,
which says that the encoding of `some a` can be turned into the encoding of `a` and constrains
nothing about encodings of `none`.

Composing with a destructor does not need a subtype: by `ComputableInTimeAndSpace.congr`,
computability only depends on the bit strings `encIn a` and `encOut (f a)`, so a machine whose
result happens to be `some x` is already a machine computing `x` at the encoding induced by `some`.

Recoding a value from one encoding to another is then transported along a computation by
`computableInTimeAndSpace_comp`, since a recoding is just a computable identity function. Note
that this costs space: the intermediate result has to be stored on a work tape, because the output
tape is append-only and cannot be read back.

`encOption` is the canonical encoding, a tag bit followed by the encoding of the value, and
`isOptionEncoding_encOption` states that it satisfies the requirements.

This is what the loop combinator
(`Cslib.Computability.Machines.Turing.MultiTape.Combinators.Loop`) needs of the encoding of the
result of its body.
