/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of composed functions

If `f` and `g` are computable, then so is `g ∘ f`. The machine runs the machine for `f` with its
output diverted onto a work tape, and then runs the machine for `g` with that tape as its input
tape.

Note that the intermediate result has to be stored on a work tape: the output tape is append-only
and cannot be read back. Its length therefore enters both the time and the space bound, and it is
not bounded by the space used by the machine for `f`, since a machine can produce an output much
longer than the space it uses.

Recoding the input or the output of a computation is the special case where one of the two
functions is the identity.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_comp`: the complexity of a composition.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type*}

/-- **Complexity of the identity.** A machine can copy its input to its output one symbol at a
time, so the identity is computable in linear time and zero space, relative to any encoding.

Together with `computableInTimeAndSpace_comp` this is what recodes a value from one encoding to
another, and what copies the input of a machine onto a work tape. -/
public theorem computableInTimeAndSpace_id {enc : α ↪ List Bool} :
    ∃ c, ComputableInTimeAndSpace (id : α → α) enc enc
      (fun a => c * ((enc a).length + 1)) (fun _ => 0) :=
  sorry

/-- **Complexity of a composition.** The bounds are those of the two machines, plus the length of
the encoded intermediate result, which has to be written to and read from a work tape. -/
proof_wanted computableInTimeAndSpace_comp {f : α → β} {g : β → γ}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {tf sf : α → ℕ} {tg sg : β → ℕ}
    (hf : ComputableInTimeAndSpace f encA encB tf sf)
    (hg : ComputableInTimeAndSpace g encB encC tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun a => g (f a)) encA encC
      (fun a => c * (tf a + tg (f a) + (encB (f a)).length + 1))
      (fun a => c * (sf a + sg (f a) + (encB (f a)).length + 1))

end Turing.MultiTapeTM
