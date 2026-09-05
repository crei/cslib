/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of a conditional

If a condition and both of its branches are computable, then so is the conditional built from
them, in the time and space of the condition plus the time and space of the branch that is taken.

This is the function-level face of the branching a machine performs on the contents of a work
tape: the machine for the condition writes its result onto a work tape, the next transition looks
at that tape and continues with the machine of one branch or the other. It is stated at the level
of functions so that it can be reused without ever talking about tapes again.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_ite`: the complexity of a conditional.
-/

-- `proof_wanted` emits a private declaration, so this module contains no public ones yet.
set_option linter.privateModule false

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- **Complexity of a conditional.** The machine runs the machine for `cond`, redirecting its
output onto a work tape. Since `encCond` is injective, the two possible contents of that tape are
two different fixed strings, which the finite control can tell apart in constant time; it then
continues with the machine for the branch that is taken, on the original input.

Only the branch that is taken is executed, hence the `max` of the two bounds. -/
proof_wanted computableInTimeAndSpace_ite {cond : α → Bool} {_if _else : α → β}
    {encIn : α ↪ List Bool} {encCond : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {tc sc tif sif telse selse : α → ℕ}
    (hcond : ComputableInTimeAndSpace cond encIn encCond tc sc)
    (hif : ComputableInTimeAndSpace _if encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace _else encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => if cond a then _if a else _else a) encIn encOut
      (fun a => c * (tc a + max (tif a) (telse a) + 1))
      (fun a => c * (sc a + max (sif a) (selse a) + 1))

end Turing.MultiTapeTM
