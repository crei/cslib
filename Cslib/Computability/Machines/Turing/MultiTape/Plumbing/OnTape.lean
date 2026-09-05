/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Clean
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeContents

/-!
# Redirecting the input and the output of a machine to work tapes

This is the bridge between the machine level and the function level. A machine that computes a
function reads its argument from the read-only input tape and writes its result to the append-only
output tape. To use it inside a bigger machine, its result has to end up on a work tape, and its
argument may already be on a work tape rather than on the input tape.

Note that there is no need to copy the input onto a work tape: the input tape is read-only, so the
first machine that is run on the input can simply read it there. Only the results of intermediate
computations live on work tapes.

## Main definitions

* `Turing.MultiTapeTM.inTape`, `Turing.MultiTapeTM.outTape`: the two extra tapes used by `onTape`
  to hold the argument and the result of the simulated machine.

## Main results

* `Turing.MultiTapeTM.exists_outputToTape`: a machine computing `f` can be run on the real input
  tape with its output redirected to a work tape.
* `Turing.MultiTapeTM.exists_onTape`: a machine computing `f` can be run with a work tape in place
  of the input tape and a work tape in place of the output tape.
* `Turing.MultiTapeTM.exists_tapeToOutput`: the contents of a work tape can be emitted as the
  output of the machine.

The delicate point in `onTape` is the input head of the simulated machine. `tm` believes that it is
a clamped position in `Fin (n + 2)`: the cells around the input are blank and an outward move there
does not move the head at all. The head of the work tape `inTape`, however, is an unrestricted
integer position, so the simulation has to clamp the outward moves itself. Since the contents of
the tape are a `List Symbol` and therefore blank-free, reading a blank already means "outside the
input"; the only thing the finite control has to remember in addition is which of the two
boundaries the head is parked on, since a left move is legal at the left boundary and a right move
is legal at the right boundary. So a `left | right` flag suffices, and the alphabet does not have
to be extended. Note also the off-by-one: the input head starts at position `1` of `Fin (n + 2)`,
whereas a work tape head starts at `0`, so the correspondence is `inputPos = workPos + 1`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {α β : Type*}

/-- The work tape holding the argument of the machine simulated by `onTape`. -/
public def inTape (k : ℕ) : Fin (k + 2) := ⟨k, by omega⟩

/-- The work tape holding the result of the machine simulated by `onTape` and `outputToTape`. -/
public def outTape (k : ℕ) : Fin (k + 2) := ⟨k + 1, by omega⟩

/-- **Redirecting the output to a work tape.** A machine computing `f` can be run on the real input
tape with its output written to the work tape `outTape k` instead of the output tape. It is started
on blank tapes and leaves all tapes except `outTape k` blank. -/
proof_wanted exists_outputToTape {Symbol : Type} {State : Type} [Finite State]
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ} (hclean : HaltsClean tm)
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s) :
    ∃ (c : ℕ) (State' : Type) (_ : Finite State') (tm' : MultiTapeTM (k + 2) Symbol State'),
      ∀ a : α, TransformsCfg tm' Finset.univ
        (fun input tp => input = encIn a ∧ tp.inputPos = 1 ∧ tp.IsClean)
        (fun _ _ tp' => TapeHolds (outTape k) (encOut (f a)) tp' ∧
          ∀ i : Fin (k + 2), i ≠ outTape k → TapeHolds i [] tp')
        (c * (t a + 1)) (s a + (encOut (f a)).length + k + 2)

/-- **Running a machine on work tapes.** A machine computing `f` can be run with the work tape
`inTape k` in place of the input tape and the work tape `outTape k` in place of the output tape.
The argument is left on `inTape k`, since the caller may still need it. -/
proof_wanted exists_onTape {Symbol : Type} {State : Type} [Finite State]
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ} (hclean : HaltsClean tm)
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s) :
    ∃ (c : ℕ) (State' : Type) (_ : Finite State') (tm' : MultiTapeTM (k + 2) Symbol State'),
      ∀ a : α, TransformsCfg tm' Finset.univ
        (fun _ tp => TapeHolds (inTape k) (encIn a) tp ∧
          ∀ i : Fin (k + 2), i ≠ inTape k → TapeHolds i [] tp)
        (fun _ _ tp' => TapeHolds (inTape k) (encIn a) tp' ∧
          TapeHolds (outTape k) (encOut (f a)) tp' ∧
          ∀ i : Fin (k + 2), i ≠ inTape k → i ≠ outTape k → TapeHolds i [] tp')
        (c * (t a + 1)) (s a + (encIn a).length + (encOut (f a)).length + k + 2)

/-- **Emitting a work tape as the output.** There is a machine that appends the contents of a work
tape to the output tape and clears the work tape, in time linear in its contents. -/
proof_wanted exists_tapeToOutput (i : Fin k) :
    ∃ (c : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Symbol State),
      ∀ w : List Symbol, TransformsCfg tm {i}
        (fun _ tp => TapeHolds i w tp)
        (fun _ tp tp' => tp'.output = tp.output ++ w ∧ TapeHolds i [] tp')
        (c * (w.length + 1)) (w.length + 1)

end Turing.MultiTapeTM
