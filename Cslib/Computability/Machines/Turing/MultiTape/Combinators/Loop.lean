/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.PFun
public import Mathlib.Computability.StateTransition
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Loop combinator

This file is about the loop whose condition and body are fused into a single function
`body : α → Option α`, which returns `none` exactly when the loop is to stop:

```
loop
  match body a with
  | none => return a
  | some a' => a := a'
```

This is the form in which the loop is implemented by a machine, since it needs only one machine for
the whole loop body. The usual `while` loop, with a separate condition and body, is derived from it
in `Cslib.Computability.Machines.Turing.MultiTape.Combinators.While`.

## Main definitions

* `Turing.MultiTapeTM.loopFunction`: the partial function computed by the loop, defined as
  `StateTransition.eval` of the loop body. It is undefined on the inputs for which the loop
  diverges.
* `Turing.MultiTapeTM.loopIterate`: the value after a given number of iterations, or `none` if the
  loop has already stopped.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_loopFunction`: the complexity of the loop.
-/

namespace Turing.MultiTapeTM

variable {α : Type*}

/-- The partial function computed by the loop with the fused body `body`, which returns `none`
exactly when the loop is to stop. It is defined exactly on the inputs for which the loop
terminates. -/
@[expose] public def loopFunction (body : α → Option α) : α →. α := StateTransition.eval body

/-- The value after `n` iterations of the fused loop body, or `none` if the loop has stopped
after at most `n` iterations. -/
@[expose] public def loopIterate (body : α → Option α) : ℕ → α → Option α
  | 0, a => some a
  | n + 1, a => (body a).bind (loopIterate body n)

/-- **Complexity of a loop.**

Assume that
* `f` picks, for every input, a value at which the loop terminates (`hf`), and the loop started at
  `a` stops after at most `iterBound a` iterations (`hiter`);
* the loop body is computable in time `t` and space `s` (`hbody`), where `s` also bounds the
  encoded length of all the values encountered while running the loop (`hsize`, which includes `a`
  itself);
* these bounds do not increase along the iterations of the loop (`ht`, `hs`).

Then `f` is computable in time proportional to the number of iterations times the cost of one
iteration, and in space proportional to the space of one iteration.

The machine works on two work tapes, `t1` holding the current value and `t3` holding the result of
the last call of the body. It runs the machine for `body` on its input, diverting its output onto
`t3`, and then repeats: run the machine for `isNone` on `t3` and branch on its result; if the loop
is over, emit the contents of `t1` and halt; otherwise clear `t1`, run the destructor of `some`
with `t3` as its input and `t1` as its output, clear `t3` and run the body again with `t1` as its
input and `t3` as its output.

Note that the input never has to be copied onto a work tape: the input tape is read-only, so the
first call of the body reads its argument there. Note also that `t1` has to be kept until the
result of the body has been inspected, since on exit the result of the loop is the value that was
fed to the last call of the body.

The space bound of the body alone does not bound the encoded length of the intermediate values: the
input tape is read-only and the output tape is append-only, so neither counts towards the space
bound, and a machine can produce an output much longer than the space it uses. The intermediate
values, however, are stored on a work tape, and hence `hsize` is a genuine additional assumption on
`s`. Since the resulting bounds are stated up to a constant factor, using a single `s` for both
purposes is no weaker than using two separate bounds, whose maximum `s` can be taken to be. -/
proof_wanted computableInTimeAndSpace_loopFunction
    {α : Type*} {body : α → Option α} {f : α → α}
    {enc : α ↪ List Bool} {encOpt : Option α ↪ List Bool} {t s iterBound : α → ℕ}
    (henc : IsOptionEncoding enc encOpt)
    (hf : ∀ a, f a ∈ loopFunction body a)
    (hiter : ∀ a, ∃ m ≤ iterBound a, loopIterate body m a = none)
    (hsize : ∀ a m x, loopIterate body m a = some x → (enc x).length ≤ s a)
    (hbody : ComputableInTimeAndSpace body enc encOpt t s)
    (ht : ∀ a m x, loopIterate body m a = some x → t x ≤ t a)
    (hs : ∀ a m x, loopIterate body m a = some x → s x ≤ s a) :
    ∃ c, ComputableInTimeAndSpace f enc enc
      (fun a => c * (iterBound a + 1) * (t a + s a + 1))
      (fun a => c * (s a + 1))

end Turing.MultiTapeTM
