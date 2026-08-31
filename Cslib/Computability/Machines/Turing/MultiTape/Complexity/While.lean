/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Bounds

/-!
# Unbounded iteration

`Bounds.while` is the companion of `Bounds.fold` for loops whose trip count is not given by a
list. It is what a universal machine needs: it runs the simulated machine until it halts, rather
than for a number of steps read off the input.

## The shape of the statement

A `while` loop is partial, so the combinator cannot simply be handed `p` and `f` and produce a
function. Instead the *result* `out` is supplied together with an iteration count `steps`, and
three hypotheses pin them down: `out a` is the `steps a`-th iterate, the test fires there, and it
did not fire earlier. Nothing is assumed about inputs on which the loop diverges, because there
are none — `steps` is total.

Two further arguments are the ones a human must invent, exactly as `A` is for `Bounds.fold`:

* `N`, a bound on the number of iterations;
* `A`, a bound on the encoded size of every intermediate value.

## Why space does not multiply

The time bound carries a factor of `N` — every iteration re-runs the test and the body. The space
bound does **not**: the work tapes of one iteration are reused by the next, so the space cost is
the largest single iteration rather than their sum. That asymmetry is the whole reason a loop can
run for exponentially many steps in polynomial space, and it is the point of
[issue #611](https://github.com/leanprover/cslib/issues/611)'s remark that for `fold` and `while_`
"tapes from earlier iterations are re-used, so the space usage is the max over all iterations".
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

variable {α γ : Type} [DataEncode α] [DataEncode γ]

/-- **Unbounded iteration.** Starting from `init a`, apply `f` until the test `p` holds; the
result is `out a`, reached after `steps a` iterations.

Time is `init` plus one test-and-body per iteration; space is `init` plus a *single* iteration
plus the largest intermediate value, because iterations reuse each other's tapes. -/
def Bounds.while {p : γ → Bool} {f : γ → γ} {init out : α → γ}
    (hi : Bounds init) (hp : Bounds p) (hf : Bounds f)
    (steps : α → ℕ)
    (h_out : ∀ a, out a = f^[steps a] (init a))
    (h_halt : ∀ a, p (f^[steps a] (init a)) = true)
    (h_first : ∀ a j, j < steps a → p (f^[j] (init a)) = false)
    (N A : ℕ → ℕ) (hN_mono : Monotone N) (hA_mono : Monotone A)
    (hN : ∀ a, steps a ≤ N (DataEncode.encode a).size)
    (hA : ∀ (a : α) (j : ℕ), j ≤ steps a →
      (DataEncode.encode (f^[j] (init a))).size ≤ A (DataEncode.encode a).size) :
    Bounds out where
  time n := hi.time n + (N n + 1) * (hp.time (A n) + hf.time (A n))
  space n := hi.space n + hp.space (A n) + hf.space (A n) + A n
  outSize := A
  time_mono := fun _ _ h =>
    Nat.add_le_add (hi.time_mono h)
      (Nat.mul_le_mul (Nat.add_le_add (hN_mono h) (le_refl 1))
        (Nat.add_le_add (hp.time_mono (hA_mono h)) (hf.time_mono (hA_mono h))))
  space_mono := fun _ _ h =>
    Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (hi.space_mono h) (hp.space_mono (hA_mono h)))
        (hf.space_mono (hA_mono h)))
      (hA_mono h)
  outSize_mono := hA_mono
  computes := sorry
  out_le a := by
    rw [h_out a]
    exact hA a (steps a) (le_refl _)

/-- Iterating a function that grows the encoding by at most `C` grows it by at most `j * C`. This
is the standard way to discharge `Bounds.while`'s `A` argument. -/
lemma size_iterate_le {f : γ → γ} (C : ℕ)
    (hf : ∀ c, (DataEncode.encode (f c)).size ≤ (DataEncode.encode c).size + C)
    (j : ℕ) (c : γ) :
    (DataEncode.encode (f^[j] c)).size ≤ (DataEncode.encode c).size + j * C := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have h1 := hf c
    have h2 := ih (f c)
    have h3 : (j + 1) * C = j * C + C := by ring
    omega

end MultiTapeTM

end Turing
