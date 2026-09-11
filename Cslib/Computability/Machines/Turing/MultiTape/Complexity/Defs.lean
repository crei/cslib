/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.Linarith

/-!
# Computability of typed functions

`DataComputableInTimeAndSpace` lifts `MultiTapeTM.ComputableInTimeAndSpace` to functions between
arbitrary encodable types, measuring resources in the *encoded* input size. `ComputableUpTo` is the
coarse view of it — polynomial slack in time, constant-factor slack in space — and
`PolyTimeLinSpace` is the coarse view most statements are phrased with.

Prefer the precise `DataComputableInTimeAndSpace` (via `Bounds`) when building an algebra of
combinators: `ComputableUpTo` destroys exactly the precision that sub-linear-space results need.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

/-! ## 3. Computability of typed functions, up to polynomial time and linear space

`MultiTapeTM.ComputableInTimeAndSpace` speaks about functions `List IOSymbol → List IOSymbol`
and measures resources in the raw input length. `DataComputableInTimeAndSpace` lifts it to
functions between arbitrary encodable types, measuring resources in the *encoded* input size.

Note that the machine is only constrained on inputs that are genuine encodings; bit strings that
do not decode to a value of `α` are left completely unspecified. That is why `DataEncode` needs
no decoding function: requiring the machine to also *recognise* malformed inputs within the same
bounds would be a strictly stronger — and, for the purposes of this file, irrelevant — demand.
-/

/-- The typed analogue of `MultiTapeTM.ComputableInTimeAndSpace`: there is a multi-tape Turing
machine with a finite alphabet and a finite state set that, on the encoding of any `a : α`,
outputs the encoding of `f a` using at most `t n` steps and at most `s n` cells, where `n` is the
encoded size of `a`. -/
def DataComputableInTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
    (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ (k sym state : ℕ) (emb : Bool ↪ Fin sym) (tm : MultiTapeTM k (Fin sym) (Fin state)),
    ∀ a : α,
      ∃ t' ≤ t (DataEncode.encode a).size, ∃ s' ≤ s (DataEncode.encode a).size,
        tm.ComputesInTimeAndSpace
          ((DataEncode.encode a).toBits.map emb)
          ((DataEncode.encode (f a)).toBits.map emb)
          t' s'

/-- Weakening the bounds of `DataComputableInTimeAndSpace`. -/
lemma DataComputableInTimeAndSpace.mono {α β : Type} [DataEncode α] [DataEncode β]
    {f : α → β} {t s t' s' : ℕ → ℕ}
    (h : DataComputableInTimeAndSpace f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    DataComputableInTimeAndSpace f t' s' := by
  obtain ⟨k, sym, state, emb, tm, h⟩ := h
  refine ⟨k, sym, state, emb, tm, fun a => ?_⟩
  obtain ⟨t₀, ht₀, s₀, hs₀, hcomp⟩ := h a
  exact ⟨t₀, le_trans ht₀ (ht _), s₀, le_trans hs₀ (hs _), hcomp⟩

/-- The main notion of this file: `f` is computable in time *polynomially* bounded in `t` and
space bounded in `s` *up to a constant factor*.

This is the level of precision at which composition theorems such as `foldl_computableUpTo` are
stated: it is coarse enough that no particular tape layout, alphabet or head-scheduling discipline
can matter, and it is closed under composition (a polynomial in a polynomial is a polynomial; a
constant multiple of a constant multiple is a constant multiple), so such statements chain.

The `+ n + 2` in the time bound simply acknowledges that a machine must be allowed to read its
input; it makes the notion insensitive to time bounds that are sublinear for trivial reasons. -/
def ComputableUpTo {α β : Type} [DataEncode α] [DataEncode β]
    (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, DataComputableInTimeAndSpace f
    (fun n => c * (t n + n + 2) ^ c)
    (fun n => c * (s n + 1))

/-- `f` is computable in polynomial time and linear space. -/
abbrev PolyTimeLinSpace {α β : Type} [DataEncode α] [DataEncode β] (f : α → β) : Prop :=
  ComputableUpTo f (fun n => n) (fun n => n)

/-- Weakening the bounds of `ComputableUpTo`. -/
lemma ComputableUpTo.mono {α β : Type} [DataEncode α] [DataEncode β]
    {f : α → β} {t s t' s' : ℕ → ℕ}
    (h : ComputableUpTo f t s) (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    ComputableUpTo f t' s' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hc.mono (fun n => ?_) (fun n => ?_)⟩
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := ht n; omega) _)
  · exact Nat.mul_le_mul_left _ (by have := hs n; omega)

/-- `ComputableUpTo` absorbs its own slack: a bound that is polynomially related to `t'` and
linearly related to `s'` may be *restated* as a bound in terms of `t'` and `s'`.

This is what lets a caller state a clean conclusion — "polynomial time, linear space" — after a
chain of compositions has produced an unwieldy closed form.

Proof sketch (routine `Nat.pow` arithmetic, still to be written): from `h` obtain `c`. Since
`t n + n + 2 ≤ d * (t' n + n + 2) ^ d + (t' n + n + 2) ≤ (d + 1) * (t' n + n + 2) ^ (max d 1)`,
one gets `c * (t n + n + 2) ^ c ≤ c * (d + 1) ^ c * (t' n + n + 2) ^ (c * max d 1)`; as the base
is at least `2`, any `c'` above both `c * (d + 1) ^ c` and `c * max d 1` works. For space,
`c * (s n + 1) ≤ c * (e * (s' n + 1) + 1) ≤ c * (e + 1) * (s' n + 1)`. Take the max of the two
witnesses. -/
lemma ComputableUpTo.absorb {α β : Type} [DataEncode α] [DataEncode β]
    {f : α → β} {t s t' s' : ℕ → ℕ} (d k e : ℕ)
    (h : ComputableUpTo f t s)
    (ht : ∀ n, t n ≤ d * (t' n + n + 2) ^ k)
    (hs : ∀ n, s n ≤ e * (s' n + 1)) :
    ComputableUpTo f t' s' := by
  sorry

/-- **Sequential composition.** Run the machine for `f`, materialise its output on a work tape,
then run the machine for `g` on it.

`S_f` bounds the encoded size of `f`'s output, which is both the argument size at which `g`'s
bounds have to be evaluated and the amount of tape the intermediate result occupies — hence its
appearance in the space bound. -/
lemma ComputableUpTo.comp {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]
    {f : α → β} {g : β → γ} {t_f s_f t_g s_g S_f : ℕ → ℕ}
    (hf : ComputableUpTo f t_f s_f) (hg : ComputableUpTo g t_g s_g)
    (h_t_g : Monotone t_g) (h_s_g : Monotone s_g)
    (h_out : ∀ a, (DataEncode.encode (f a)).size ≤ S_f (DataEncode.encode a).size) :
    ComputableUpTo (g ∘ f)
      (fun n => t_f n + t_g (S_f n))
      (fun n => s_f n + s_g (S_f n) + S_f n) := by
  sorry

end MultiTapeTM

end Turing
