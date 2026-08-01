/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.Nat.BigO

/-!
# Tests for the big-O calculus

These examples exercise the algebra of `Cslib.BoundFun`, the `≤` order (which is domination, not
pointwise inequality) and the `bigO` tactic.
-/

open Cslib Cslib.BoundFun

open scoped Pointwise

section Calculus

variable (f g h : BoundFun) (c k : ℕ)

/-- Transitivity in a `calc` block. -/
example : log ≤ exp2 linear :=
  calc log ≤ linear := log_le_linear
    _ ≤ exp2 linear := linear_le_exp2_linear

/-- Constants are absorbed. -/
example : const c ≤ f := by bigO

/-- Additive constants are absorbed. -/
example : (linear + const k) * f ≤ linear * f := by bigO

/-- Constant factors are absorbed. -/
example : const c * (f + const k) ≤ f := by bigO

/-- Polynomial normalisation. -/
example : const 5 * linear ^ 2 + const 3 * linear + const 7 ≤ linear ^ 2 := by bigO

/-- `2 ^ (c · log n)` is polynomial. -/
example : exp2 (const c * log) ≤ linear ^ (c + 1) := by bigO

/-- Products and powers are congruences for domination. -/
example (h₁ : f ≤ g) : f * exp2 log ≤ g * linear := by gcongr; exact exp2_log_le_linear

example (h₁ : f ≤ g) : f ^ k ≤ g ^ k := by gcongr

/-- The exponential turns sums into products. -/
example : exp2 (linear + linear) = exp2 linear * exp2 linear := exp2_add ..

/-- Exponentials are compared through their exponents, pointwise. -/
example : exp2 log ≤ exp2 linear := exp2_le_exp2 fun n => by
  simpa using Nat.log_le_self 2 n

/-- A polynomial factor in the exponent is absorbed by the next power. -/
example : exp2 (const c * linear ^ (k + 1)) ≤ exp2 (linear ^ (k + 2)) := exp2_const_mul_pow_le c k

/-- The absorption of a linear factor into an exponential. -/
example (s : BoundFun) (d : ℕ) (hd : ∀ n, log n ≤ d * s n) :
    linear * exp2 (const c * s) ≤ exp2 (const (c + d) * s) := linear_mul_exp2_le hd c

end Calculus

section OfFun

/-- Plain functions enter the calculus through their monotone envelope. -/
example (F : ℕ → ℕ) (h : ∀ n, F n ≤ 3 * (n + 1)) : ofFun F ≤ linear := ofFun_le h

/-- The envelope dominates the function pointwise. -/
example (F : ℕ → ℕ) (n : ℕ) : F n ≤ ofFun F n := le_ofFun F n

/-- A concrete non-monotone running time. -/
example : ofFun (fun n => if n % 2 = 0 then 5 * n else 2) ≤ linear :=
  ofFun_le (c := 5) fun n => by simp only [linear_apply]; split <;> omega

end OfFun

section OClasses

variable (f g : BoundFun) (c k : ℕ)

/-- Membership in `poly(n)`. -/
example : linear ^ 3 * const 5 ∈ PolyO := mem_PolyO_of_le (by bigO) (pow_linear_mem_PolyO 3)

/-- `2 ^ O(s)` is closed under products. -/
example (s : BoundFun) (hf : f ∈ ExpO s) (hg : g ∈ ExpO s) : f * g ∈ ExpO s := mul_mem_ExpO hf hg

/-- A chain of class inclusions: `2 ^ O(log n) ⊆ poly(n)`, and the classes are lower sets. -/
example (h : f ≤ g) (hg : g ∈ ExpO log) : f ∈ PolyO :=
  ExpO_log_subset_PolyO (mem_ExpO_of_le h hg)

/-- The `O` in the exponent absorbs a domination of the exponent. -/
example (s₁ s₂ : BoundFun) (h : s₁ ≤ s₂) : ExpO s₁ ⊆ ExpO s₂ := ExpO_subset_ExpO h

/-- A linear factor is absorbed by `2 ^ O(s)` when `s` dominates the logarithm. -/
example (s : BoundFun) (h : log ≤ s) : {linear} * ExpO s ⊆ ExpO s :=
  singleton_linear_mul_ExpO_subset h

/-- `2 ^ O(n ^ k)` is `2 ^ poly(n)`. -/
example : ExpO (linear ^ k) ⊆ ExpPolyO := ExpO_subset_ExpPolyO (pow_linear_mem_PolyO k)

/-- Polynomials in `s` are `2 ^ O(s)`. -/
example : linear ^ 4 ∈ ExpO linear := pow_mem_ExpO 4 linear

/-- A power of a fixed base with an affine exponent is `2 ^ O(s)`. -/
example : ofFun (fun n => 5 ^ (3 * n + 2)) ∈ ExpO linear :=
  ofFun_base_pow_mem_ExpO 5 3 2 fun n => by simp only [linear_apply]; omega

/-- Products of plain functions are handled factor by factor. -/
example : ofFun (fun n => 7 * (2 * (n + 1) + 1) ^ 3) ∈ ExpO linear :=
  ofFun_mul_mem_ExpO (ofFun_const_mem_ExpO 7 linear)
    (ofFun_pow_mem_ExpO 3 3 fun n => by simp only [linear_apply]; omega)

end OClasses
