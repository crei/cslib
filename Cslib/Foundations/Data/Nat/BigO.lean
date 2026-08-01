/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# A big-O calculus for natural number bound functions

Complexity theory is full of statements of the shape "the running time is `O(f)`". This file
provides a calculus for such bounds that is meant to be used with the resource bounds of Turing
machines, in `Cslib.Computability.Machines.Turing.MultiTape.Classes`.

## Design

Bound functions are *bundled*: a `BoundFun` is a monotone function `ℕ → ℕ` that is at least `1`.
Both assumptions are harmless for resource bounds (a machine reading its input already takes at
least one step, and resource bounds are traditionally assumed to be monotone), and both buy a lot:

* Since `f ≥ 1`, domination `∃ c, ∀ n, f n ≤ c * g n` needs neither an additive constant nor an
  eventuality threshold: constants and finitely many exceptional arguments are absorbed by the
  multiplicative constant. So there is a *single* relation, and it is registered as the `≤` of a
  `Preorder BoundFun`. **`f ≤ g` therefore means `f = O(g)`, not `∀ n, f n ≤ g n`.**
* Since bound functions are bundled, the calculus is an algebra on `BoundFun` (`*`, `+`, `^`,
  `exp2`) rather than on lambda terms. Goals are lambda-free, `calc` works, and the covariance
  instances `MulLeftMono`/`MulRightMono` make Mathlib's generic ordered-algebra lemmas
  (`mul_le_mul'`, `pow_le_pow_left'`, `add_le_add`) and `gcongr` apply out of the box.
* Since bound functions are monotone, a plain function `F : ℕ → ℕ` (a concrete running time, which
  need be neither monotone nor nonzero) is turned into a bound function by its monotone envelope
  `BoundFun.ofFun`. `BoundFun.le_ofFun` and `BoundFun.ofFun_le` are the interface: a pointwise
  bound `∀ n, F n ≤ c * g n` gives `ofFun F ≤ g` with no monotonicity side goal.

The atoms are `BoundFun.const c` (the constant `c + 1`), `BoundFun.linear` (`n + 1`),
`BoundFun.log` (`Nat.log 2 n + 1`) and `BoundFun.exp2 e` (`2 ^ e n`). All of them are normalised by
a `+ 1` so that they are at least `1`; this does not change the class of dominated functions,
since all constants are equivalent (`BoundFun.const_le`) and `n + 1` dominates `n`.

Note that `exp2` is *not* monotone for `≤`: `e₁ ≤ e₂` only bounds `e₁` by `c * e₂`, and
`2 ^ (c * e₂ n)` is not `O(2 ^ e₂ n)`. The correct rules are `BoundFun.exp2_le_exp2` (pointwise
comparison of exponents) and `BoundFun.exp2_le_exp2_of_le_add` (pointwise comparison up to an
additive constant in the exponent, which the multiplicative constant absorbs).

For the same reason, `2 ^ O(s)` is not of the form `O(g)` for a single bound function `g`: it is a
genuine *family*. Such families are therefore named once and for all as sets of bound functions
(`BoundFun.ExpO`, `BoundFun.PolyO`, `BoundFun.ExpPolyO`), and the calculus is lifted to them
(`BoundFun.ExpO_subset_ExpO`, `BoundFun.mul_mem_ExpO`, ...). Statements about these classes mention
no constants at all, and the exponent constant of `2 ^ O(s)` is absorbed once, in
`BoundFun.ExpO_subset_ExpO`.

## Main results

* `BoundFun`, its algebra (`CommMonoid`, `Add`, `exp2`) and the `Preorder` whose `≤` is
  domination.
* `BoundFun.ofFun`, `BoundFun.le_ofFun`, `BoundFun.ofFun_le`: the entry point for plain functions.
* Base facts such as `BoundFun.one_le`, `BoundFun.const_le`, `BoundFun.le_mul_right`,
  `BoundFun.log_le_linear`, `BoundFun.linear_le_exp2_linear`, `BoundFun.exp2_log_le_linear`.
* `BoundFun.exp2_add`, `BoundFun.exp2_const_mul`: the exponential algebra, as equalities.
* Absorption facts such as `BoundFun.linear_mul_exp2_le`, `BoundFun.exp2_const_mul_log_le` and
  `BoundFun.exp2_const_mul_pow_le`.
* The O-classes `BoundFun.O`, `BoundFun.ExpO`, `BoundFun.PolyO` and `BoundFun.ExpPolyO`, together
  with their closure properties. These are sets of bound functions, which is what allows statements
  such as `2 ^ O(s)` to be made without mentioning any constant.
* The `bigO` tactic, which normalises the exponential algebra, descends with `gcongr` and closes
  the resulting leaves with the base facts.
-/

@[expose] public section

namespace Cslib

/-- A bound function: a monotone function `ℕ → ℕ` that is at least `1`. See the module
documentation for why these assumptions are made. -/
structure BoundFun where
  /-- The underlying function. -/
  toFun : ℕ → ℕ
  /-- Bound functions are monotone. -/
  monotone' : Monotone toFun
  /-- Bound functions are at least `1`. -/
  one_le_apply' : 1 ≤ toFun 0

namespace BoundFun

instance : CoeFun BoundFun fun _ => ℕ → ℕ := ⟨toFun⟩

@[simp] theorem coe_mk (f : ℕ → ℕ) (hm hp) : ⇑(mk f hm hp) = f := rfl

@[ext] theorem ext {f g : BoundFun} (h : ∀ n, f n = g n) : f = g := by
  cases f; cases g; simpa using funext h

/-- Bound functions are monotone. -/
theorem monotone (f : BoundFun) : Monotone ⇑f := f.monotone'

/-- Bound functions are at least `1` everywhere. -/
theorem one_le_apply (f : BoundFun) (n : ℕ) : 1 ≤ f n :=
  f.one_le_apply'.trans (f.monotone (Nat.zero_le n))

/-- Bound functions are positive. -/
theorem pos_apply (f : BoundFun) (n : ℕ) : 0 < f n := f.one_le_apply n

/-! ### Algebra -/

/-- The pointwise product of bound functions. -/
protected def mul (f g : BoundFun) : BoundFun :=
  ⟨fun n => f n * g n, fun _ _ h => Nat.mul_le_mul (f.monotone h) (g.monotone h),
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (f.pos_apply 0).ne' (g.pos_apply 0).ne')⟩

/-- The constant bound function `1`. -/
protected def one : BoundFun := ⟨fun _ => 1, monotone_const, le_rfl⟩

/-- The pointwise `k`-th power of a bound function. -/
protected def pow (f : BoundFun) (k : ℕ) : BoundFun :=
  ⟨fun n => f n ^ k, fun _ _ h => Nat.pow_le_pow_left (f.monotone h) k,
    Nat.one_le_pow _ _ (f.pos_apply 0)⟩

instance : CommMonoid BoundFun where
  mul := BoundFun.mul
  one := BoundFun.one
  npow k f := f.pow k
  mul_assoc _ _ _ := by ext n; exact Nat.mul_assoc ..
  one_mul _ := by ext n; exact Nat.one_mul ..
  mul_one _ := by ext n; exact Nat.mul_one ..
  mul_comm _ _ := by ext n; exact Nat.mul_comm ..
  npow_zero _ := by ext n; exact pow_zero ..
  npow_succ _ _ := by ext n; exact pow_succ ..

/-- The pointwise sum of bound functions. -/
instance : Add BoundFun :=
  ⟨fun f g => ⟨fun n => f n + g n, fun _ _ h => Nat.add_le_add (f.monotone h) (g.monotone h),
    (f.one_le_apply 0).trans (Nat.le_add_right ..)⟩⟩

@[simp] theorem mul_apply (f g : BoundFun) (n : ℕ) : (f * g) n = f n * g n := rfl
@[simp] theorem one_apply (n : ℕ) : (1 : BoundFun) n = 1 := rfl
@[simp] theorem pow_apply (f : BoundFun) (k n : ℕ) : (f ^ k) n = f n ^ k := rfl
@[simp] theorem add_apply (f g : BoundFun) (n : ℕ) : (f + g) n = f n + g n := rfl

/-! ### Atoms -/

/-- The constant bound function with value `c + 1`. The `+ 1` normalises the value to be at least
`1`; since all constants dominate each other (`const_le`), this is no loss. -/
def const (c : ℕ) : BoundFun := ⟨fun _ => c + 1, monotone_const, Nat.le_add_left ..⟩

/-- The bound function `n + 1`, the normalised form of the identity. -/
def linear : BoundFun := ⟨fun n => n + 1, fun _ _ h => Nat.add_le_add_right h 1, Nat.le_refl 1⟩

/-- The bound function `Nat.log 2 n + 1`, the normalised binary logarithm. It agrees with
`Nat.log2 n + 1` by `Nat.log2_eq_log_two`. -/
def log : BoundFun :=
  ⟨fun n => Nat.log 2 n + 1, fun _ _ h => Nat.add_le_add_right (Nat.log_mono_right h) 1,
    Nat.le_add_left ..⟩

/-- The bound function `2 ^ e n`. -/
def exp2 (e : BoundFun) : BoundFun :=
  ⟨fun n => 2 ^ e n, fun _ _ h => Nat.pow_le_pow_right (by omega) (e.monotone h),
    Nat.one_le_two_pow⟩

@[simp] theorem const_apply (c n : ℕ) : const c n = c + 1 := rfl
@[simp] theorem linear_apply (n : ℕ) : linear n = n + 1 := rfl
@[simp] theorem log_apply (n : ℕ) : log n = Nat.log 2 n + 1 := rfl
@[simp] theorem exp2_apply (e : BoundFun) (n : ℕ) : exp2 e n = 2 ^ e n := rfl

/-! ### Domination -/

/-- Domination of bound functions is the `≤` of a `Preorder`: `f ≤ g` means `f = O(g)`, i.e.
`f n ≤ c * g n` for some constant `c` and all `n`. Since bound functions are at least `1`, no
additive constant and no eventuality threshold are needed. -/
instance : Preorder BoundFun where
  le f g := ∃ c, ∀ n, f n ≤ c * g n
  le_refl _ := ⟨1, fun n => by simp⟩
  le_trans _ _ _ := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, fun n => (ha n).trans ?_⟩
    calc _ ≤ a * (b * _) := by gcongr; exact hb n
      _ = a * b * _ := by ring

theorem le_def {f g : BoundFun} : f ≤ g ↔ ∃ c, ∀ n, f n ≤ c * g n := Iff.rfl

/-- Introduction rule for domination. -/
theorem le_of_forall_le_mul {f g : BoundFun} {c : ℕ} (h : ∀ n, f n ≤ c * g n) : f ≤ g := ⟨c, h⟩

/-- A pointwise inequality is a domination. -/
theorem le_of_forall_le {f g : BoundFun} (h : ∀ n, f n ≤ g n) : f ≤ g :=
  le_of_forall_le_mul (c := 1) fun n => by simpa using h n

/-- Elimination rule for domination. -/
theorem exists_le_mul {f g : BoundFun} (h : f ≤ g) : ∃ c, ∀ n, f n ≤ c * g n := h

instance : MulLeftMono BoundFun :=
  ⟨fun f _ _ h => by
    obtain ⟨c, hc⟩ := h
    refine ⟨c, fun n => ?_⟩
    simp only [mul_apply]
    calc f n * _ ≤ f n * (c * _) := by gcongr; exact hc n
      _ = c * (f n * _) := by ring⟩

instance : MulRightMono BoundFun :=
  ⟨fun f _ _ h => by
    obtain ⟨c, hc⟩ := h
    refine ⟨c, fun n => ?_⟩
    simp only [mul_apply]
    calc _ * f n ≤ c * _ * f n := by gcongr; exact hc n
      _ = c * (_ * f n) := by ring⟩

instance : AddLeftMono BoundFun :=
  ⟨fun f g₁ g₂ (h : g₁ ≤ g₂) => by
    obtain ⟨c, hc⟩ := h
    refine ⟨c + 1, fun n => ?_⟩
    have h1 := hc n
    have h2 : (c + 1) * (f n + g₂ n) = c * g₂ n + (f n + c * f n + g₂ n) := by ring
    simp only [add_apply]
    omega⟩

instance : AddRightMono BoundFun :=
  ⟨fun f g₁ g₂ (h : g₁ ≤ g₂) => by
    obtain ⟨c, hc⟩ := h
    refine ⟨c + 1, fun n => ?_⟩
    have h1 := hc n
    have h2 : (c + 1) * (g₂ n + f n) = c * g₂ n + (f n + c * f n + g₂ n) := by ring
    simp only [Function.swap, add_apply]
    omega⟩

/-! ### Base facts -/

/-- Every bound function dominates the constant `1`. -/
@[simp] theorem one_le (f : BoundFun) : 1 ≤ f :=
  le_of_forall_le fun n => f.one_le_apply n

/-- Constants are dominated by `1`. -/
theorem const_le_one (c : ℕ) : const c ≤ 1 :=
  le_of_forall_le_mul (c := c + 1) fun _ => by simp

/-- Every constant is dominated by every bound function: constants are the bottom of the order. -/
@[simp] theorem const_le (c : ℕ) (f : BoundFun) : const c ≤ f := (const_le_one c).trans (one_le f)

/-- A product dominates its left factor. -/
@[simp] theorem le_mul_right (f g : BoundFun) : f ≤ f * g :=
  le_of_forall_le fun n => Nat.le_mul_of_pos_right _ (g.pos_apply n)

/-- A product dominates its right factor. -/
@[simp] theorem le_mul_left (f g : BoundFun) : g ≤ f * g :=
  le_of_forall_le fun n => Nat.le_mul_of_pos_left _ (f.pos_apply n)

/-- A sum is dominated by any common upper bound; sums are suprema for `≤`. -/
theorem add_le {f g h : BoundFun} (h₁ : f ≤ h) (h₂ : g ≤ h) : f + g ≤ h := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  refine ⟨a + b, fun n => ?_⟩
  have := ha n
  have := hb n
  have : (a + b) * h n = a * h n + b * h n := by ring
  simp only [add_apply]
  omega

/-- A sum dominates its left summand. -/
@[simp] theorem le_add_right (f g : BoundFun) : f ≤ f + g :=
  le_of_forall_le fun _ => Nat.le_add_right ..

/-- A sum dominates its right summand. -/
@[simp] theorem le_add_left (f g : BoundFun) : g ≤ f + g :=
  le_of_forall_le fun _ => Nat.le_add_left ..

/-- Constant factors can be dropped. -/
theorem const_mul_le_of_le {f g : BoundFun} {c : ℕ} (h : f ≤ g) : const c * f ≤ g :=
  calc const c * f ≤ 1 * f := by gcongr; exact const_le_one c
    _ = f := one_mul f
    _ ≤ g := h

/-- A product is dominated by a bound of its left factor if the right factor is constant. -/
theorem mul_le_of_le_of_le_one {f g h : BoundFun} (h₁ : f ≤ h) (h₂ : g ≤ 1) : f * g ≤ h :=
  calc f * g ≤ h * 1 := mul_le_mul' h₁ h₂
    _ = h := mul_one h

/-- A bound function is dominated by its powers. -/
theorem le_pow_of_le {f g : BoundFun} {k : ℕ} (h : f ≤ g) : f ≤ g ^ (k + 1) :=
  h.trans <| le_of_forall_le fun n => Nat.le_self_pow (by omega) _

/-- Powers grow with the exponent. -/
theorem pow_le_pow_exp (f : BoundFun) {k l : ℕ} (h : k ≤ l) : f ^ k ≤ f ^ l :=
  le_of_forall_le fun n => Nat.pow_le_pow_right (f.one_le_apply n) h

/-! ### The exponential -/

/-- The exponential turns sums into products. -/
theorem exp2_add (e₁ e₂ : BoundFun) : exp2 (e₁ + e₂) = exp2 e₁ * exp2 e₂ := by
  ext n; exact pow_add ..

/-- A constant factor in the exponent becomes a power. -/
theorem exp2_const_mul (c : ℕ) (e : BoundFun) : exp2 (const c * e) = exp2 e ^ (c + 1) := by
  ext n; rw [exp2_apply, mul_apply, const_apply, pow_apply, exp2_apply, ← pow_mul, Nat.mul_comm]

/-- Two exponentials with a constant in the exponent multiply to a single one: the constants add
(the `+ 1` accounts for the normalisation of `const`). -/
theorem exp2_const_mul_mul (a b : ℕ) (e : BoundFun) :
    exp2 (const a * e) * exp2 (const b * e) = exp2 (const (a + b + 1) * e) := by
  ext n
  simp only [mul_apply, exp2_apply, const_apply, ← pow_add]
  ring_nf

/-- The exponential is monotone for the *pointwise* order on exponents. It is not monotone for
domination of exponents. -/
theorem exp2_le_exp2 {e₁ e₂ : BoundFun} (h : ∀ n, e₁ n ≤ e₂ n) : exp2 e₁ ≤ exp2 e₂ :=
  le_of_forall_le fun n => Nat.pow_le_pow_right (by omega) (h n)

/-- An additive constant in the exponent is absorbed by the multiplicative constant of `≤`. -/
theorem exp2_le_exp2_of_le_add {e₁ e₂ : BoundFun} {K : ℕ} (h : ∀ n, e₁ n ≤ e₂ n + K) :
    exp2 e₁ ≤ exp2 e₂ :=
  le_of_forall_le_mul (c := 2 ^ K) fun n =>
    calc 2 ^ e₁ n ≤ 2 ^ (e₂ n + K) := Nat.pow_le_pow_right (by omega) (h n)
      _ = 2 ^ K * 2 ^ e₂ n := by rw [pow_add]; ring

/-- A constant exponent gives a constant. -/
@[simp] theorem exp2_const_le_one (c : ℕ) : exp2 (const c) ≤ 1 :=
  le_of_forall_le_mul (c := 2 ^ (c + 1)) fun _ => by simp

/-- `log₂ n ≤ n`. -/
@[simp] theorem log_le_linear : log ≤ linear :=
  le_of_forall_le fun n => Nat.add_le_add_right (Nat.log_le_self 2 n) 1

/-- `n + 1 ≤ 2 ^ (log₂ n + 1)`. -/
@[simp] theorem linear_le_exp2_log : linear ≤ exp2 log :=
  le_of_forall_le fun n => Nat.lt_pow_succ_log_self (by omega) n

/-- `2 ^ (log₂ n + 1) = O(n)`. -/
@[simp] theorem exp2_log_le_linear : exp2 log ≤ linear :=
  le_of_forall_le_mul (c := 2) fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · calc 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by rw [pow_succ]; ring
        _ ≤ 2 * n := by gcongr; exact Nat.pow_log_le_self 2 hn.ne'
        _ ≤ 2 * (n + 1) := by gcongr; omega

/-- `n + 1 ≤ 2 ^ (n + 1)`. -/
@[simp] theorem linear_le_exp2_linear : linear ≤ exp2 linear :=
  le_of_forall_le fun n => by
    calc n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-! ### Plain functions -/

/-- The monotone envelope of a plain function: `ofFun F n` is `1` plus the maximum of `F` on
`[0, n]`. This is the way a concrete resource bound (which is in general neither monotone nor
nonzero) enters the calculus. -/
def ofFun (F : ℕ → ℕ) : BoundFun :=
  ⟨fun n => (Finset.range (n + 1)).sup F + 1,
    fun _ _ h =>
      Nat.add_le_add_right
        (Finset.sup_mono (Finset.range_subset_range.2 (Nat.add_le_add_right h 1))) 1,
    Nat.le_add_left ..⟩

/-- A function is bounded by its monotone envelope. -/
theorem le_ofFun (F : ℕ → ℕ) (n : ℕ) : F n ≤ ofFun F n := by
  have := Finset.le_sup (f := F) (Finset.self_mem_range_succ n)
  simp only [ofFun]
  omega

/-- The key intro rule: a pointwise bound of a plain function by a constant multiple of a bound
function dominates the whole monotone envelope, with no monotonicity side goal. -/
theorem ofFun_le {F : ℕ → ℕ} {g : BoundFun} {c : ℕ} (h : ∀ n, F n ≤ c * g n) : ofFun F ≤ g := by
  refine le_of_forall_le_mul (c := c + 1) fun n => ?_
  have hsup : (Finset.range (n + 1)).sup F ≤ c * g n := by
    refine Finset.sup_le fun m hm => (h m).trans ?_
    gcongr
    exact g.monotone (by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hm)
  have h1 : 1 ≤ g n := g.one_le_apply n
  have : (c + 1) * g n = c * g n + g n := by ring
  simp only [ofFun]
  omega

/-- The envelope of a constant function is constant. -/
theorem ofFun_const_le (a : ℕ) : ofFun (fun _ => a) ≤ 1 := ofFun_le (c := a) fun _ => by simp

/-- The envelope of a product is dominated by the product of the envelopes. -/
theorem ofFun_mul_le (F G : ℕ → ℕ) : ofFun (fun n => F n * G n) ≤ ofFun F * ofFun G := by
  refine le_of_forall_le fun n => ?_
  have hsup : (Finset.range (n + 1)).sup (fun n => F n * G n)
      ≤ (Finset.range (n + 1)).sup F * (Finset.range (n + 1)).sup G :=
    Finset.sup_le fun m hm => Nat.mul_le_mul (Finset.le_sup hm) (Finset.le_sup hm)
  simp only [ofFun, mul_apply]
  have hring : ((Finset.range (n + 1)).sup F + 1) * ((Finset.range (n + 1)).sup G + 1)
      = (Finset.range (n + 1)).sup F * (Finset.range (n + 1)).sup G
        + ((Finset.range (n + 1)).sup F + (Finset.range (n + 1)).sup G + 1) := by ring
  omega

/-- Bridge from a plain exponential bound to the `exp2` algebra: a bound of the shape
`a * 2 ^ (c * e n)` is `O(2 ^ ((c + 1) * e n))`, which is `exp2 (const c * e)`. -/
theorem ofFun_le_exp2_const_mul {F : ℕ → ℕ} {e : BoundFun} {a c : ℕ}
    (h : ∀ n, F n ≤ a * 2 ^ (c * e n)) : ofFun F ≤ exp2 (const c * e) :=
  ofFun_le (c := a) fun n => (h n).trans <| Nat.mul_le_mul_left a <|
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (Nat.le_succ c))

/-- The envelope of `n + k` is linear: additive constants are absorbed. -/
theorem ofFun_add_const_le_linear (k : ℕ) : ofFun (fun n => n + k) ≤ linear :=
  ofFun_le (c := k + 1) fun n => by
    have h : (k + 1) * linear n = n + k + (k * n + 1) := by simp only [linear_apply]; ring
    rw [h]
    exact Nat.le_add_right ..

/-! ### Absorption facts -/

/-- A linear factor is absorbed by an exponential whose exponent dominates the logarithm: this is
the standard hypothesis `s(n) ≥ log n` of the space-to-time theorem. -/
theorem linear_mul_exp2_le {s : BoundFun} {d : ℕ} (hd : ∀ n, log n ≤ d * s n) (c : ℕ) :
    linear * exp2 (const c * s) ≤ exp2 (const (c + d) * s) := by
  refine le_of_forall_le fun n => ?_
  have hlin : n + 1 ≤ 2 ^ (d * s n) :=
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) n).trans_le
      (Nat.pow_le_pow_right (by omega) (hd n))
  simp only [mul_apply, linear_apply, exp2_apply, const_apply]
  calc (n + 1) * 2 ^ ((c + 1) * s n) ≤ 2 ^ (d * s n) * 2 ^ ((c + 1) * s n) := by gcongr
    _ = 2 ^ ((c + d + 1) * s n) := by rw [← pow_add]; ring_nf

/-- `2 ^ (c · log n)` is polynomial. The `bigO` tactic, defined below, closes this goal as well. -/
theorem exp2_const_mul_log_le (c : ℕ) : exp2 (const c * log) ≤ linear ^ (c + 1) := by
  rw [exp2_const_mul]
  gcongr
  exact exp2_log_le_linear

private theorem mul_pow_le_pow_succ_add (c m k : ℕ) :
    c * m ^ k ≤ m ^ (k + 1) + c ^ (k + 1) := by
  rcases le_or_gt c m with h | h
  · calc c * m ^ k ≤ m * m ^ k := by gcongr
      _ = m ^ (k + 1) := by ring
      _ ≤ m ^ (k + 1) + c ^ (k + 1) := Nat.le_add_right ..
  · calc c * m ^ k ≤ c * c ^ k := by gcongr; omega
      _ = c ^ (k + 1) := by ring
      _ ≤ m ^ (k + 1) + c ^ (k + 1) := Nat.le_add_left ..

/-- A constant factor in a polynomial exponent is absorbed by the next power. -/
theorem exp2_const_mul_pow_le (c k : ℕ) :
    exp2 (const c * linear ^ (k + 1)) ≤ exp2 (linear ^ (k + 2)) :=
  exp2_le_exp2_of_le_add (K := (c + 1) ^ (k + 2)) fun n => by
    simpa using mul_pow_le_pow_succ_add (c + 1) (n + 1) (k + 1)

/-! ### O-classes

`2 ^ O(s)` is not a single bound function but a *family*, so the statements about it are about a
set of bound functions. The classes below are the ones that occur in complexity theory; they are
all lower sets for domination, and closed under products, which is what makes the constants of the
underlying calculus invisible in statements about them. -/

/-- The class `O(g)` of bound functions dominated by `g`. -/
def O (g : BoundFun) : Set BoundFun := {f | f ≤ g}

/-- The class `2 ^ O(s)` of bound functions dominated by `2 ^ (c * s)` for some constant `c`. -/
def ExpO (s : BoundFun) : Set BoundFun := {f | ∃ c, f ≤ exp2 (const c * s)}

/-- The class `poly(n) = n ^ O(1)` of polynomially bounded bound functions. -/
def PolyO : Set BoundFun := {f | ∃ k, f ≤ linear ^ k}

/-- The class `2 ^ poly(n)` of bound functions with a polynomial exponent. -/
def ExpPolyO : Set BoundFun := {f | ∃ k, f ≤ exp2 (linear ^ k)}

@[simp] theorem mem_O {f g : BoundFun} : f ∈ O g ↔ f ≤ g := Iff.rfl
@[simp] theorem mem_ExpO {f s : BoundFun} : f ∈ ExpO s ↔ ∃ c, f ≤ exp2 (const c * s) := Iff.rfl
@[simp] theorem mem_PolyO {f : BoundFun} : f ∈ PolyO ↔ ∃ k, f ≤ linear ^ k := Iff.rfl
@[simp] theorem mem_ExpPolyO {f : BoundFun} : f ∈ ExpPolyO ↔ ∃ k, f ≤ exp2 (linear ^ k) := Iff.rfl

/-! #### Lower-closedness -/

/-- `O(g)` is a lower set for domination. -/
theorem mem_O_of_le {f g e : BoundFun} (h : f ≤ g) (hg : g ∈ O e) : f ∈ O e := h.trans hg

/-- `2 ^ O(s)` is a lower set for domination. -/
theorem mem_ExpO_of_le {f g s : BoundFun} (h : f ≤ g) (hg : g ∈ ExpO s) : f ∈ ExpO s :=
  let ⟨c, hc⟩ := hg; ⟨c, h.trans hc⟩

/-- `poly(n)` is a lower set for domination. -/
theorem mem_PolyO_of_le {f g : BoundFun} (h : f ≤ g) (hg : g ∈ PolyO) : f ∈ PolyO :=
  let ⟨k, hk⟩ := hg; ⟨k, h.trans hk⟩

/-- `2 ^ poly(n)` is a lower set for domination. -/
theorem mem_ExpPolyO_of_le {f g : BoundFun} (h : f ≤ g) (hg : g ∈ ExpPolyO) : f ∈ ExpPolyO :=
  let ⟨k, hk⟩ := hg; ⟨k, h.trans hk⟩

/-- `O` is monotone. -/
theorem O_subset_O {g₁ g₂ : BoundFun} (h : g₁ ≤ g₂) : O g₁ ⊆ O g₂ := fun _ hf => hf.trans h

/-- Any dominated bound function generates a subclass. -/
theorem O_subset_ExpO {g s : BoundFun} (h : g ∈ ExpO s) : O g ⊆ ExpO s :=
  fun _ hf => mem_ExpO_of_le hf h

/-- **The `O` in the exponent absorbs domination of the exponent**: this is the lemma that makes
the constant of a space bound invisible in `2 ^ O(s)`. -/
theorem ExpO_subset_ExpO {s₁ s₂ : BoundFun} (h : s₁ ≤ s₂) : ExpO s₁ ⊆ ExpO s₂ := by
  rintro f ⟨c, hf⟩
  obtain ⟨d, hd⟩ := h
  refine ⟨(c + 1) * d, hf.trans (exp2_le_exp2 fun n => ?_)⟩
  simp only [mul_apply, const_apply]
  calc (c + 1) * s₁ n ≤ (c + 1) * (d * s₂ n) := by gcongr; exact hd n
    _ = (c + 1) * d * s₂ n := by ring
    _ ≤ ((c + 1) * d + 1) * s₂ n := by gcongr; omega

/-! #### Closure under multiplication -/

/-- `1` is in `2 ^ O(s)`. -/
theorem one_mem_ExpO (s : BoundFun) : (1 : BoundFun) ∈ ExpO s := ⟨0, one_le _⟩

/-- `2 ^ O(s)` is closed under products, since the exponents add. -/
theorem mul_mem_ExpO {f g s : BoundFun} (hf : f ∈ ExpO s) (hg : g ∈ ExpO s) : f * g ∈ ExpO s :=
  let ⟨a, ha⟩ := hf
  let ⟨b, hb⟩ := hg
  ⟨a + b + 1, by rw [← exp2_const_mul_mul]; exact mul_le_mul' ha hb⟩

/-! #### Membership in `2 ^ O(s)`

These are the rules by which concrete bounds enter `2 ^ O(σ)`. Together they cover the shapes that
occur in configuration counts: constants, polynomials in `σ` and powers of a fixed base with an
exponent that is affine in `σ`. Each of them provides the constant in the exponent, so consumers
never have to exhibit one. -/

/-- Polynomials in `σ` are `2 ^ O(σ)`: this is the textbook `poly(s) ⊆ 2^{O(s)}`. -/
theorem pow_mem_ExpO (k : ℕ) (σ : BoundFun) : σ ^ k ∈ ExpO σ := by
  refine ⟨k, le_of_forall_le fun n => ?_⟩
  simp only [pow_apply, exp2_apply, mul_apply, const_apply]
  calc σ n ^ k ≤ (2 ^ σ n) ^ k := Nat.pow_le_pow_left Nat.lt_two_pow_self.le k
    _ = 2 ^ (k * σ n) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ ((k + 1) * σ n) := Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_right _ (Nat.le_succ k))

/-- A plain function that is `O(σ)` pointwise has all its powers in `2 ^ O(σ)`. -/
theorem ofFun_pow_mem_ExpO {F : ℕ → ℕ} {σ : BoundFun} (k c : ℕ) (h : ∀ n, F n ≤ c * σ n) :
    ofFun (fun n => F n ^ k) ∈ ExpO σ :=
  mem_ExpO_of_le
    (ofFun_le (c := c ^ k) fun n => by
      calc F n ^ k ≤ (c * σ n) ^ k := Nat.pow_le_pow_left (h n) k
        _ = c ^ k * (σ ^ k) n := by simp only [pow_apply, mul_pow])
    (pow_mem_ExpO k σ)

/-- A power of a fixed base with an exponent that is affine in `σ` is `2 ^ O(σ)`: the change of
base only costs a factor in the exponent. -/
theorem ofFun_base_pow_mem_ExpO {F : ℕ → ℕ} {σ : BoundFun} (B a b : ℕ)
    (h : ∀ n, F n ≤ a * σ n + b) : ofFun (fun n => B ^ F n) ∈ ExpO σ := by
  refine ⟨B * a, ofFun_le_exp2_const_mul (a := 2 ^ (B * b)) fun n => ?_⟩
  calc B ^ F n ≤ (2 ^ B) ^ F n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ ≤ (2 ^ B) ^ (a * σ n + b) := Nat.pow_le_pow_right Nat.one_le_two_pow (h n)
    _ = 2 ^ (B * b) * 2 ^ (B * a * σ n) := by rw [← pow_mul, ← pow_add]; ring_nf

/-- A constant is `2 ^ O(σ)`. -/
theorem ofFun_const_mem_ExpO (a : ℕ) (σ : BoundFun) : ofFun (fun _ => a) ∈ ExpO σ :=
  mem_ExpO_of_le (ofFun_const_le a) (one_mem_ExpO σ)

/-- Products of plain functions in `2 ^ O(σ)` are in `2 ^ O(σ)`. This is the form in which a
configuration count is decomposed into its factors. -/
theorem ofFun_mul_mem_ExpO {F G : ℕ → ℕ} {σ : BoundFun} (hF : ofFun F ∈ ExpO σ)
    (hG : ofFun G ∈ ExpO σ) : ofFun (fun n => F n * G n) ∈ ExpO σ :=
  mem_ExpO_of_le (ofFun_mul_le F G) (mul_mem_ExpO hF hG)

/-- `1` is polynomially bounded. -/
theorem one_mem_PolyO : (1 : BoundFun) ∈ PolyO := ⟨0, by simp⟩

/-- Powers of `linear` are polynomially bounded. -/
theorem pow_linear_mem_PolyO (k : ℕ) : linear ^ k ∈ PolyO := ⟨k, le_rfl⟩

/-- `poly(n)` is closed under products. -/
theorem mul_mem_PolyO {f g : BoundFun} (hf : f ∈ PolyO) (hg : g ∈ PolyO) : f * g ∈ PolyO :=
  let ⟨k, hk⟩ := hf
  let ⟨l, hl⟩ := hg
  ⟨k + l, by rw [pow_add]; exact mul_le_mul' hk hl⟩

/-- `linear` has a polynomial exponential bound. -/
theorem linear_mem_ExpPolyO : linear ∈ ExpPolyO := ⟨1, by rw [pow_one]; simp⟩

/-- `2 ^ poly(n)` is closed under products. -/
theorem mul_mem_ExpPolyO {f g : BoundFun} (hf : f ∈ ExpPolyO) (hg : g ∈ ExpPolyO) :
    f * g ∈ ExpPolyO := by
  obtain ⟨k, hk⟩ := hf
  obtain ⟨l, hl⟩ := hg
  refine ⟨max k l + 1, (mul_le_mul' hk hl).trans ?_⟩
  rw [← exp2_add]
  refine exp2_le_exp2_of_le_add (K := 2) fun n => ?_
  simp only [add_apply, pow_apply, linear_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h₁ : (n + 1) ^ k ≤ (n + 1) ^ max k l :=
      Nat.pow_le_pow_right (by omega) (le_max_left ..)
    have h₂ : (n + 1) ^ l ≤ (n + 1) ^ max k l :=
      Nat.pow_le_pow_right (by omega) (le_max_right ..)
    have h₃ : 2 * (n + 1) ^ max k l ≤ (n + 1) ^ (max k l + 1) := by
      calc 2 * (n + 1) ^ max k l ≤ (n + 1) * (n + 1) ^ max k l := by gcongr; omega
        _ = (n + 1) ^ (max k l + 1) := by rw [pow_succ]; ring
    omega

/-! #### Interaction of the classes -/

/-- `2 ^ O(log n)` is polynomial. -/
theorem ExpO_log_subset_PolyO : ExpO log ⊆ PolyO :=
  fun _ ⟨c, hc⟩ => ⟨c + 1, hc.trans (exp2_const_mul_log_le c)⟩

/-- `2 ^ O(s)` is `2 ^ poly(n)` for a polynomially bounded `s`. -/
theorem ExpO_subset_ExpPolyO {s : BoundFun} (hs : s ∈ PolyO) : ExpO s ⊆ ExpPolyO := by
  obtain ⟨k, c₁, h₁⟩ := hs
  rintro f ⟨c, hf⟩
  refine ⟨k + 1, hf.trans (exp2_le_exp2_of_le_add (K := ((c + 1) * c₁) ^ (k + 1)) fun n => ?_)⟩
  simp only [mul_apply, const_apply, pow_apply, linear_apply]
  calc (c + 1) * s n ≤ (c + 1) * (c₁ * (n + 1) ^ k) := by gcongr; simpa using h₁ n
    _ = (c + 1) * c₁ * (n + 1) ^ k := by ring
    _ ≤ (n + 1) ^ (k + 1) + ((c + 1) * c₁) ^ (k + 1) := mul_pow_le_pow_succ_add ..

/-- A linear factor is absorbed by `2 ^ O(s)` if `s` dominates the logarithm. -/
theorem linear_mul_mem_ExpO {f s : BoundFun} (h : log ≤ s) (hf : f ∈ ExpO s) :
    linear * f ∈ ExpO s :=
  let ⟨d, hd⟩ := h
  let ⟨c, hc⟩ := hf
  ⟨c + d, (mul_le_mul' le_rfl hc).trans (linear_mul_exp2_le hd c)⟩

end BoundFun

open scoped Pointwise

namespace BoundFun

/-- A linear factor is absorbed by `2 ^ O(s)` if `s` dominates the logarithm. This is the set-level
form of `BoundFun.linear_mul_mem_ExpO`, as used for the space-to-time theorem. -/
theorem singleton_linear_mul_ExpO_subset {s : BoundFun} (h : log ≤ s) :
    {linear} * ExpO s ⊆ ExpO s := by
  rw [Set.singleton_mul]
  rintro _ ⟨f, hf, rfl⟩
  exact linear_mul_mem_ExpO h hf

/-- A linear factor times `2 ^ O(s)` for a polynomially bounded `s` is `2 ^ poly(n)`. -/
theorem singleton_linear_mul_ExpO_subset_ExpPolyO {s : BoundFun} (hs : s ∈ PolyO) :
    {linear} * ExpO s ⊆ ExpPolyO := by
  rw [Set.singleton_mul]
  rintro _ ⟨f, hf, rfl⟩
  exact mul_mem_ExpPolyO linear_mem_ExpPolyO (ExpO_subset_ExpPolyO hs hf)

/-! ### The `bigO` tactic

`bigO` normalises the exponential algebra, descends into the structure of the goal with `gcongr`
and the sup/constant rules, and closes the leaves with the base facts, which are `simp` lemmas. -/

end BoundFun

open BoundFun in
/-- Prove a domination goal `f ≤ g` between bound functions (`f = O(g)`). The tactic normalises
the exponential algebra (`exp2_add`, `exp2_const_mul`), descends with `gcongr` and the rules for
sums and constant factors, and discharges the leaves with `simp` using the base facts of the
calculus, or with hypotheses from the context. -/
syntax "bigO" : tactic

open BoundFun in
macro_rules
  | `(tactic| bigO) =>
    `(tactic|
      focus
        (try simp only [BoundFun.exp2_add, BoundFun.exp2_const_mul, mul_one, one_mul, mul_pow,
          pow_one, pow_zero]
         first
           | done
           | assumption
           | (simp; done)
           | (refine BoundFun.add_le ?_ ?_ <;> bigO)
           | (refine BoundFun.const_mul_le_of_le ?_ <;> bigO)
           | (refine BoundFun.le_pow_of_le ?_ <;> bigO)
           | (refine BoundFun.mul_le_of_le_of_le_one ?_ ?_ <;> bigO)
           | (gcongr <;> bigO)))

end Cslib
