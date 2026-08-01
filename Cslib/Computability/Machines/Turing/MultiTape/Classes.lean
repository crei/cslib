/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Order.Monotone.Defs

import Mathlib.Tactic.Ring
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Foundations.Data.Nat.BigO

/-!
# Complexity classes for deterministic multi-tape Turing machines

This file defines the resource-bounded complexity classes for deterministic multi-tape Turing
machines on top of `DecidableInTimeAndSpace`.

## Design

The general classes `DTIME` and `DSPACE` are defined using a single bound function `ℕ → ℕ` but allow
for `O`-fuzzyness. Some textbooks use exact bounds ([Papadimitriou94]), while others use a
definition similar to this one ([AroraBarak09], [Sipser2013]). The fuzzy definition is justified by
the space and time compression / speedup theorems (which are not proven here) and allow for
easier proofs and simpler theorem statements. Once we have better machinery, we can prove the
compression / speedup theorems and potentially move to exact bounds.

The `O`-fuzziness is expressed by `Cslib.BoundFun`: bound functions are bundled as monotone
functions that are at least `1`, and the `≤` of `BoundFun` *is* domination (`f ≤ g` means
`f = O(g)`). A language is in `DTIME t` if it is decidable within some bound `t'` with `t' ≤ t`.
Since `t' ≤ t` unfolds to `∀ n, t' n ≤ c * t n`, this is equivalent to the formulation with an
explicit constant, recorded as `mem_DTIME_iff` and `mem_DSPACE_iff`; the additive constant of the
usual `c₁ * t n + c₂` formulation is not needed because bound functions are at least `1`.

Concrete resource bounds of machines are plain functions `ℕ → ℕ`, and need be neither monotone nor
nonzero; they enter through the monotone envelope `Cslib.BoundFun.ofFun`, see `mem_DTIME_ofFun`.
Compared to the formulation with plain bound functions, degenerate bounds (non-monotone ones, or
ones that vanish) are no longer expressible; this is intended, and the normalised representatives
`BoundFun.linear` (`n + 1`) and `BoundFun.log` (`log₂ n + 1`) define the same classes as `n` and
`log₂ n` do, since they dominate each other up to constants.

The classes are always relative to an alphabet `Symbol`.

Bounds such as `2^{O(s)}` are not single bound functions but families of them, and are therefore
given by the O-classes of `Cslib.BoundFun` (`BoundFun.ExpO`, `BoundFun.PolyO`,
`BoundFun.ExpPolyO`). The corresponding complexity classes are `DTIMEOf` and `DSPACEOf`, the unions
of the `DTIME` / `DSPACE` classes of the members. Statements about them mention no constants at
all, and inclusions between them reduce to inclusions in the big-O calculus via `DTIMEOf_mono`.
The named classes below are defined in this way; `P_eq_iUnion` and friends relate them to the
formulation as a union over a family of bounds.

## Important Declarations

* `DTIME` - the class of languages decidable in time `O(t(n))` for a bound function `t`.
* `DSPACE` - the class of languages decidable in space `O(s(n))` for a bound function `s`.
* `DTIMEOf`, `DSPACEOf` - the same for a class of bound functions, such as `2^{O(s)}`.
* `mem_DTIME_ofFun`, `mem_DSPACE_ofFun`, `mem_DTIMEOf_ofFun`, `mem_DSPACEOf_ofFun` - membership
  from a concrete, plain resource bound.
* `mem_DTIME_iff`, `mem_DSPACE_iff` - the equivalence with the formulation using an explicit
  constant, i.e. a bound of the shape `c * t n`.
* `DTIME_mono`, `DSPACE_mono`, `DTIMEOf_mono`, `DSPACEOf_mono` - the classes only depend on their
  bound up to `O`.
* `iUnion_DTIME_subset_of_le`, `iUnion_DSPACE_subset_of_le` - the same for unions over a family
  of bounds.
* `DTIMEOf_setOf_exists_le`, `DTIMEOf_O`, `DTIMEOf_ExpO` - the bridges between `DTIMEOf` and the
  formulation as a union over a family of bounds.

Some named complexity classes are defined in the `Classes` namespace:

* `P`, `E`, `EXP`
* `L`, `PSPACE`, `ESPACE`, `EXPSPACE`

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]

-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

variable {Symbol : Type} [Inhabited Symbol]

/-- Monotonicity of `DecidableInTimeAndSpace` in the time bound. -/
lemma DecidableInTimeAndSpace.mono_time {L : Language Symbol} {s : ℕ → ℕ} :
    Monotone (DecidableInTimeAndSpace L · s) := by
  intro t₁ t₂ h hd
  obtain ⟨k, sym, state, emb, tm, hcomp⟩ := hd
  refine ⟨k, sym, state, emb, tm, fun input => ?_⟩
  obtain ⟨t', ht', s', hs', hcs⟩ := hcomp input
  exact ⟨t', ht'.trans (h _), s', hs', hcs⟩

/-- Monotonicity of `DecidableInTimeAndSpace` in the space bound. -/
lemma DecidableInTimeAndSpace.mono_space {L : Language Symbol} {t : ℕ → ℕ} :
    Monotone (DecidableInTimeAndSpace L t ·) := by
  intro s₁ s₂ h hd
  obtain ⟨k, sym, state, emb, tm, hcomp⟩ := hd
  refine ⟨k, sym, state, emb, tm, fun input => ?_⟩
  obtain ⟨t', ht', s', hs', hcs⟩ := hcomp input
  exact ⟨t', ht', s', hs'.trans (h _), hcs⟩

/-- The complexity class of languages decidable in time `O(t)` by a deterministic multi-tape
Turing machine, disregarding the space requirement. -/
def DTIME (t : BoundFun) :=
  {L : Language Symbol | ∃ t' : BoundFun, t' ≤ t ∧ ∃ s, DecidableInTimeAndSpace L t' s}

/-- The complexity class of languages decidable in space `O(s)` by a deterministic multi-tape
Turing machine, for some time bound. -/
def DSPACE (s : BoundFun) :=
  {L : Language Symbol | ∃ s' : BoundFun, s' ≤ s ∧ ∃ t, DecidableInTimeAndSpace L t s'}

/-- Membership in `DTIME`: a machine deciding `L` within some bound function `t'` that is `O(t)`. -/
lemma mem_DTIME {L : Language Symbol} {t t' : BoundFun} {s : ℕ → ℕ} (h : t' ≤ t)
    (hd : DecidableInTimeAndSpace L t' s) : L ∈ DTIME t := ⟨t', h, s, hd⟩

/-- Membership in `DSPACE`: a machine deciding `L` within some bound function `s'` that is
`O(s)`. -/
lemma mem_DSPACE {L : Language Symbol} {s s' : BoundFun} {t : ℕ → ℕ} (h : s' ≤ s)
    (hd : DecidableInTimeAndSpace L t s') : L ∈ DSPACE s := ⟨s', h, t, hd⟩

/-- Membership in `DTIME` from a plain time bound `T`, via its monotone envelope. This is the form
in which concrete machine bounds are used: no monotonicity of `T` is required. -/
lemma mem_DTIME_ofFun {L : Language Symbol} {t : BoundFun} {T S : ℕ → ℕ}
    (h : BoundFun.ofFun T ≤ t) (hd : DecidableInTimeAndSpace L T S) : L ∈ DTIME t :=
  mem_DTIME h (hd.mono_time fun n => BoundFun.le_ofFun T n)

/-- Membership in `DSPACE` from a plain space bound `S`, via its monotone envelope. -/
lemma mem_DSPACE_ofFun {L : Language Symbol} {s : BoundFun} {S T : ℕ → ℕ}
    (h : BoundFun.ofFun S ≤ s) (hd : DecidableInTimeAndSpace L T S) : L ∈ DSPACE s :=
  mem_DSPACE h (hd.mono_space fun n => BoundFun.le_ofFun S n)

/-- `DTIME` in terms of an explicit constant: `L ∈ DTIME t` iff `L` is decidable within time
`c * t n` for some constant `c`. -/
lemma mem_DTIME_iff {L : Language Symbol} {t : BoundFun} :
    L ∈ DTIME t ↔ ∃ c : ℕ, ∃ s, DecidableInTimeAndSpace L (fun n => c * t n) s := by
  constructor
  · rintro ⟨t', ⟨c, hc⟩, s, hd⟩
    exact ⟨c, s, hd.mono_time hc⟩
  · rintro ⟨c, s, hd⟩
    exact mem_DTIME_ofFun (BoundFun.ofFun_le (c := c) fun _ => le_rfl) hd

/-- `DSPACE` in terms of an explicit constant: `L ∈ DSPACE s` iff `L` is decidable within space
`c * s n` for some constant `c`. -/
lemma mem_DSPACE_iff {L : Language Symbol} {s : BoundFun} :
    L ∈ DSPACE s ↔ ∃ c : ℕ, ∃ t, DecidableInTimeAndSpace L t (fun n => c * s n) := by
  constructor
  · rintro ⟨s', ⟨c, hc⟩, t, hd⟩
    exact ⟨c, t, hd.mono_space hc⟩
  · rintro ⟨c, t, hd⟩
    exact mem_DSPACE_ofFun (BoundFun.ofFun_le (c := c) fun _ => le_rfl) hd

/-- `DTIME` only depends on the time bound up to `O`. -/
lemma DTIME_mono {t₁ t₂ : BoundFun} (h : t₁ ≤ t₂) :
    DTIME (Symbol := Symbol) t₁ ⊆ DTIME t₂ :=
  fun _ ⟨_, ht', _, hd⟩ => mem_DTIME (ht'.trans h) hd

/-- `DSPACE` only depends on the space bound up to `O`. -/
lemma DSPACE_mono {s₁ s₂ : BoundFun} (h : s₁ ≤ s₂) :
    DSPACE s₁ ⊆ (DSPACE s₂ : Set (Language Symbol)) :=
  fun _ ⟨_, hs', _, hd⟩ => mem_DSPACE (hs'.trans h) hd

/-- Lifting a family of dominations to an inclusion of unions of `DTIME` classes. This is the
form in which statements like `2^{O(s)} ⊆ 2^{n^{O(1)}}` are used. -/
lemma iUnion_DTIME_subset_of_le {ι κ : Sort*} {F : ι → BoundFun} {G : κ → BoundFun}
    (h : ∀ i, ∃ j, F i ≤ G j) :
    (⋃ i, DTIME (Symbol := Symbol) (F i)) ⊆ ⋃ j, DTIME (G j) := by
  refine Set.iUnion_subset fun i => ?_
  obtain ⟨j, hj⟩ := h i
  exact (DTIME_mono hj).trans (Set.subset_iUnion (fun j => DTIME (Symbol := Symbol) (G j)) j)

/-- Lifting a family of dominations to an inclusion of unions of `DSPACE` classes. -/
lemma iUnion_DSPACE_subset_of_le {ι κ : Sort*} {F : ι → BoundFun} {G : κ → BoundFun}
    (h : ∀ i, ∃ j, F i ≤ G j) :
    (⋃ i, DSPACE (Symbol := Symbol) (F i)) ⊆ ⋃ j, DSPACE (G j) := by
  refine Set.iUnion_subset fun i => ?_
  obtain ⟨j, hj⟩ := h i
  exact (DSPACE_mono hj).trans (Set.subset_iUnion (fun j => DSPACE (Symbol := Symbol) (G j)) j)

/-! ### Classes of bound functions

A bound such as `2 ^ O(s)` is a whole family of bound functions, not a single one. Such families
are the O-classes of `Cslib.BoundFun` (`BoundFun.ExpO`, `BoundFun.PolyO`, ...), and the complexity
class for such a family is the union of the `DTIME` / `DSPACE` classes of its members. -/

/-- The class of languages decidable in time `t` for some bound function `t` in the class `𝒪` of
bound functions. -/
def DTIMEOf (𝒪 : Set BoundFun) : Set (Language Symbol) := ⋃ t ∈ 𝒪, DTIME t

/-- The class of languages decidable in space `s` for some bound function `s` in the class `𝒪` of
bound functions. -/
def DSPACEOf (𝒪 : Set BoundFun) : Set (Language Symbol) := ⋃ s ∈ 𝒪, DSPACE s

/-- Membership in `DTIMEOf`, from membership in one of the `DTIME` classes it unions. -/
lemma mem_DTIMEOf {L : Language Symbol} {𝒪 : Set BoundFun} {t : BoundFun} (ht : t ∈ 𝒪)
    (h : L ∈ DTIME t) : L ∈ DTIMEOf 𝒪 := Set.mem_biUnion ht h

/-- Membership in `DSPACEOf`, from membership in one of the `DSPACE` classes it unions. -/
lemma mem_DSPACEOf {L : Language Symbol} {𝒪 : Set BoundFun} {s : BoundFun} (hs : s ∈ 𝒪)
    (h : L ∈ DSPACE s) : L ∈ DSPACEOf 𝒪 := Set.mem_biUnion hs h

/-- The workhorse for membership in `DTIMEOf`: a machine with plain running time `T` whose monotone
envelope is dominated by a member of `𝒪`. -/
lemma mem_DTIMEOf_ofFun {L : Language Symbol} {𝒪 : Set BoundFun} {t : BoundFun} {T S : ℕ → ℕ}
    (hT : BoundFun.ofFun T ≤ t) (ht : t ∈ 𝒪) (hd : DecidableInTimeAndSpace L T S) :
    L ∈ DTIMEOf 𝒪 := mem_DTIMEOf ht (mem_DTIME_ofFun hT hd)

/-- The workhorse for membership in `DSPACEOf`: a machine with plain space usage `S` whose monotone
envelope is dominated by a member of `𝒪`. -/
lemma mem_DSPACEOf_ofFun {L : Language Symbol} {𝒪 : Set BoundFun} {s : BoundFun} {T S : ℕ → ℕ}
    (hS : BoundFun.ofFun S ≤ s) (hs : s ∈ 𝒪) (hd : DecidableInTimeAndSpace L T S) :
    L ∈ DSPACEOf 𝒪 := mem_DSPACEOf hs (mem_DSPACE_ofFun hS hd)

/-- `DTIMEOf` is monotone in the class of bound functions. This is the form in which inclusions
between complexity classes are proved: they reduce to inclusions in the big-O calculus. -/
lemma DTIMEOf_mono {𝒪₁ 𝒪₂ : Set BoundFun} (h : 𝒪₁ ⊆ 𝒪₂) :
    DTIMEOf (Symbol := Symbol) 𝒪₁ ⊆ DTIMEOf 𝒪₂ :=
  Set.biUnion_subset_biUnion_left h

/-- `DSPACEOf` is monotone in the class of bound functions. -/
lemma DSPACEOf_mono {𝒪₁ 𝒪₂ : Set BoundFun} (h : 𝒪₁ ⊆ 𝒪₂) :
    DSPACEOf (Symbol := Symbol) 𝒪₁ ⊆ DSPACEOf 𝒪₂ :=
  Set.biUnion_subset_biUnion_left h

/-- The classes of the big-O calculus are of the form `{f | ∃ i, f ≤ F i}`, for which `DTIMEOf` is
the union of the `DTIME` classes of the generating family. -/
lemma DTIMEOf_setOf_exists_le {ι : Sort*} (F : ι → BoundFun) :
    DTIMEOf (Symbol := Symbol) {f | ∃ i, f ≤ F i} = ⋃ i, DTIME (F i) := by
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun t ht => ?_) (Set.iUnion_subset fun i => ?_)
  · obtain ⟨i, hi⟩ := ht
    exact (DTIME_mono hi).trans (Set.subset_iUnion (fun i => DTIME (Symbol := Symbol) (F i)) i)
  · exact Set.subset_biUnion_of_mem (u := fun t => DTIME (Symbol := Symbol) t) ⟨i, le_rfl⟩

/-- The `DSPACE` analogue of `DTIMEOf_setOf_exists_le`. -/
lemma DSPACEOf_setOf_exists_le {ι : Sort*} (F : ι → BoundFun) :
    DSPACEOf (Symbol := Symbol) {f | ∃ i, f ≤ F i} = ⋃ i, DSPACE (F i) := by
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun s hs => ?_) (Set.iUnion_subset fun i => ?_)
  · obtain ⟨i, hi⟩ := hs
    exact (DSPACE_mono hi).trans (Set.subset_iUnion (fun i => DSPACE (Symbol := Symbol) (F i)) i)
  · exact Set.subset_biUnion_of_mem (u := fun s => DSPACE (Symbol := Symbol) s) ⟨i, le_rfl⟩

/-- Time `O(t)` is `DTIME t`. -/
@[simp] lemma DTIMEOf_O (t : BoundFun) : DTIMEOf (Symbol := Symbol) (BoundFun.O t) = DTIME t :=
  Set.Subset.antisymm (Set.iUnion₂_subset fun _ ht => DTIME_mono ht)
    (Set.subset_biUnion_of_mem (u := fun t => DTIME (Symbol := Symbol) t) (BoundFun.mem_O.2 le_rfl))

/-- Space `O(s)` is `DSPACE s`. -/
@[simp] lemma DSPACEOf_O (s : BoundFun) : DSPACEOf (Symbol := Symbol) (BoundFun.O s) = DSPACE s :=
  Set.Subset.antisymm (Set.iUnion₂_subset fun _ hs => DSPACE_mono hs)
    (Set.subset_biUnion_of_mem (u := fun s => DSPACE (Symbol := Symbol) s)
      (BoundFun.mem_O.2 le_rfl))

/-- Time `2 ^ O(s)`, in terms of the union over the constant in the exponent. -/
lemma DTIMEOf_ExpO (s : BoundFun) :
    DTIMEOf (Symbol := Symbol) (BoundFun.ExpO s)
      = ⋃ c, DTIME (BoundFun.exp2 (BoundFun.const c * s)) :=
  DTIMEOf_setOf_exists_le _

/-- Space `2 ^ O(s)`, in terms of the union over the constant in the exponent. -/
lemma DSPACEOf_ExpO (s : BoundFun) :
    DSPACEOf (Symbol := Symbol) (BoundFun.ExpO s)
      = ⋃ c, DSPACE (BoundFun.exp2 (BoundFun.const c * s)) :=
  DSPACEOf_setOf_exists_le _

namespace Classes

open BoundFun

/-- Deterministic polynomial time. -/
def P : Set (Language Symbol) := DTIMEOf PolyO

/-- Deterministic exponential time (linear exponent). -/
def E : Set (Language Symbol) := DTIMEOf (ExpO linear)

/-- Deterministic exponential time (polynomial exponent). -/
def EXP : Set (Language Symbol) := DTIMEOf ExpPolyO

/-- Deterministic logarithmic space. -/
def L : Set (Language Symbol) := DSPACE log

/-- Deterministic polynomial space. -/
def PSPACE : Set (Language Symbol) := DSPACEOf PolyO

/-- Deterministic exponential space (linear exponent). -/
def ESPACE : Set (Language Symbol) := DSPACEOf (ExpO linear)

/-- Deterministic exponential space (polynomial exponent). -/
def EXPSPACE : Set (Language Symbol) := DSPACEOf ExpPolyO

/-- `P` is the union of the classes `DTIME (n ^ k)`. -/
lemma P_eq_iUnion : P (Symbol := Symbol) = ⋃ k, DTIME (linear ^ k) := DTIMEOf_setOf_exists_le _

/-- `E` is the union of the classes `DTIME (2 ^ (c * n))`. -/
lemma E_eq_iUnion : E (Symbol := Symbol) = ⋃ c, DTIME (exp2 (const c * linear)) :=
  DTIMEOf_setOf_exists_le _

/-- `EXP` is the union of the classes `DTIME (2 ^ (n ^ k))`. -/
lemma EXP_eq_iUnion : EXP (Symbol := Symbol) = ⋃ k, DTIME (exp2 (linear ^ k)) :=
  DTIMEOf_setOf_exists_le _

/-- `PSPACE` is the union of the classes `DSPACE (n ^ k)`. -/
lemma PSPACE_eq_iUnion : PSPACE (Symbol := Symbol) = ⋃ k, DSPACE (linear ^ k) :=
  DSPACEOf_setOf_exists_le _

/-- `ESPACE` is the union of the classes `DSPACE (2 ^ (c * n))`. -/
lemma ESPACE_eq_iUnion : ESPACE (Symbol := Symbol) = ⋃ c, DSPACE (exp2 (const c * linear)) :=
  DSPACEOf_setOf_exists_le _

/-- `EXPSPACE` is the union of the classes `DSPACE (2 ^ (n ^ k))`. -/
lemma EXPSPACE_eq_iUnion : EXPSPACE (Symbol := Symbol) = ⋃ k, DSPACE (exp2 (linear ^ k)) :=
  DSPACEOf_setOf_exists_le _

end Classes

end Turing.MultiTapeTM
