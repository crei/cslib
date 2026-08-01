/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Cslib.Computability.Machines.Turing.MultiTape.Classes

import Mathlib.Tactic.Ring

/-!
# From space bounds to time bounds

A deterministic machine that decides a language in space `s` cannot repeat a configuration before
halting, so the number of steps is bounded by the number of reachable configurations. Combined with
the configuration count of `ConfigBound`, this yields the inclusion
`DSPACE(s) ⊆ DTIME(2^{O(s)})`.

Two forms are provided:

* `space_subset_time_general` makes no assumption on `s` and keeps the input-length factor
  `BoundFun.linear`, which counts the read-only input-head positions. This factor is essential in
  general: for `s = O(1)` the class is the regular languages, decided in `Θ(n)` time, so the
  constant base `2 ^ (c * s n)` cannot absorb it.
* `space_subset_time` is the textbook statement `DSPACE(s) ⊆ DTIME(2^{O(s)})`, valid under the
  assumption `s(n) ≥ log n`, here `BoundFun.log ≤ s`, under which the input-length factor is
  absorbed into the exponential.

Both are stated with `DTIMEOf` over an O-class of bound functions (`BoundFun.ExpO s` is `2^{O(s)}`,
`{BoundFun.linear} * BoundFun.ExpO s` is `n · 2^{O(s)}`), so that the constant hidden in the
exponent of `2^{O(s)}` does not appear in the statements, nor in the proofs: the machine-dependent
constants are introduced once by `storageBound_mem_ExpO` and absorbed by the closure properties of
the O-classes.

Two inclusions for specific complexity classes are derived from this:

* `logspace_subset_p` shows `L ⊆ P`
* `pspace_subset_exp` shows `PSPACE ⊆ EXP`

-/

@[expose] public section

open Cslib Cslib.BoundFun

open scoped Pointwise

namespace Turing.MultiTapeTM

open scoped Classical in
/-- A Turing machine that computes `output` in `t` steps using space at most `σ` already computes
it within `(input.length + 2) * storageBound Symbol State k σ` steps, using no more space. -/
lemma ComputesInTimeAndSpace.truncate
    {Symbol State : Type} [Fintype Symbol] [Fintype State]
    {k : ℕ}
    {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol}
    {t s σ : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s)
    (hσ : s ≤ σ) :
    ∃ t' ≤ (input.length + 2) * storageBound Symbol State k σ,
    ∃ s' ≤ s, tm.ComputesInTimeAndSpace input output t' s' := by
  obtain ⟨hhalt, hout, hspace⟩ := h
  obtain ⟨τ, hτcard, hτle, hτhalt⟩ := exists_halt_le_card_image tm input hhalt
  rw [tm.outputString_eq_of_halt (tm.initCfg input) hτle hτhalt] at hout
  exact ⟨τ, hτcard.trans (card_configs_le t σ (hspace.trans_le hσ)),
    tm.spaceUsed (tm.initCfg input) τ, (spaceUsed_mono tm _ hτle).trans hspace.le,
    hτhalt, hout, rfl⟩

/-- General form of the space-to-time inclusion, making no assumption on `s`. The time bound lies
in the class `{linear} * ExpO s`, i.e. it is `n · 2^{O(s)}`: the linear factor accounts for the
read-only input-head positions and cannot be dropped in general, since for `s = O(1)` the class is
the regular languages, which need `Θ(n)` time. -/
theorem space_subset_time_general
    {Symbol : Type} [Inhabited Symbol]
    (s : BoundFun) :
    DSPACE s ⊆ DTIMEOf (Symbol := Symbol) ({linear} * ExpO s) := by
  rintro L ⟨s', hs', tBound, kk, sym, state, emb, tm, hcomp⟩
  set g := BoundFun.ofFun (fun n => storageBound (Fin sym) (Fin state) kk (s' n))
  refine mem_DTIMEOf_ofFun (S := ⇑s') (t := linear * g)
    (T := fun n => (n + 2) * storageBound (Fin sym) (Fin state) kk (s' n)) ?_ ?_
    ⟨kk, sym, state, emb, tm, fun input => ?_⟩
  · -- The running time is at most `(n + 2)` times the number of storage configurations.
    calc BoundFun.ofFun (fun n => (n + 2) * storageBound (Fin sym) (Fin state) kk (s' n))
        ≤ BoundFun.ofFun (fun n => n + 2) * g := BoundFun.ofFun_mul_le ..
      _ ≤ linear * g := by gcongr; exact BoundFun.ofFun_add_const_le_linear 2
  · -- That bound is `n · 2^{O(s)}`, since the machine runs in space `s' ≤ s`.
    exact Set.mul_mem_mul rfl (ExpO_subset_ExpO hs' (storageBound_mem_ExpO ..))
  · -- Truncate the computation to the configuration-count bound.
    obtain ⟨t, -, σ, hσ, hcomp'⟩ := hcomp input
    obtain ⟨t', ht', σ', hσ', hcs⟩ := hcomp'.truncate (σ := s' input.length) hσ
    exact ⟨t', by simpa using ht', σ', hσ'.trans hσ, hcs⟩

/-- The textbook space-to-time inclusion `DSPACE(s) ⊆ DTIME(2^{O(s)})`, under the standard
assumption `s(n) ≥ log n`, here expressed as `BoundFun.log ≤ s`. It follows from
`space_subset_time_general` by absorbing the input-length factor into the exponential. -/
theorem space_subset_time
    {Symbol : Type} [Inhabited Symbol] (s : BoundFun) (hs : log ≤ s) :
    DSPACE s ⊆ DTIMEOf (Symbol := Symbol) (ExpO s) :=
  (space_subset_time_general s).trans (DTIMEOf_mono (singleton_linear_mul_ExpO_subset hs))

open Classes

/-- The inclusion `L ⊆ P`: every log-space decidable language is decidable in polynomial time,
since `2^{O(log n)}` is polynomial. -/
theorem logspace_subset_p {Symbol : Type} [Inhabited Symbol] :
    L (Symbol := Symbol) ⊆ P :=
  (space_subset_time log le_rfl).trans (DTIMEOf_mono ExpO_log_subset_PolyO)

/-- The inclusion `PSPACE ⊆ EXP`: for a polynomially bounded space bound `s`, the time bound
`n · 2^{O(s)}` of `space_subset_time_general` is `2^{poly(n)}`. -/
theorem pspace_subset_exp {Symbol : Type} [Inhabited Symbol] :
    PSPACE (Symbol := Symbol) ⊆ EXP :=
  Set.iUnion₂_subset fun s hs => (space_subset_time_general s).trans
    (DTIMEOf_mono (singleton_linear_mul_ExpO_subset_ExpPolyO hs))

end Turing.MultiTapeTM
