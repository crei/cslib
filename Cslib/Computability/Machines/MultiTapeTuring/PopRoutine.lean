/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.TMWithAuxTapes

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

public def pop₁ : MultiTapeTM 1 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public lemma pop₁_eval_list {w : List α} {ls : List (List α)} :
  pop₁.eval_list [w :: ls].get = .some [ls].get := by
  sorry

public def pop {k : ℕ} (i : Fin k.succ) : MultiTapeTM k.succ (WithSep α) :=
  pop₁.with_tapes #v[i] (h_le := by omega)

@[simp, grind =]
public theorem pop_eval_list {k : ℕ} {i : Fin k.succ}
  {tapes : Fin k.succ → List (List α)}
  {h_not_empty : tapes i ≠ []} :
  (pop i).eval_list tapes = .some (Function.update tapes i (tapes i).tail) := by
  sorry

public def pop' {k aux : ℕ} (i : ℕ) (h_i_lt : i < k := by decide) :
    MultiTapeTMWithAuxTapes k aux (WithSep α) :=
  (pop₁.allocate_aux_tapes aux).with_tapes #v[⟨i, h_i_lt⟩]
    (h_le_k := by omega)
    (h_le_aux := by rfl)

@[simp, grind =]
public theorem pop'_eval_list {k aux i : ℕ} {h_i_lt : i < k}
  {tapes : Fin k → List (List α)}
  {h_not_empty : tapes ⟨i, h_i_lt⟩ ≠ []} :
  (pop' (aux := aux) i h_i_lt).eval_list tapes = .some
    (Function.update tapes ⟨i, h_i_lt⟩ (tapes ⟨i, h_i_lt⟩).tail) := by
  sorry

end Routines

end Turing
