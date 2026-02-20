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
public lemma pop₁_eval_list {tapes : Fin 1 → List (List α)} :
  pop₁.eval_list tapes = .some (Function.update tapes 0 (tapes 0).tail) := by
  sorry

public def pop {k : ℕ} (i : Fin k.succ) : MultiTapeTM k.succ (WithSep α) :=
  pop₁.with_tapes [i].get (by intro x y; grind) (h_le := by omega)

@[simp, grind =]
public theorem pop_eval_list {k : ℕ} {i : Fin k.succ}
  {tapes : Fin k.succ → List (List α)} :
  (pop i).eval_list tapes = .some (Function.update tapes i (tapes i).tail) := by
  simp [pop]
  grind

end Routines

end Turing
