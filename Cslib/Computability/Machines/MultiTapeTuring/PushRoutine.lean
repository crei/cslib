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

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

public def push₁ (w : List α) : MultiTapeTM 1 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public lemma push₁_eval_list {w : List α} {tapes : Fin 1 → List (List α)} :
  (push₁ w).eval_list tapes = .some (Function.update tapes 0 (w :: (tapes 0))) := by
  sorry

public def push {k : ℕ} (i : Fin k.succ) (w : List α) : MultiTapeTM k.succ (WithSep α) :=
  (push₁ w).with_tapes [i].get (by intro x y; grind) (h_le := by omega)

@[simp, grind =]
public theorem push_eval_list {k : ℕ}
  {i : Fin k.succ} {w : List α} {tapes : Fin k.succ → List (List α)} :
  (push i w).eval_list tapes =
    .some (Function.update tapes i (w :: (tapes i))) := by
  simp [push]
  grind

-- public lemma push₁_evalWithStats_list {w : List α} {ls : List (List α)} :
--   (push₁ w).evalWithStats_list #v[ls].get =
--     .some (
--       [w :: ls].get,
--       [⟨-w.length - 1, 0, -w.length - 1, by omega⟩].get) := by
--   sorry

end Routines

end Turing
