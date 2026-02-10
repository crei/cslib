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
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

public def copy₁ : MultiTapeTM 2 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public lemma copy₁_eval_list {w : List α} {ls₁ ls₂ : List (List α)} :
  copy₁.eval_list [w :: ls₁, ls₂].get = Part.some [w :: ls₁, w :: ls₂].get := by
  sorry

public def copy {k : ℕ} (i j : Fin k.succ) (h_neq : i ≠ j := by decide) :
  MultiTapeTM k.succ (WithSep α) :=
  copy₁.with_tapes #v[i, j] (h_le := by omega)

@[simp, grind =]
public lemma copy_eval_list
  {k : ℕ} {i j : Fin k.succ} {h_neq : i ≠ j}
  {tapes : Fin k.succ → List (List α)}
  (h_tapes_i : tapes i ≠ []) :
  (copy i j (h_neq := h_neq)).eval_list tapes = Part.some
    (Function.update tapes j (((tapes i).head h_tapes_i) :: (tapes j))) := by
  sorry

public lemma copy₁_evalWithStats {w : List α} {ls₁ ls₂ : List (List α)} :
  copy₁.evalWithStats_list #v[w :: ls₁, ls₂].get =
    .some (
      [w :: ls₁, w :: ls₂].get,
      [⟨-1, w.length, 0, by omega⟩, ⟨-w.length - 2, 0, -w.length - 1, by omega⟩].get) := by
  sorry


-- TODO at some point, we might not want exact stats but rather an upper bound.
-- Can this be made compatible with using equality?

end Routines

end Turing
