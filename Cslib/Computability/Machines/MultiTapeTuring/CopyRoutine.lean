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
public import Cslib.Computability.Machines.MultiTapeTuring.TMWithAuxTapes

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
public lemma copy₁_eval_list {tapes : Fin 2 → List (List α)} :
  copy₁.eval_list tapes =
    Part.some (Function.update tapes 1 (((tapes 0).headD []) :: tapes 1)) := by
  sorry

public def copy {k : ℕ} (i j : ℕ)
  (h_neq : i ≠ j := by decide)
  (h_i_lt : i < k := by decide)
  (h_j_lt : j < k := by decide) :
  MultiTapeTM k (WithSep α) :=
  copy₁.with_tapes #v[⟨i, h_i_lt⟩, ⟨j, h_j_lt⟩] (h_le := by omega)

@[simp, grind =]
public lemma copy_eval_list
  {k : ℕ} {i j : ℕ} {h_neq : i ≠ j} {h_i_lt : i < k} {h_j_lt : j < k}
  {tapes : Fin k → List (List α)}
  (h_tapes_i : tapes ⟨i, h_i_lt⟩ ≠ []) :
  (copy i j (h_neq := h_neq) (h_i_lt) (h_j_lt)).eval_list tapes = Part.some
    (Function.update tapes ⟨j, h_j_lt⟩
      (((tapes ⟨i, h_i_lt⟩).head h_tapes_i) :: (tapes ⟨j, h_j_lt⟩))) := by
  sorry

public def copy' {k aux : ℕ} (i j : ℕ)
  (h_neq : i ≠ j := by decide)
  (h_i_lt : i < k := by decide)
  (h_j_lt : j < k := by decide) :
  MultiTapeTMWithAuxTapes k aux (WithSep α) :=
  (copy₁.allocate_aux_tapes aux).with_tapes #v[⟨i, h_i_lt⟩, ⟨j, h_j_lt⟩]
    (h_le_k := by omega)
    (h_le_aux := by rfl)

@[simp, grind =]
public lemma copy'_eval_list
  {k aux : ℕ} {i j : ℕ} {h_neq : i ≠ j} {h_i_lt : i < k} {h_j_lt : j < k}
  {tapes : Fin k → List (List α)}
  (h_tapes_i : tapes ⟨i, h_i_lt⟩ ≠ []) :
  (copy' (aux := aux) i j (h_neq := h_neq) (h_i_lt) (h_j_lt)).eval_list_aux tapes = Part.some
    (Function.update tapes ⟨j, h_j_lt⟩
      (((tapes ⟨i, h_i_lt⟩).head h_tapes_i) :: (tapes ⟨j, h_j_lt⟩))) := by
  sorry

public noncomputable def copy'' {k : ℕ} (i j : ℕ)
  (h_neq : i ≠ j := by decide)
  (h_i_lt : i < k := by decide)
  (h_j_lt : j < k := by decide) :
  MultiTapeTM k (WithSep α) :=
  copy₁.with_tapes' [⟨i, h_i_lt⟩, ⟨j, h_j_lt⟩].get (by intro x y; grind) (h_le := by omega)

@[simp, grind =]
public lemma copy''_eval_list
  {k : ℕ} {i j : ℕ} {h_neq : i ≠ j} {h_i_lt : i < k} {h_j_lt : j < k}
  {tapes : Fin k → List (List α)} :
  (copy'' i j (h_neq := h_neq) (h_i_lt) (h_j_lt)).eval_list tapes = Part.some
    (Function.update tapes ⟨j, h_j_lt⟩
      (((tapes ⟨i, h_i_lt⟩).headD []) :: (tapes ⟨j, h_j_lt⟩))) := by
  simp [copy'']
  grind

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
