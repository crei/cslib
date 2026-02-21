/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

def copy₁ : MultiTapeTM 2 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
lemma copy₁_eval_list {tapes : Fin 2 → List (List α)} :
  copy₁.eval_list tapes =
    Part.some (Function.update tapes 1 (((tapes 0).headD []) :: tapes 1)) := by
  sorry

/--
A Turing machine that copies the first word on tape `i` to tape `j`.
If Tape `i` is empty, pushes the empty word to tape `j`.
-/
public def copy {k : ℕ}
  (i j : Fin (k + 2))
  (h_inj : [i, j].get.Injective := by intro x y; grind) :
  MultiTapeTM (k + 2) (WithSep α) :=
  copy₁.with_tapes [i, j].get (by intro x y; grind)

@[simp, grind =]
public lemma copy_eval_list
  {k : ℕ}
  (i j : Fin (k + 2))
  (h_inj : [i, j].get.Injective := by intro x y; grind)
  {tapes : Fin (k + 2) → List (List α)} :
  (copy i j h_inj).eval_list tapes = Part.some
    (Function.update tapes j (((tapes i).headD []) :: (tapes j))) := by
  simpa [copy] using apply_updates_function_update h_inj

end Routines

end Turing
