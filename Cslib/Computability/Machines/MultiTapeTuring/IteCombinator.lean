/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

/--
A Turing machine combinator that runs `tm₁` if the first word on tape `i` exists and is non-empty,
otherwise it runs `tm₂`. -/
public def ite (i : Fin k) (tm₁ tm₂ : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem ite_halts
  {i : Fin k}
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  (h_tm₁_halts : ∀ tapes, tm₁.haltsOn tapes)
  (h_tm₂_halts : ∀ tapes, tm₂.haltsOn tapes) :
  ∀ tapes, (ite i tm₁ tm₂).haltsOn tapes := by
  sorry

@[simp, grind =]
public theorem ite_eval_list
  {i : Fin k}
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  {tapes : Fin k → List (List α)} :
  (ite i tm₁ tm₂).eval_list tapes =
    if (tapes i).headD [] = [] then tm₂.eval_list tapes else tm₁.eval_list tapes := by
  sorry

@[simp]
public theorem ite_spaceUsed_list
  {i : Fin k}
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  {tapes : Fin k → List (List α)} :
  (ite i tm₁ tm₂).spaceUsed_list tapes sorry =
    if (tapes i).headD [] = [] then
      tm₂.spaceUsed_list tapes sorry
    else
      tm₁.spaceUsed_list tapes sorry := by
  sorry

end Routines

end Turing
