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

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

--- Repeatedly run a sub routine as long as a condition on the symbol
--- at the first head is true.
public def ite (i : Fin k) (tm₁ tm₂ : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp, grind =]
public theorem ite_eval
  {i : Fin k}
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  {tapes : Fin k → List (List α)}
  {h_nonempty : tapes i ≠ []} :
  (ite i tm₁ tm₂).eval_list tapes =
    if (tapes i).head h_nonempty = [] then tm₂.eval_list tapes else tm₁.eval_list tapes := by
  sorry

end Routines

end Turing
