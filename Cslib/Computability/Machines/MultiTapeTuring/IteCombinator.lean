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
public def ite (tm₁ tm₂ : MultiTapeTM k.succ (WithSep α)) :
    MultiTapeTM k.succ (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem ite_eval
  (tm₁ tm₂ : MultiTapeTM k.succ (WithSep α))
  (tapes : Fin k.succ → List (List α))
  (h_nonempty : tapes 0 ≠ []) :
  (ite tm₁ tm₂).eval_list tapes =
    if (tapes 0).head h_nonempty = [] then tm₂.eval_list tapes else tm₁.eval_list tapes := by
  sorry

end Routines

end Turing
