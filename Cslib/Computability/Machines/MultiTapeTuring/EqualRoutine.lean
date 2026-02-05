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

--- A 3-tape Turing machine that pushes the new word "1"
--- to the third tape if the first words on the first and second tape are the same
--- and otherwise pushes the empty word to the third tape.
public def eq : MultiTapeTM 3 (WithSep OneTwo) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem eq_eval_list (w₁ w₂ : List OneTwo) (ws₁ ws₂ ws₃ : List (List OneTwo)) :
  eq.eval_list [w₁ :: ws₁, w₂ :: ws₂, ws₃].get =
    Part.some (if w₁ = w₂ then
      [w₁ :: ws₁, w₂ :: ws₂, [.one] :: ws₃].get
    else
      [w₁ :: ws₁, w₂ :: ws₂, [] :: ws₃].get) := by
  sorry

end Routines

end Turing
