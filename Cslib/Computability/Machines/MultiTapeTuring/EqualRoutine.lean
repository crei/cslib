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

namespace Turing

namespace Routines

--- A 3-tape Turing machine that pushes the new word "1"
--- to the third tape if the first words on the first and second tape are the same
--- and otherwise pushes the empty word to the third tape.
public def eq₀ : MultiTapeTM 3 (WithSep OneTwo) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem eq₀_eval_list (w₁ w₂ : List OneTwo) (ws₁ ws₂ ws₃ : List (List OneTwo)) :
  eq₀.eval_list [w₁ :: ws₁, w₂ :: ws₂, ws₃].get =
    Part.some (if w₁ = w₂ then
      [w₁ :: ws₁, w₂ :: ws₂, [.one] :: ws₃].get
    else
      [w₁ :: ws₁, w₂ :: ws₂, [] :: ws₃].get) := by
  sorry

public def eq {k : ℕ} (q s t : Fin k.succ)
  (h_neq : q ≠ s := by decide) (h_neq' : q ≠ t := by decide) (h_neq'' : s ≠ t := by decide) :
  MultiTapeTM k.succ (WithSep OneTwo) :=
  eq₀.with_tapes #v[q, s, t] (h_le := by omega)

@[simp, grind =]
public theorem eq_eval_list {k : ℕ} {q s t : Fin k.succ}
  {h_neq : q ≠ s} {h_neq' : q ≠ t} {h_neq'' : s ≠ t}
  {tapes : Fin k.succ → List (List OneTwo)} {h_q_nonempty : tapes q ≠ []} {h_s_nonempty : tapes s ≠ []} :
  (eq q s t (h_neq := h_neq) (h_neq' := h_neq') (h_neq'' := h_neq'')).eval_list tapes =
    Part.some (Function.update tapes t
      ((if (tapes q).head h_q_nonempty = (tapes s).head h_s_nonempty then
        [.one]
      else
        []) :: (tapes t))) := by
  sorry

end Routines

end Turing
