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

namespace Turing

namespace MultiTapeTM

variable [Inhabited α]
variable {k : ℕ}

/--
Sequential combination of Turing machines. Runs `tm₁` and then `tm₂` on the resulting tapes
(if the first one halts).
-/
public def seq (tm₁ tm₂ : MultiTapeTM k α) : MultiTapeTM k α := sorry

public theorem seq_eval
  (tm₁ tm₂ : MultiTapeTM k α)
  (tapes₀ : Fin k → BiTape α) :
  (seq tm₁ tm₂).eval tapes₀ =
    tm₁.eval tapes₀ >>= fun tape₁ => tm₂.eval tape₁ := by
  sorry

@[simp, grind =]
public theorem seq_eval_list
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  {tapes₀ : Fin k → List (List α)} :
  (seq tm₁ tm₂).eval_list tapes₀ =
    tm₁.eval_list tapes₀ >>= fun tape₁ => tm₂.eval_list tape₁ := by
  sorry

public theorem seq_associative
  (tm₁ tm₂ tm₃ : MultiTapeTM k α)
  (tapes₀ : Fin k → List (List α)) :
  (seq (seq tm₁ tm₂) tm₃).eval = (seq tm₁ (seq tm₂ tm₃)).eval := by
  sorry

@[simp]
public theorem seq_halts_of_halts
  {tm₁ tm₂ : MultiTapeTM k α}
  (h_halts₁ : ∀ tapes, tm₁.haltsOn tapes)
  (h_halts₂ : ∀ tapes, tm₂.haltsOn tapes) :
  ∀ tapes, (seq tm₁ tm₂).haltsOn tapes := by
  sorry

@[simp]
public theorem seq_spaceUsed_list
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  (h_halts₁ : ∀ tapes, tm₁.haltsOn tapes)
  (h_halts₂ : ∀ tapes, tm₂.haltsOn tapes)
  {tapes₀ : Fin k → List (List α)} :
  (seq tm₁ tm₂).spaceUsed_list tapes₀ sorry = fun i =>
    let tapes₁ := (tm₁.eval_list tapes₀).get sorry
    max (tm₁.spaceUsed_list tapes₀ h_halts₁ i) (tm₂.spaceUsed_list tapes₁ h_halts₂ i)
  := by sorry

/--
Sequential combination of Turing machines.
-/
infixl:90 " <;> " => seq


end MultiTapeTM

end Turing
