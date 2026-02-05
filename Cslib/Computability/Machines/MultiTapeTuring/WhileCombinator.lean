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
public def doWhileSymbol (cond : Option α → Bool) (tm : MultiTapeTM k.succ α) :
    MultiTapeTM k.succ α where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem doWhileSymbol_eval
  (tm : MultiTapeTM k.succ α)
  (cond : Option α → Bool)
  (tapes_seq : ℕ → Fin k.succ → BiTape α)
  (h_transform : ∀ i, tm.eval (tapes_seq i) = .some (tapes_seq i.succ))
  (h_stops : ∃ m, ¬cond (tapes_seq m 0).head) :
  (doWhileSymbol cond tm).eval (tapes_seq 0) = .some (tapes_seq (Nat.find h_stops)) := by
  sorry

--- Repeatedly run a sub routine as long as the first word on the first tape is non-empty.
public def doWhile (tm : MultiTapeTM k.succ (WithSep α)) :
    MultiTapeTM k.succ (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public theorem doWhile_eval
  (tm : MultiTapeTM k.succ (WithSep α))
  (tapes_seq : ℕ → Fin k.succ → List (List α))
  (h_transform : ∀ i, tm.eval_list (tapes_seq i) = .some (tapes_seq i.succ))
  (h_nonempty : ∀ i, tapes_seq i 0 ≠ [])
  (h_stops : ∃ m, (tapes_seq m 0).head (h_nonempty m) = []) :
  (doWhile tm).eval_list (tapes_seq 0) = .some (tapes_seq (Nat.find h_stops)) := by
  sorry

end Routines

end Turing
