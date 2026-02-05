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

--- Run tm₂ after tm₁ has terminated.
public def seq (tm₁ tm₂ : MultiTapeTM k α) : MultiTapeTM k α := sorry


public theorem seq_eval
  (tm₁ tm₂ : MultiTapeTM k α)
  (tapes₀ : Fin k → BiTape α) :
  (seq tm₁ tm₂).eval tapes₀ =
    tm₁.eval tapes₀ >>= fun tape₁ => tm₂.eval tape₁ := by
  sorry

public theorem seq_eval_list
  (tm₁ tm₂ : MultiTapeTM k (WithSep α))
  (tapes₀ : Fin k → List (List α)) :
  (seq tm₁ tm₂).eval_list tapes₀ =
    tm₁.eval_list tapes₀ >>= fun tape₁ => tm₂.eval_list tape₁ := by
  sorry



end Routines

end Turing
