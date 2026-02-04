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

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]

public def push (w : List α) : MultiTapeTM 1 (WithSep α) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

@[simp]
public lemma push_eval_list {w : List α} {ls : List (List α)} :
  (push w).eval_list [ls].get = .some [w :: ls].get := by
  sorry

public lemma push_evalWithStats_list {w : List α} {ls : List (List α)} :
  (push w).evalWithStats_list #v[ls].get =
    .some (
      [w :: ls].get,
      [⟨-w.length - 1, 0, -w.length - 1, by omega⟩].get) := by
  sorry

end Routines

end Turing
