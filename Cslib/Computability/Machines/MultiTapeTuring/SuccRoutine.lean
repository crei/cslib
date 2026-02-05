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
import Mathlib.Data.Nat.Bits

namespace Turing

namespace Routines

public def succ : MultiTapeTM 1 (WithSep OneTwo) where
  Λ := PUnit
  q₀ := 0
  M _ syms := sorry

public def dya (n : ℕ) : List OneTwo :=
  if n = 0 then []
  else if Even n then
    dya (n / 2 - 1) ++ [.two]
  else
    dya ((n - 1) / 2) ++ [.one]


@[simp]
public lemma succ_eval_list {n : ℕ} {ls : List (List OneTwo)} :
  succ.eval_list [(dya n) :: ls].get = .some [(dya n.succ) :: ls].get := by
  sorry

public lemma push_evalWithStats_list {n : ℕ} {ls : List (List OneTwo)} :
  succ.evalWithStats_list [(dya n) :: ls].get =
    .some (
      [(dya n.succ) :: ls].get,
      -- this depends on if we have overflow on the highest dyadic character or not.
      if (dya n.succ).length = (dya n).length then
        [⟨0, (dya n).length, 0, by omega⟩].get
      else
        [⟨-1, (dya n).length, -1, by omega⟩].get) := by
  sorry

-- TODO for space complexity, the max head position here is actually not important,
-- because we know that the tape has already been used.

-- TODO actually the better notion is actually to prove for all "list routines"
-- that the space used is
-- the currently used tape plus the new word (including separator) plus one (because we sometimes
-- overshoot by one cell to the left).
-- but then this has to hold for all inputs (that are list encodings)
-- AND this is wrong for anything that uses auxiliary tapes for temporary values.
-- So we have that plus an additional overhead for auxiliary tapes.

-- TODO so maybe start with writing down the algorithm for Savitch and then see how we can analyze
-- space usage.


end Routines

end Turing
