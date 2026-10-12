/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Complexity.PolyTime

namespace CslibTests.MultiTapePolyTime

open Turing.MultiTapeTM

-- `fun_prop` assembles polynomial-time computability from the closure properties.
example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.2, p.1 + 1 + 1))
    (encPair encNat encNat) (encPair encNat encNat) := by
  fun_prop

example {c : ℕ → Bool} (hc : ComputableTidilyInPolyTime c encNat encBool) :
    ComputableTidilyInPolyTime (fun n => if c n then n + 1 else n) encNat encNat := by
  fun_prop

end CslibTests.MultiTapePolyTime
