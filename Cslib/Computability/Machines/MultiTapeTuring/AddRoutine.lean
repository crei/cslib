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
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.WhileCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.IteCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.EqualRoutine

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

-- a
-- b
-- 0

def whileCond (cond : MultiTapeTM k.succ (WithSep α)) (tm : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k.succ (WithSep α) :=
  let k := ⟨k, by omega⟩
  cond <;>
  doWhile k ((pop k) <;> (tm.extend (by omega) <;> cond)) <;>
  (pop ⟨k, by omega⟩)

def not (i : Fin k.succ) := ite i (pop i <;> push i []) (pop i <;> push i [OneTwo.one])

@[simp, grind =]
theorem not_eval_list {i : Fin k.succ} {tapes : Fin k.succ → List (List OneTwo)}
  {h_tapes_i : tapes i ≠ []} :
  (not i).eval_list tapes = .some (Function.update tapes i (
    (if (tapes i).head h_tapes_i = [] then [OneTwo.one] else []) :: (tapes i).tail)) := by
  simp [not, ite_eval, h_tapes_i]
  grind

-- public def add₀ : MultiTapeTM 4 (WithSep OneTwo) :=
--   copy 1 2 <;> push 1 []
--   -- Here we have [a, 0 :: b, b]

-- lemma add₀_eval_list {a b : List OneTwo} {ls₁ ls₂ ls₃ ls₄ : List (List OneTwo)} :
--   add₀.eval_list
--     [a :: ls₁, b :: ls₂, ls₃, ls₄].get =
--     .some [a :: ls₁, [] :: b :: ls₂, b :: ls₃, ls₄].get := by
--   simp [add₀]
--   grind [add₀]

public def add₀ : MultiTapeTM 4 (WithSep OneTwo) :=
  (((copy 1 2 <;> push 1 []) <;>
  -- Here we have [a, 0 :: b, b]
  (whileCond ((eq 0 1 3) <;> not 3) (succ 1 <;> succ 2))) <;>
  -- Here we have [a, a :: b, a + b]
  (pop 1))

@[simp, grind =]
theorem add₀_eval_list {tapes : Fin 4 → List (List OneTwo)}
  {h_nonempty₀ : tapes 0 ≠ []} {h_nonempty₁ : tapes 1 ≠ []} :
  add₀.eval_list tapes = .some
    (Function.update tapes 2 ((dya (dya_inv ((tapes 0).head h_nonempty₀) + dya_inv ((tapes 1).head h_nonempty₁)) :: (tapes 2)))) := by
  sorry

-- --- Repeatedly run a sub routine as long as a condition on the symbol
-- --- at the first head is true.
-- public def ite (tm₁ tm₂ : MultiTapeTM k.succ (WithSep α)) :
--     MultiTapeTM k.succ (WithSep α) where
--   Λ := PUnit
--   q₀ := 0
--   M _ syms := sorry

-- @[simp]
-- public theorem ite_eval
--   (tm₁ tm₂ : MultiTapeTM k.succ (WithSep α))
--   (tapes : Fin k.succ → List (List α))
--   (h_nonempty : tapes 0 ≠ []) :
--   (ite tm₁ tm₂).eval_list tapes =
--     if (tapes 0).head h_nonempty = [] then tm₂.eval_list tapes else tm₁.eval_list tapes := by
--   sorry

end Routines

end Turing
