/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V3.Data
public import Mathlib.Control.Fix
public import Mathlib.Control.LawfulFix

@[expose] public section

namespace Turing

namespace RoseTreeMachine

def Var := ℕ
deriving Repr

inductive Prog where
  | var (id : Var)
  | empty
  | cons (h t : Prog)
  /-- `elim v em cs`: if `v` evaluates to `empty`, run `em`; otherwise destructure into
      `head` and `tail` (both appended to `env`, in that order) and run `cs`. -/
  | elim (v em cs : Prog)
  | ifEq (x y then_ else_ : Prog)
  /-- `fold body init list`: `init` and `list` produce starting accumulator and the input
      list; `body` runs once per element with `env` extended by `[acc, x]`. -/
  | fold (body init list : Prog)
  /-- `while_ init body`: `init` produces the starting accumulator; `body` runs with
      `env` extended by the current accumulator. -/
  | while_ (init body : Prog)
deriving Repr


-- TODO this version uses super reduced time and space bounds. Whenever we can remove a
-- factor, we do. Check if this is ok.

abbrev set (σ : ℕ → Data) (i : ℕ) (v : Data) := Function.update σ i v

/-- Semantics of Prog including time and space resource bounds.
`ProgSem σ i p x t s` means that on environment `σ` with variable height
`i`, the program `p` evaluates to `x` and uses `t` time and `s` space. -/
inductive ProgSem : (ℕ → Data) → ℕ → Prog → Data → ℕ → ℕ → Prop
  | var : ProgSem σ i (.var x) (σ x) (σ x).size (σ x).size
  | empty : ProgSem σ i .empty (Data.l []) 1 1
  | cons (h₁ : ProgSem σ i head hd hd_t hd_s) (h₂ : ProgSem σ i tail tl tl_t tl_s) :
      ProgSem σ i (.cons head tail) (Data.l (hd :: tl.asList)) (hd_t + tl_t) (max hd_s tl_s)
  | elim_nil
      (h₁ : ProgSem σ i val (Data.l []) t_v s_v)
      (h₂ : ProgSem σ i empty r t_em s_em) :
      ProgSem σ i (.elim val empty _) r (t_v + em_v) (max s_v s_em)
  | elim_cons
      (h₁ : ProgSem σ i val (Data.l (hd :: tl)) t_v s_v)
      (h₂ : ProgSem (set (set σ i hd) (i + 1) (Data.l tl)) (i + 2) cons r t_em s_em) :
      -- TODO include the size of hd for time and space?
      ProgSem σ i (.elim val _ cons) r (t_v + em_v) (max s_v s_em)
  | ifEq_eq
      (h_a : ProgSem σ i p_a a t_a s_a)
      (h_b : ProgSem σ i p_b a t_b s_b)
      (h_then : ProgSem σ i then_ r t_t s_t) :
      ProgSem σ i (.ifEq p_a p_b then_ _) r (t_a + t_b + t_t) (max (max s_a s_b) s_t)
  | ifEq_veq
      (h_a : ProgSem σ i p_a a t_a s_a)
      (h_b : ProgSem σ i p_b b t_b s_b)
      (h_neq : a ≠ b)
      (h_else : ProgSem σ i else_ r t_e s_e) :
      ProgSem σ i (.ifEq p_a p_b _ else_) r (t_a + t_b + t_e) (max (max s_a s_b) s_e)
  | fold_empty
      (h_a : ProgSem σ i p_a a t_a s_a)
      (h_b : ProgSem σ i p_b b t_b s_b)
      (h_neq : a ≠ b)
      (h_else : ProgSem σ i else_ r t_e s_e) :
      ProgSem σ i (.fold body init list) r (t_a + t_b + t_e) (max (max s_a s_b) s_e)


end RoseTreeMachine

end Turing
