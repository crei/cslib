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

mutual
/-- Semantics of Prog including time and space resource bounds.
`ProgSem σ i p x t s` means that on environment `σ` with variable height
`i`, the program `p` evaluates to `x` and uses `t` time and `s` space. -/
inductive ProgSem : (List Data) → Prog → Data → ℕ → ℕ → Prop
  | var (h : σ[(i : ℕ)]? = some v) : ProgSem σ (.var i) v v.size v.size
  | empty : ProgSem σ .empty (Data.l []) 2 2
  | cons (h₁ : ProgSem σ head hd hd_t hd_s) (h₂ : ProgSem σ tail tl tl_t tl_s) :
      ProgSem σ (.cons head tail) (Data.l (hd :: tl.asList)) (hd_t + tl_t) (hd_s + tl_s)
  | elim_nil
      (h₁ : ProgSem σ val (Data.l []) t_v s_v)
      (h₂ : ProgSem σ empty r t_em s_em) :
      ProgSem σ (.elim val empty _) r (t_v + em_v) (max s_v s_em)
  | elim_cons
      (h₁ : ProgSem σ val (Data.l (hd :: tl)) t_v s_v)
      (h₂ : ProgSem (σ ++ [hd, Data.l tl]) cons r t_em s_em) :
      -- TODO include the size of hd for time and space?
      ProgSem σ (.elim val _ cons) r (t_v + em_v) (max s_v s_em)
  | ifEq_eq
      (h_a : ProgSem σ p_a a t_a s_a)
      (h_b : ProgSem σ p_b a t_b s_b)
      (h_then : ProgSem σ then_ r t_t s_t) :
      ProgSem σ (.ifEq p_a p_b then_ _) r (t_a + t_b + t_t) (max (max s_a s_b) s_t)
  | ifEq_veq
      (h_a : ProgSem σ p_a a t_a s_a)
      (h_b : ProgSem σ p_b b t_b s_b)
      (h_neq : a ≠ b)
      (h_else : ProgSem σ else_ r t_e s_e) :
      ProgSem σ (.ifEq p_a p_b _ else_) r (t_a + t_b + t_e) (max (max s_a s_b) s_e)
  /-- `fold body init list`: evaluate `init` to the starting accumulator and `list` to the
      input list, then thread the accumulator through `body` over the elements via `FoldSem`. -/
  | fold
      (h_init : ProgSem σ init acc t_init s_init)
      (h_list : ProgSem σ list (Data.l xs) t_list s_list)
      (h_fold : FoldSem σ acc xs body r t_f s_f) :
      ProgSem σ (.fold body init list) r (t_init + t_list + t_f)
        (max (max s_init s_list) s_f)
  /-- `while_ init body`: evaluate `init` to the starting accumulator, then iterate `body`
      via `WhileSem` until it signals halting. -/
  | while_
      (h_init : ProgSem σ init acc t_init s_init)
      (h_while : WhileSem σ acc body r t_w s_w) :
      ProgSem σ (.while_ init body) r (t_init + t_w) (max s_init s_w)

/-- Folds `body` over the remaining elements `xs`, threading the accumulator.
`FoldSem σ acc xs body r t s` means that starting from accumulator `acc` and processing the
elements `xs` (each step running `body` with `env` extended by `[acc, x]`) yields result `r`
using `t` time and `s` space. -/
inductive FoldSem : (List Data) → Data → List Data → Prog → Data → ℕ → ℕ → Prop
  | nil : FoldSem σ acc [] body acc 0 0
  | cons
      (h_body : ProgSem (σ ++ [acc, x]) body acc' t_b s_b)
      (h_rest : FoldSem σ acc' xs body r t_r s_r) :
      FoldSem σ acc (x :: xs) body r (t_b + t_r) (max s_b s_r)

/-- Iterates `body` of a `while_` loop, threading the accumulator.
`WhileSem σ body acc r t s` means that, starting from accumulator `acc`, repeatedly running
`body` with `env` extended by `[acc]` eventually yields result `r` using `t` time and `s` space.
Before each iteration the halting condition is checked on the current accumulator: iteration
terminates (with the accumulator as result) when `acc` is empty or its head is empty. Otherwise
`body` is evaluated and its result becomes the new accumulator. Non-terminating loops simply have
no derivation. -/
inductive WhileSem : (List Data) → Data → Prog → Data → ℕ → ℕ → Prop
  | halt
      (h_stop : acc.asList.head?.getD (Data.l []) = Data.l []) :
      WhileSem σ acc body acc acc.size acc.size
  | step
      (h_cont : acc.asList.head?.getD (Data.l []) ≠ Data.l [])
      (h_body : ProgSem (σ ++ [acc]) body v t_b s_b)
      (h_rest : WhileSem σ v body r t_r s_r) :
      WhileSem σ acc body r (t_b + t_r) (max s_b s_r)
end

/-- The program `p` computes the value `y` from the value `x` in time `t` and space `s`. -/
def ComputesInTimeAndSpace (p : Prog) (x y : Data) (t : ℕ) (s : ℕ) : Prop :=
  ProgSem [x] p y t s



end RoseTreeMachine

end Turing
