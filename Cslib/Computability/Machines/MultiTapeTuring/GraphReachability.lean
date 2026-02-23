/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.IteCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.EqualRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.DuplicateRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.DecRoutine


namespace Turing

namespace Routines

-- This is an attempt at proving Savitch's theorem. We start by stating a generic
-- space-efficient graph reachability algorithm.

/-

General idea, assume distance is power of two:

def reachable(a, b, t, r):
  if t = 0:
    return r(a, b)
  else:
    for c in vertices:
      if reachable(a, c, t - 1, r) and reachable(c, b, t - 1, r):
        return True
    return False

Until we have a generic mechanism for recursion, let's translate this into a program that
uses "goto", and every variable is a stack:

def reachable(a, b, t, edge):
  result = 0
  initial_t = t
  pc = [:fun_start]
  while !pc.is_empty():
    match pc.pop()
    | :fun_start =>
      if t = 0:
        result = edge(a, b)
      else:
        c.push(0)
        pc.push(:loop_start)
    | :loop_start =>
      if c.top() = num_vertices:
        c.pop()
        result = 0
      else:
        a.push(a.top())
        b.push(c.top())
        t = t - 1
        pc.push(:after_first_rec)
        pc.push(:fun_start)
    | :after_first_rec =>
        a.pop()
        b.pop()
        t = t + 1
        if result == 1:
          a.push(c.top())
          b.push(b.top())
          t = t - 1
          pc.push(:after_second_rec)
          pc.push(:fun_start)
        else:
          result = 0
          pc.push(:loop_continue)
    | :after_second_rec =>
        a.pop()
        b.pop()
        t = t + 1
        if result == 1:
          c.pop()
        else:
          pc.push(:loop_continue)
    | :loop_continue =>
        c.top() += 1
        pc.push(:loop_start)
  -- cleanup
  initial_t.pop()
  t.pop()
  a.pop()
  b.pop()
-/

abbrev tapeCount := 20

@[simp, grind =]
lemma tape_count_eq : tapeCount = 20 := rfl

abbrev a : Fin tapeCount := ⟨3, sorry⟩
abbrev b : Fin tapeCount := ⟨4, sorry⟩
abbrev t : Fin tapeCount := ⟨5, sorry⟩
abbrev result : Fin tapeCount := ⟨6, sorry⟩
abbrev initialT : Fin tapeCount := ⟨7, sorry⟩
abbrev pc : Fin tapeCount := ⟨8, sorry⟩
abbrev c : Fin tapeCount := ⟨9, sorry⟩
abbrev mainAux : Fin tapeCount := ⟨10, sorry⟩

abbrev l_funStart := dya 1
abbrev l_loopStart := dya 2
abbrev l_afterFirstRec := dya 3
abbrev l_afterSecondRec := dya 4
abbrev l_loopContinue := dya 5

-- if t = 0:
--   result = edge(a, b)
-- else:
--   c.push(0)
--   pc.push(:loop_start)

def funStart (edge : MultiTapeTM tapeCount (WithSep OneTwo)) :=
  ite t (push c [] <;> push pc l_loopStart) edge

@[simp]
lemma funStart_eval_list
  (tapes : Fin tapeCount → List (List OneTwo))
  (edge : MultiTapeTM tapeCount (WithSep OneTwo)) :
  (funStart edge).eval_list tapes =
    if (tapes t).headD [] = [] then
      (edge.eval_list tapes)
    else
      .some (Function.update (Function.update tapes c ([] :: (tapes c)))
        pc (l_loopStart :: (tapes pc))) := by
  simp [funStart]

def infiniteLoop {α : Type} {k : ℕ} : MultiTapeTM k (WithSep α) := sorry

public def eqLit {k : ℕ}
  (q : Fin (k + 3))
  (w : List OneTwo)
  (s : Fin (k + 3))
  (aux : Fin (k + 3) := ⟨k + 2, by omega⟩)
  (h_inj : [q, aux, s].get.Injective := by intro x y; grind) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
    push aux w <;> eq q aux s h_inj <;> pop aux

@[simp]
public theorem eqLit_eval_list {k : ℕ} {q s aux : Fin (k + 3)} {w : List OneTwo}
  {h_inj : [q, aux, s].get.Injective}
  {tapes : Fin (k + 3) → List (List OneTwo)} :
  (eqLit q w s aux h_inj).eval_list tapes =
    .some (Function.update tapes s (
      (if (tapes q).headD [] = w then
        [.one]
      else
        []) :: (tapes s))) := by
  simp [eqLit, eq_eval_list h_inj]
  have h_neq : aux ≠ s := Function.Injective.ne h_inj (a₁ := 1) (a₂ := 2) (by grind)
  have h_neq : q ≠ aux := Function.Injective.ne h_inj (a₁ := 0) (a₂ := 1) (by grind)
  grind

-- | :loop_start =>
-- if c.top() = num_vertices:
--   c.pop()
--   result = 0
-- else:
--   a.push(a.top())
--   b.push(c.top())
--   t = t - 1
--   pc.push(:after_first_rec)
--   pc.push(:fun_start)

def loopStart (maxConfig : List OneTwo) :=
  eqLit c maxConfig mainAux <;>
    ite mainAux
      (pop mainAux <;> pop c <;> push result [])
      (pop mainAux <;> duplicate a <;> copy c b <;>
        dec t mainAux (by decide) <;> push pc l_afterFirstRec <;> push pc l_funStart)

-- TODO this simp lemma is probably not really needed, because the proof is just `simp [loopStart]`

-- @[simp]
-- lemma loopStart_eval_list
--   (maxConfig : List OneTwo)
--   (loopStart maxConfig).eval_list tapes = .some sorry := by
--   simp [loopStart]
--   sorry

-- | :after_first_rec =>
--     a.pop()
--     b.pop()
--     t = t + 1
--     if result == 1:
--       a.push(c.top())
--       b.push(b.top())
--       t = t - 1
--       pc.push(:after_second_rec)
--       pc.push(:fun_start)
--     else:
--       result = 0
--       pc.push(:loop_continue)

def afterFirstRec :=
  pop a <;> pop b <;> succ t <;> ite result
    (duplicate c <;> duplicate b <;> dec t mainAux (by decide) <;>
      push pc l_afterSecondRec <;> push pc l_funStart)
    (pop result <;> push result [] <;> push pc l_loopContinue)

-- | :after_second_rec =>
--     a.pop()
--     b.pop()
--     t = t + 1
--     if result == 1:
--       c.pop()
--     else:
--       pc.push(:loop_continue)

def afterSecondRec :=
  pop a <;> pop b <;> succ t <;> ite result (pop c) (push pc l_loopContinue)

-- | :loop_continue =>
--     c.top() += 1
--     pc.push(:loop_start)

def loopContinue := succ c <;> push pc l_loopStart

public def iteLit {k : ℕ}
  (i : Fin (k + 3))
  (w : List OneTwo)
  (aux : Fin (k + 3) := ⟨k + 1, by omega⟩)
  (tm₁ tm₂ : MultiTapeTM (k + 3) (WithSep OneTwo))
  (h_inj : [i, aux, aux + 1].get.Injective := by decide) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
    eqLit i w (aux + 1) aux (h_inj := by intro x y; grind) <;>
      ite (aux + 1) (pop (aux + 1) <;> tm₁) (pop (aux + 1) <;> tm₂)

-- TODO not sure if this simp lemma is needed. We can also put @[simp] at iteLit instead.

@[simp]
lemma itLit_eval_list {k : ℕ}
  (i : Fin (k + 3))
  (w : List OneTwo)
  (aux : Fin (k + 3))
  (tm₁ tm₂ : MultiTapeTM (k + 3) (WithSep OneTwo))
  (h_inj : [i, aux, aux + 1].get.Injective)
  (tapes : Fin (k + 3) → List (List OneTwo)) :
  (iteLit i w aux tm₁ tm₂ h_inj).eval_list tapes =
      if (tapes i).headD [] = w then tm₁.eval_list tapes else tm₂.eval_list tapes := by
  simp [iteLit]

public def matchCombine {k : ℕ}
  (i : Fin (k + 3)) (aux : Fin (k + 3)) (h_inj : [i, aux, aux + 1].get.Injective)
  (branches : List ((List OneTwo) × (MultiTapeTM (k + 3) (WithSep OneTwo)))) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
  match branches with
  | [] => infiniteLoop
  | (w, tm) :: branches =>
      eqLit i w aux (aux + 1) (h_inj := by sorry /- use swap on h_inj? -/) <;>
        ite aux (pop aux <;> tm) (pop aux <;> matchCombine i aux (by intro x y; grind) branches)

def innerLoop (edge : MultiTapeTM tapeCount (WithSep OneTwo)) (maxConfig : List OneTwo) :
    MultiTapeTM tapeCount (WithSep OneTwo) :=
  iteLit pc l_funStart mainAux (pop pc <;> funStart edge)
    (iteLit pc l_loopStart mainAux (pop pc <;> loopStart maxConfig)
      (iteLit pc l_afterFirstRec mainAux (pop pc <;> afterFirstRec)
        (iteLit pc l_afterSecondRec mainAux (pop pc <;> afterSecondRec)
          (pop pc <;> loopContinue))))

lemma innerLoop_eval_list
  (edge : MultiTapeTM tapeCount (WithSep OneTwo))
  (maxConfig : List OneTwo)
  (tapes : Fin tapeCount → List (List OneTwo)) :
  (innerLoop edge maxConfig).eval_list tapes = sorry := by
  simp [innerLoop, loopStart, afterFirstRec, afterSecondRec, loopContinue]
  sorry


end Routines
end Turing
