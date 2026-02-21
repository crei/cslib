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
        c.push(c.top() + 1)
        pc.push(:loop_start)
  -- cleanup
  initial_t.pop()
  t.pop()
  a.pop()
  b.pop()
-/

def tapeCount := 20

lemma tape_count_eq : tapeCount = 20 := rfl

def a : Fin tapeCount := ⟨3, sorry⟩
def b : Fin tapeCount := ⟨4, sorry⟩
def t : Fin tapeCount := ⟨5, sorry⟩
def result : Fin tapeCount := ⟨6, sorry⟩
def initialT : Fin tapeCount := ⟨7, sorry⟩
def pc : Fin tapeCount := ⟨8, sorry⟩
def c : Fin tapeCount := ⟨9, sorry⟩
def mainAux : Fin tapeCount := ⟨10, sorry⟩

def l_funStart := dya 1
def l_loopStart := dya 2

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
  have : pc ≠ c := by decide
  simp [funStart]
  grind

def infiniteLoop {α : Type} {k : ℕ} : MultiTapeTM k (WithSep α) := sorry

public def eqLit {k : ℕ}
  (q : Fin (k + 3))
  (w : List OneTwo)
  (s : Fin (k + 3))
  (aux : Fin (k + 3) := ⟨k + 2, by omega⟩)
  (h_inj : [q, aux, s].get.Injective := by intro x y; grind) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
    push aux w <;> eq q aux s h_inj <;> pop aux

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
      (duplicate a <;> copy c b <;> dec t <;> push pc l_funStart <;> push pc l_loopStart)

public def matchCombine {k : ℕ}
  (i : Fin (k + 3)) (aux : Fin (k + 3)) (h_inj : [i, aux, aux + 1].get.Injective)
  (branches : List ((List OneTwo) × (MultiTapeTM (k + 3) (WithSep OneTwo)))) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
  match branches with
  | [] => infiniteLoop
  | (w, tm) :: branches =>
      eqLit i w aux (aux + 1) (h_inj := by sorry /- use swap on h_inj? -/) <;>
        ite aux (pop aux <;> tm) (pop aux <;> matchCombine i aux (by intro x y; grind) branches)

def innerLoop (edge : MultiTapeTM tapeCount (WithSep OneTwo)) :
    MultiTapeTM tapeCount (WithSep OneTwo) :=
  matchCombine pc mainAux (by decide)
  [ (l_funStart, funStart edge),
    (l_loopStart, loop 1, infiniteLoop) ]



theorem reachable

end Routines
end Turing
