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
public import Cslib.Computability.Machines.MultiTapeTuring.WhileCombinator

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
    result = False
    for c in vertices:
      result |= reachable(a, c, t - 1, r) and reachable(c, b, t - 1, r)
    return result

Until we have a generic mechanism for recursion, let's translate this into a program that
uses "goto", and every variable is a stack:

def reachable(a, b, t, edge):
  pc = [:fun_start]
  while !pc.is_empty():
    match pc.pop()
    | :fun_start =>
      if t = 0:
        result.push(edge(a, b))
      else:
        c.push(0)
        result.push(0)
        pc.push(:loop_start)
    | :loop_start =>
      if c.top() = num_vertices:
        c.pop()
      else:
        a.push(a.top())
        b.push(c.top())
        t = t - 1
        pc.push(:after_first_rec)
        pc.push(:fun_start)
    | :after_first_rec =>
        a.pop()
        b.pop()
        -- we keep the result of the first recursive call.
        a.push(c.top())
        b.push(b.top())
        pc.push(:after_second_rec)
        pc.push(:fun_start)
    | :after_second_rec =>
        a.pop()
        b.pop()
        t = t + 1
        result.push(result.pop() ∨ result.pop() ∨ result.pop())
        c.top() += 1
        pc.push(:loop_start)
  -- cleanup
  t.pop()
  a.pop()
  b.pop()
-/

abbrev tapeCount := 20

@[simp, grind =]
lemma tape_count_eq : tapeCount = 20 := rfl

abbrev a : Fin tapeCount := ⟨0, sorry⟩
abbrev b : Fin tapeCount := ⟨1, sorry⟩
abbrev t : Fin tapeCount := ⟨3, sorry⟩
abbrev result : Fin tapeCount := ⟨2, sorry⟩
abbrev initialT : Fin tapeCount := ⟨7, sorry⟩
abbrev pc : Fin tapeCount := ⟨8, sorry⟩
abbrev c : Fin tapeCount := ⟨9, sorry⟩
abbrev mainAux : Fin tapeCount := ⟨10, sorry⟩

abbrev l_funStart := dya 1
abbrev l_loopStart := dya 2
abbrev l_afterFirstRec := dya 3
abbrev l_afterSecondRec := dya 4
abbrev l_loopContinue := dya 5

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

@[simp]
public def iteLit {k : ℕ}
  (i : Fin (k + 3))
  (w : List OneTwo)
  (aux : Fin (k + 3) := ⟨k + 1, by omega⟩)
  (tm₁ tm₂ : MultiTapeTM (k + 3) (WithSep OneTwo))
  (h_inj : [i, aux, aux + 1].get.Injective := by decide) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
    eqLit i w (aux + 1) aux (h_inj := by intro x y; grind) <;>
      ite (aux + 1) (pop (aux + 1) <;> tm₁) (pop (aux + 1) <;> tm₂)

@[simp]
public def combineOr {k : ℕ} (i : Fin k) :
  MultiTapeTM k (WithSep OneTwo) :=
    ite i
      (pop i <;> pop i <;> push i [OneTwo.one])
      (pop i <;>
        ite i
          (pop i <;> push i [OneTwo.one])
          (pop i <;> push i []))


-- | :fun_start =>
-- if t = 0:
--   result.push(edge(a, b))
-- else:
--   c.push(0)
--   result.push(0)
--   pc.push(:loop_start)

@[simp]
def funStart (edge : MultiTapeTM tapeCount (WithSep OneTwo)) :=
  ite t (push c [] <;> push result [] <;> push pc l_loopStart) edge

-- | :loop_start =>
-- if c.top() = num_vertices:
--   c.pop()
-- else:
--   a.push(a.top())
--   b.push(c.top())
--   t = t - 1
--   pc.push(:after_first_rec)
--   pc.push(:fun_start)

@[simp]
def loopStart (maxConfig : List OneTwo) :=
  iteLit c maxConfig mainAux
    (pop c)
    (duplicate a <;> copy c b <;>
      dec t mainAux (by decide) <;> push pc l_afterFirstRec <;> push pc l_funStart)

-- | :after_first_rec =>
-- a.pop()
-- b.pop()
-- -- we keep the result of the first recursive call.
-- a.push(c.top())
-- b.push(b.top())
-- pc.push(:after_second_rec)
-- pc.push(:fun_start)

@[simp]
def afterFirstRec :=
  pop a <;> pop b <;> copy c a <;> duplicate b <;>
    push pc l_afterSecondRec <;> push pc l_funStart

-- | :after_second_rec =>
-- a.pop()
-- b.pop()
-- t = t + 1
-- result.push(result.pop() ∨ result.pop() ∨ result.pop())
-- c.top() += 1
-- pc.push(:loop_start)

@[simp]
def afterSecondRec :=
  pop a <;> pop b <;> succ t <;>
    combineOr result <;> combineOr result <;> succ c <;> push pc l_loopStart


@[simp]
def innerLoop (edge : MultiTapeTM tapeCount (WithSep OneTwo)) (maxConfig : List OneTwo) :
    MultiTapeTM tapeCount (WithSep OneTwo) :=
  iteLit pc l_funStart mainAux (pop pc <;> funStart edge)
    (iteLit pc l_loopStart mainAux (pop pc <;> loopStart maxConfig)
      (iteLit pc l_afterFirstRec mainAux (pop pc <;> afterFirstRec)
        (pop pc <;> afterSecondRec)))

lemma relatesInStepsExp {α : Type}
  (r : α → α → Prop)
  (a b : α)
  (t : ℕ) :
  (Relation.RelatesInSteps r a b (Nat.pow 2 t.succ)) ↔
  ∃ c, Relation.RelatesInSteps r a c (Nat.pow 2 t) ∧
       Relation.RelatesInSteps r c b (Nat.pow 2 t) := by
  sorry

def finiteRel (r : (List OneTwo) → (List OneTwo) → Prop) (max : ℕ) : Prop :=
  ∀ a b, r a b → (dya_inv a < max ∧ dya_inv b < max)

lemma finiteRel_apply₁ {r : (List OneTwo) → (List OneTwo) → Prop} {max : ℕ}
  (h_finite : finiteRel r max) {a b : List OneTwo} (h_r : r a b) :
    dya_inv a < max := (h_finite a b h_r).1

lemma finiteRel_apply₂ {r : (List OneTwo) → (List OneTwo) → Prop} {max : ℕ}
  (h_finite : finiteRel r max) {a b : List OneTwo} (h_r : r a b) :
    dya_inv b < max := (h_finite a b h_r).2

def edge_semantics
  (r : (List OneTwo) → (List OneTwo) → Prop)
  (h_r_dec : ∀ x y, Decidable (r x y))
  (edge : MultiTapeTM tapeCount (WithSep OneTwo)) : Prop :=
  ∀ tapes,
  edge.eval_list tapes = .some (if r ((tapes a).headD []) ((tapes b).headD []) then
    Function.update tapes result ([.one] :: (tapes result))
  else
    Function.update tapes result ([] :: (tapes result)))

lemma inner_loop_halts_on_lists
  {r : (List OneTwo) → (List OneTwo) → Prop}
  {h_r_dec : ∀ x y, Decidable (r x y)}
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  (h_edge_semantics : edge_semantics r h_r_dec edge)
  {maxConfig : List OneTwo} :
  ∀ tapes, (innerLoop edge maxConfig).HaltsOnLists tapes := by
  intro tapes
  apply MultiTapeTM.HaltsOnLists_of_eval_list
  unfold edge_semantics at h_edge_semantics
  simp [h_edge_semantics]
  split_ifs
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
    split_ifs
    · simp
    · simp
  · simp
  · simp

def reachability
  (edge : MultiTapeTM tapeCount (WithSep OneTwo))
  (maxConfig : List OneTwo)
  (x y : List OneTwo)
  (t_val : ℕ) :=
  push a x <;> push b y <;> push t (dya t_val) <;> push pc [] <;> push pc l_funStart <;>
    doWhile pc (innerLoop edge maxConfig) <;>
    pop t <;> pop a <;> pop b

@[simp]
def iter_count_bound (max : ℕ) (t : ℕ) : ℕ := match t with
  | .zero => 1
  | .succ t' => 2 + max * (3 + 2 * iter_count_bound max t')

@[simp]
noncomputable def innerLoopFun
  {r : (List OneTwo) → (List OneTwo) → Prop}
  {h_r_dec : ∀ x y, Decidable (r x y)}
  (max : ℕ)
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  (h_edge_semantics : edge_semantics r h_r_dec edge) :=
    (innerLoop edge (dya max)).eval_list_tot (inner_loop_halts_on_lists h_edge_semantics)

-- TODO continue here: prove this theorem by induction.
lemma loop_semantics
  {r : (List OneTwo) → (List OneTwo) → Prop}
  {h_r_dec : ∀ x y, Decidable (r x y)}
  (h_rs_dec : ∀ x y t, Decidable (Relation.RelatesInSteps r x y t))
  {max : ℕ}
  (h_finite : finiteRel r max)
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  (h_edge_semantics : edge_semantics r h_r_dec edge)
  (tapes : Fin tapeCount → List (List OneTwo))
  (h_pc_funStart : (tapes pc).head?.getD [] = l_funStart) :
    (innerLoopFun max h_edge_semantics)^[iter_count_bound max (dya_inv ((tapes t).headD []))]
        tapes = Function.update (Function.update tapes
      pc (tapes pc).tail)
      result (
        if Relation.RelatesInSteps r ((tapes a).headD []) ((tapes b).headD [])
              (Nat.pow 2 (dya_inv ((tapes t).headD []))) then
          [.one] :: (tapes result)
        else
          [] :: (tapes result)) ∧
      ∀ n' < iter_count_bound max (dya_inv ((tapes t).headD [])),
        (((innerLoopFun max h_edge_semantics)^[n'] tapes) pc).length ≥ (tapes pc).length := by
  induction h_t : (dya_inv ((tapes t).headD [])) generalizing tapes with
    | zero =>
      have h_t_dya : (tapes t).head?.getD [] = dya 0 := by rw [← h_t]; simp
      unfold edge_semantics at h_edge_semantics
      simp [h_edge_semantics, h_pc_funStart, h_t_dya, Relation.RelatesInSteps.single_iff]
      split
      · simp
      · simp
    | succ t_val ih =>
      by_cases h_rel : Relation.RelatesInSteps r
          ((tapes a).headD []) ((tapes b).headD []) (Nat.pow 2 (t_val + 1))
      · simp only [h_rel]
        simp
        obtain ⟨c, h_c_rel⟩ :=
          (relatesInStepsExp r ((tapes a).headD []) ((tapes b).headD []) t_val).mp h_rel
        have h_c_le : dya_inv c < max := by sorry

        sorry
      · sorry


theorem reachability_eval_list
  {r : (List OneTwo) → (List OneTwo) → Prop}
  {h_r_dec : ∀ x y, Decidable (r x y)}
  (h_rs_dec : ∀ x y t, Decidable (Relation.RelatesInSteps r x y t))
  {max : ℕ}
  (h_finite : finiteRel r max)
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  (h_edge_semantics : edge_semantics r h_r_dec edge)
  {t_val : ℕ}
  {a_val b_val : List OneTwo}
  {tapes : Fin tapeCount → List (List OneTwo)} :
  (reachability edge (dya max) a_val b_val t_val).eval_list tapes = .some (Function.update tapes
    result (
      if Relation.RelatesInSteps r a_val b_val t_val then
        [.one] :: (tapes result)
      else
        [] :: (tapes result))) := by
  simp [reachability]
  sorry


end Routines
end Turing
