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

abbrev l_funStart := [OneTwo.one]
abbrev l_loopStart := [OneTwo.two]
abbrev l_afterFirstRec := [OneTwo.one, OneTwo.one]
abbrev l_afterSecondRec := [OneTwo.one, OneTwo.two]
abbrev l_loopContinue := [OneTwo.two, OneTwo.one]

public def eqLit {k : ℕ}
  (q : Fin (k + 3))
  (w : List OneTwo)
  (s : Fin (k + 3))
  (aux : Fin (k + 3) := ⟨k + 2, by omega⟩)
  (h_inj : [q, aux, s].get.Injective := by intro x y; grind) :
  MultiTapeTM (k + 3) (WithSep OneTwo) :=
    push aux w ;ₜ eq q aux s h_inj ;ₜ pop aux

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
    eqLit i w (aux + 1) aux (h_inj := by intro x y; grind) ;ₜ
      ite (aux + 1) (pop (aux + 1) ;ₜ tm₁) (pop (aux + 1) ;ₜ tm₂)

@[simp]
public def combineAnd {k : ℕ} (i : Fin k) :
  MultiTapeTM k (WithSep OneTwo) :=
    ite i
      (pop i ;ₜ
        ite i
          (pop i ;ₜ push i [OneTwo.one])
          (pop i ;ₜ push i []))
      (pop i ;ₜ pop i ;ₜ push i [])

@[simp]
public def combineOr {k : ℕ} (i : Fin k) :
  MultiTapeTM k (WithSep OneTwo) :=
    ite i
      (pop i ;ₜ pop i ;ₜ push i [OneTwo.one])
      (pop i ;ₜ
        ite i
          (pop i ;ₜ push i [OneTwo.one])
          (pop i ;ₜ push i []))


-- | :fun_start =>
-- if t = 0:
--   result.push(edge(a, b))
-- else:
--   c.push(0)
--   result.push(0)
--   pc.push(:loop_start)

@[simp]
def funStart (edge : MultiTapeTM tapeCount (WithSep OneTwo)) :=
  ite t (push c [] ;ₜ push result [] ;ₜ push pc l_loopStart) edge

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
    (duplicate a ;ₜ copy c b ;ₜ
      dec t mainAux (by decide) ;ₜ push pc l_afterFirstRec ;ₜ push pc l_funStart)

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
  pop a ;ₜ pop b ;ₜ copy c a ;ₜ duplicate b ;ₜ
    push pc l_afterSecondRec ;ₜ push pc l_funStart

-- | :after_second_rec =>
-- a.pop()
-- b.pop()
-- t = t + 1
-- result.push(result.pop() ∨ result.pop() ∨ result.pop())
-- c.top() += 1
-- pc.push(:loop_start)

@[simp]
def afterSecondRec :=
  pop a ;ₜ pop b ;ₜ succ t ;ₜ
    combineAnd result ;ₜ combineOr result ;ₜ succ c ;ₜ push pc l_loopStart

def innerLoop (edge : MultiTapeTM tapeCount (WithSep OneTwo)) (maxConfig : List OneTwo) :
    MultiTapeTM tapeCount (WithSep OneTwo) :=
  iteLit pc l_funStart mainAux (pop pc ;ₜ funStart edge)
    (iteLit pc l_loopStart mainAux (pop pc ;ₜ loopStart maxConfig)
      (iteLit pc l_afterFirstRec mainAux (pop pc ;ₜ afterFirstRec)
        (pop pc ;ₜ afterSecondRec)))

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
  simp [h_edge_semantics, innerLoop]
  split_ifs <;> simp <;> split_ifs <;> simp

def reachability
  (edge : MultiTapeTM tapeCount (WithSep OneTwo))
  (maxConfig : List OneTwo)
  (x y : List OneTwo)
  (t_val : ℕ) :=
  push a x ;ₜ push b y ;ₜ push t (dya t_val) ;ₜ push pc [] ;ₜ push pc l_funStart ;ₜ
    doWhile pc (innerLoop edge maxConfig) ;ₜ
    pop t ;ₜ pop a ;ₜ pop b

@[simp]
def iter_count_bound (max : ℕ) (t : ℕ) : ℕ := match t with
  | .zero => 1
  | .succ t' => 2 + max * (3 + 2 * iter_count_bound max t')

def innerLoopFun
  {r : (List OneTwo) → (List OneTwo) → Prop}
  {h_r_dec : ∀ x y, Decidable (r x y)}
  (max : ℕ)
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  (h_edge_semantics : edge_semantics r h_r_dec edge) :=
    (innerLoop edge (dya max)).eval_list_tot (inner_loop_halts_on_lists h_edge_semantics)

lemma inner_loop_start
  {max : ℕ}
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  {tapes : Fin tapeCount → List (List OneTwo)}
  (h_pc_loopStart : (tapes pc).head?.getD [] = l_loopStart) :
  (innerLoop edge (dya max)).eval_list tapes = Part.some (if (tapes c).head?.getD [] = dya max then
      Function.update (Function.update tapes pc (tapes pc).tail) c (tapes c).tail
    else
      Function.update (Function.update (Function.update (Function.update tapes
        a ((tapes a).head?.getD [] :: tapes a))
        b ((tapes c).head?.getD [] :: tapes b))
        t (dya (dya_inv ((tapes t).head?.getD []) - 1) :: (tapes t).tail))
        pc (l_funStart :: l_afterFirstRec :: (tapes pc).tail)) := by
  simp [innerLoop, h_pc_loopStart]
  split_ifs <;> simp ; grind

-- TODO the result of eval_list makes heavy use of
-- Function.update tapes x (f(tapes) :: (tapes x).tail)
-- create an abstraction for that? Sometimes we need .tail.tail

lemma inner_loop_after_first_rec
  {max : ℕ}
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  {tapes : Fin tapeCount → List (List OneTwo)}
  (h_pc_afterFirstRec : (tapes pc).head?.getD [] = l_afterFirstRec) :
  (innerLoop edge (dya max)).eval_list tapes = Part.some (
    Function.update (Function.update (Function.update tapes
    a ((tapes c).head?.getD [] :: (tapes a).tail))
    b ((tapes b)[1]?.getD [] :: (tapes b).tail))
    pc (l_funStart :: l_afterSecondRec :: (tapes pc).tail)) := by
  simp [innerLoop, h_pc_afterFirstRec]
  grind

lemma function_update_sort
  {α : Type} {k : ℕ} {x y : Fin k} {h_lt : x < y}
  {a b : α} {f : Fin k → α} :
  Function.update (Function.update f x a) y b =
    Function.update (Function.update f y b) x a := by grind

lemma function_update_pull
  {α : Type} {k : ℕ} (x : Fin k) {y : Fin k} {h_lt : x ≠ y}
  {a b : α} {f : Fin k → α} :
  Function.update (Function.update f x a) y b =
    Function.update (Function.update f y b) x a := by grind

lemma inner_loop_after_second_rec
  {max : ℕ}
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  {tapes : Fin tapeCount → List (List OneTwo)}
  (h_pc_afterSecondRec : (tapes pc).head?.getD [] = l_afterSecondRec) :
  (innerLoop edge (dya max)).eval_list tapes = Part.some (
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update tapes
    a (tapes a).tail)
    b (tapes b).tail)
    t (dya (dya_inv ((tapes t).head?.getD []) + 1) :: (tapes t).tail))
    result (
      (if (((tapes result).head?.getD [] != []) ∧
         (tapes result)[1]?.getD [] != []) ∨
         (tapes result)[2]?.getD [] != [] then
        [.one]
      else
        []) :: (tapes result).tail.tail.tail))
    c (dya (dya_inv ((tapes c).head?.getD []) + 1) :: (tapes c).tail))
    pc (l_loopStart :: (tapes pc).tail)) := by
  simp [innerLoop, h_pc_afterSecondRec]
  split_ifs
  · simp
    split_ifs <;> simp <;> grind
  · simp
    split_ifs <;> simp <;> grind
  · simp
    split_ifs <;> simp <;> grind
  · simp
    split_ifs <;> simp <;> grind
  · simp
    grind
  · simp
    grind

@[simp]
lemma list_getElem?_zero_eq_head? {α : Type} (l : List α) :
  l[0]? = l.head? := by
  cases l with
  | nil => simp
  | cons a l => simp

private lemma innerLoopFun_eq_of_eval_list
  {r : (List OneTwo) → (List OneTwo) → Prop}
  {h_r_dec : ∀ x y, Decidable (r x y)}
  {max : ℕ}
  {edge : MultiTapeTM tapeCount (WithSep OneTwo)}
  {h_edge_semantics : edge_semantics r h_r_dec edge}
  {tapes result' : Fin tapeCount → List (List OneTwo)}
  (h : (innerLoop edge (dya max)).eval_list tapes = Part.some result') :
  innerLoopFun max h_edge_semantics tapes = result' :=
  MultiTapeTM.eval_list_tot_eq_of_eval_list _ _ _ _ h

set_option maxHeartbeats 4000000 in
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
  induction h_t : (dya_inv ((tapes t).head?.getD [])) generalizing tapes with
    | zero =>
      have h_t_dya : (tapes t).head?.getD [] = dya 0 := by rw [← h_t]; simp
      have h_t_empty : (tapes t).head?.getD [] = [] := by rw [h_t_dya]; simp
      unfold edge_semantics at h_edge_semantics
      have h_headD : dya_inv ((tapes t).headD []) = 0 := by
        rw [List.headD_eq_head?]; exact h_t
      rw [h_headD]; simp only [iter_count_bound, Function.iterate_one, Nat.pow]
      constructor
      · -- Main equality: innerLoopFun tapes = expected (with 2^0 = 1)
        show innerLoopFun max h_edge_semantics tapes = _
        have h_eval : (innerLoop edge (dya max)).eval_list tapes =
            Part.some (if r ((tapes a).headD []) ((tapes b).headD []) then
              Function.update (Function.update tapes pc (tapes pc).tail)
                result ([OneTwo.one] :: tapes result)
            else
              Function.update (Function.update tapes pc (tapes pc).tail)
                result ([] :: tapes result)) := by
          simp [innerLoop, h_pc_funStart, h_t_empty, h_edge_semantics]
        rw [innerLoopFun_eq_of_eval_list h_eval]
        simp only [Relation.RelatesInSteps.single_iff]
        split_ifs <;> rfl
      · -- PC length property: trivially true for n' < 1 (n' = 0)
        intro n' h_n'
        have : n' = 0 := by omega
        subst this; simp
    | succ t_val ih =>
      have h_inner (tapes : Fin tapeCount → List (List OneTwo))
        (h_pc : (tapes pc).head?.getD [] = l_loopStart)
        (h_c : (tapes c).head?.getD [] ≠ dya max)
        (h_t : dya_inv ((tapes t).head?.getD []) = t_val.succ) :
        (innerLoopFun max h_edge_semantics)^[3 + 2 * (iter_count_bound max t_val)] tapes =
          Function.update (Function.update (Function.update (Function.update tapes
              c ((dya_succ ((tapes c).headD [])) :: (tapes c).tail))
              t (dya (t_val.succ) :: (tapes t).tail))
              pc (l_loopStart :: (tapes pc).tail))
              result (if
                ((tapes result).headD [] != []) ∨
                (Relation.RelatesInSteps r ((tapes a).headD []) ((tapes c).headD []) (2 ^ t_val) ∧
                Relation.RelatesInSteps r ((tapes c).headD []) ((tapes b).headD []) (2 ^ t_val))
                then
                  [.one] :: (tapes result).tail
                else
                  [] :: (tapes result).tail) := by
        -- Decompose f^[3+2n] into f ∘ f^[n] ∘ f ∘ f^[n] ∘ f
        conv_lhs => rw [show 3 + 2 * iter_count_bound max t_val =
          1 + (iter_count_bound max t_val +
            (1 + (iter_count_bound max t_val + 1))) from by omega]
        simp only [Function.iterate_add_apply, Function.iterate_one]
        -- Goal: f (f^[n] (f (f^[n] (f tapes)))) = target
        -- Step 1: inner_loop_start (loopStart, c ≠ max)
        have h_step1_eval := @inner_loop_start max edge tapes h_pc
        simp only [if_neg h_c] at h_step1_eval
        have h_step1 := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
          h_edge_semantics _ _ h_step1_eval
        rw [h_step1]
        -- After step 1: a pushed, b gets c.headD, t decremented, pc = funStart::afterFirstRec::tail
        -- Step 2: First recursive call (ih with t_val)
        have h_t_sub : dya_inv ((tapes t).head?.getD []) - 1 = t_val := by omega
        have h_pc₁ : (Function.update (Function.update (Function.update (Function.update tapes
            a ((tapes a).head?.getD [] :: tapes a))
            b ((tapes c).head?.getD [] :: tapes b))
            t (dya (dya_inv ((tapes t).head?.getD []) - 1) :: (tapes t).tail))
            pc (l_funStart :: l_afterFirstRec :: (tapes pc).tail) pc).head?.getD []
            = l_funStart := by
          simp [Function.update_self]
        have h_t₁ : dya_inv ((Function.update (Function.update (Function.update (Function.update
            tapes
            a ((tapes a).head?.getD [] :: tapes a))
            b ((tapes c).head?.getD [] :: tapes b))
            t (dya (dya_inv ((tapes t).head?.getD []) - 1) :: (tapes t).tail))
            pc (l_funStart :: l_afterFirstRec :: (tapes pc).tail) t).head?.getD [])
            = t_val := by
          have h_ne : pc ≠ t := by decide
          simp [Function.update_of_ne h_ne, Function.update_self, h_t_sub, dya_inv_dya]
        obtain ⟨h_ih₁, h_ih₁_pc⟩ := ih _ h_pc₁ h_t₁
        -- h_ih₁ uses dya_inv(headD) which we need to show equals t_val
        -- Convert headD to head?.getD for matching
        have h_headD₁ : dya_inv ((Function.update (Function.update (Function.update
            (Function.update tapes
            a ((tapes a).head?.getD [] :: tapes a))
            b ((tapes c).head?.getD [] :: tapes b))
            t (dya (dya_inv ((tapes t).head?.getD []) - 1) :: (tapes t).tail))
            pc (l_funStart :: l_afterFirstRec :: (tapes pc).tail) t).headD [])
            = t_val := by
          rw [List.headD_eq_head?]; exact h_t₁
        rw [h_headD₁] at h_ih₁
        rw [h_ih₁]
        -- After step 2: goal is f (f^[n] (f <post-IH1>)) = target
        -- where post-IH1 = Function.update (Function.update tapes₁ pc tail) result (...)
        -- Step 3: inner_loop_after_first_rec
        -- Need pc of post-IH1 = l_afterFirstRec
        -- post-IH1 pc = (Function.update tapes₁ pc (tapes₁ pc).tail) pc = (tapes₁ pc).tail
        --             = (l_funStart :: l_afterFirstRec :: (tapes pc).tail).tail
        --             = l_afterFirstRec :: (tapes pc).tail
        -- So head?.getD [] = l_afterFirstRec ✓
        -- Define tapes₁ for reference in step 3 proofs
        set tapes₁ := Function.update (Function.update (Function.update (Function.update tapes
          a ((tapes a).head?.getD [] :: tapes a))
          b ((tapes c).head?.getD [] :: tapes b))
          t (dya (dya_inv ((tapes t).head?.getD []) - 1) :: (tapes t).tail))
          pc (l_funStart :: l_afterFirstRec :: (tapes pc).tail) with htapes₁_def
        set tapes₂ := Function.update (Function.update tapes₁
          pc (tapes₁ pc).tail)
          result (if Relation.RelatesInSteps r ((tapes₁ a).headD []) ((tapes₁ b).headD [])
            (Nat.pow 2 t_val) then [OneTwo.one] :: tapes₁ result
            else [] :: tapes₁ result) with htapes₂_def
        have h_pc₂ : (tapes₂ pc).head?.getD [] = l_afterFirstRec := by
          simp only [htapes₂_def]
          have : result ≠ pc := by decide
          simp [Function.update_of_ne this, Function.update_self]
          simp [htapes₁_def, Function.update_self]
        have h_step3_eval := @inner_loop_after_first_rec max edge tapes₂ h_pc₂
        have h_step3 := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
          h_edge_semantics _ _ h_step3_eval
        rw [h_step3]
        -- After step 3: a/b swapped, pc = funStart::afterSecondRec::tail
        -- Step 4: Second recursive call (ih with t_val)
        set tapes₃ := Function.update (Function.update (Function.update tapes₂
          a ((tapes₂ c).head?.getD [] :: (tapes₂ a).tail))
          b ((tapes₂ b)[1]?.getD [] :: (tapes₂ b).tail))
          pc (l_funStart :: l_afterSecondRec :: (tapes₂ pc).tail) with htapes₃_def
        have h_pc₃ : (tapes₃ pc).head?.getD [] = l_funStart := by
          simp [htapes₃_def, Function.update_self]
        have h_t₃ : dya_inv ((tapes₃ t).head?.getD []) = t_val := by
          have h1 : pc ≠ t := by decide
          have h2 : b ≠ t := by decide
          have h3 : a ≠ t := by decide
          have h4 : result ≠ t := by decide
          simp [htapes₃_def, htapes₂_def, htapes₁_def,
            Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h3, Function.update_of_ne h4,
            Function.update_self, h_t_sub, dya_inv_dya]
        obtain ⟨h_ih₂, h_ih₂_pc⟩ := ih _ h_pc₃ h_t₃
        have h_headD₃ : dya_inv ((tapes₃ t).headD []) = t_val := by
          rw [List.headD_eq_head?]; exact h_t₃
        rw [h_headD₃] at h_ih₂
        rw [h_ih₂]
        -- After step 4: result has second recursive check
        -- Step 5: inner_loop_after_second_rec
        set tapes₄ := Function.update (Function.update tapes₃
          pc (tapes₃ pc).tail)
          result (if Relation.RelatesInSteps r ((tapes₃ a).headD []) ((tapes₃ b).headD [])
            (Nat.pow 2 t_val) then [OneTwo.one] :: tapes₃ result
            else [] :: tapes₃ result) with htapes₄_def
        have h_pc₄ : (tapes₄ pc).head?.getD [] = l_afterSecondRec := by
          simp only [htapes₄_def]
          have : result ≠ pc := by decide
          simp [Function.update_of_ne this, Function.update_self]
          simp [htapes₃_def, Function.update_self]
        have h_step5_eval := @inner_loop_after_second_rec max edge tapes₄ h_pc₄
        have h_step5 := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
          h_edge_semantics _ _ h_step5_eval
        rw [h_step5]
        -- Now goal is: the 6-nested Function.update chain on tapes₄ = the 4-nested target
        -- We need to show that after unfolding tapes₄, tapes₃, tapes₂, tapes₁, the result
        -- matches the target. This requires extensive Function.update simplification for
        -- each tape index (a, b, c, t, pc, result, and all others).
        -- The key equalities needed:
        -- * a: (... a).tail restores original tapes a
        -- * b: (... b).tail restores original tapes b
        -- * c: dya(dya_inv(c.head) + 1) = dya_succ(c.headD) by definition
        -- * t: dya(dya_inv(dya(t_val)) + 1) = dya(t_val.succ) since dya_inv_dya
        -- * pc: l_loopStart :: tail chain = l_loopStart :: (tapes pc).tail
        -- * result: combines the two recursive checks via inner_loop_after_second_rec logic
        ext i
        by_cases h_i_result : i = result
        · -- result tape: most complex case
          subst h_i_result
          -- Don't unfold set definitions - instead compute through layers
          -- The outer Function.update chain (from inner_loop_after_second_rec) at result:
          -- Since pc ≠ result and c ≠ result, the result value is the 4th update.
          simp only [
            Function.update_of_ne (show pc ≠ result by decide),
            Function.update_of_ne (show c ≠ result by decide),
            Function.update_self]
          -- Now goal: (if cond_on_tapes₄ then [.one] else []) :: (tapes₄ result).tail.tail.tail
          --         = (if target_cond then [.one] :: tail else [] :: tail)
          -- Extract what tapes₄ result is
          have h_t4_result : tapes₄ result =
              (if Relation.RelatesInSteps r ((tapes₃ a).headD []) ((tapes₃ b).headD [])
                (Nat.pow 2 t_val) then [OneTwo.one] :: tapes₃ result
              else [] :: tapes₃ result) := by
            simp [htapes₄_def, Function.update_self]
          have h_t3_result : tapes₃ result = tapes₂ result := by
            simp [htapes₃_def, Function.update_of_ne (show pc ≠ result by decide),
              Function.update_of_ne (show b ≠ result by decide),
              Function.update_of_ne (show a ≠ result by decide)]
          have h_t2_result : tapes₂ result =
              (if Relation.RelatesInSteps r ((tapes₁ a).headD []) ((tapes₁ b).headD [])
                (Nat.pow 2 t_val) then [OneTwo.one] :: tapes₁ result
              else [] :: tapes₁ result) := by
            simp [htapes₂_def, Function.update_self]
          have h_t1_result : tapes₁ result = tapes result := by
            simp [htapes₁_def, Function.update_of_ne (show pc ≠ result by decide),
              Function.update_of_ne (show t ≠ result by decide),
              Function.update_of_ne (show b ≠ result by decide),
              Function.update_of_ne (show a ≠ result by decide)]
          -- Extract IH tape values
          have h_t1_a : (tapes₁ a).headD [] = (tapes a).head?.getD [] := by
            simp [htapes₁_def, Function.update_of_ne (show pc ≠ a by decide),
              Function.update_of_ne (show t ≠ a by decide),
              Function.update_of_ne (show b ≠ a by decide),
              Function.update_self]
          have h_t1_b : (tapes₁ b).headD [] = (tapes c).head?.getD [] := by
            simp [htapes₁_def, Function.update_of_ne (show pc ≠ b by decide),
              Function.update_of_ne (show t ≠ b by decide),
              Function.update_self]
          have h_t3_a : (tapes₃ a).headD [] = (tapes c).head?.getD [] := by
            simp [htapes₃_def, Function.update_of_ne (show pc ≠ a by decide),
              Function.update_of_ne (show b ≠ a by decide),
              Function.update_self, htapes₂_def,
              Function.update_of_ne (show result ≠ a by decide),
              htapes₁_def, Function.update_of_ne (show t ≠ a by decide),
              Function.update_of_ne (show c ≠ a by decide), List.headD_eq_head?]
          have h_t3_b : (tapes₃ b).headD [] = (tapes b).head?.getD [] := by
            simp [htapes₃_def, Function.update_of_ne (show pc ≠ b by decide),
              Function.update_of_ne (show a ≠ b by decide),
              htapes₂_def, Function.update_of_ne (show result ≠ b by decide),
              htapes₁_def, Function.update_of_ne (show t ≠ b by decide),
              Function.update_self, List.headD_eq_head?]
          -- Rewrite tapes₄ result through the chain
          rw [h_t4_result, h_t3_result, h_t2_result, h_t1_result]
          rw [h_t1_a, h_t1_b, h_t3_a, h_t3_b]
          simp only [List.headD_eq_head?]
          -- Now the goal has small terms with explicit ifs
          -- Case split on path2 (the outer if of tapes₄ result)
          split_ifs with h_path2 h_path1 h_path1 h_path2 h_path1 h_path1
          all_goals simp_all [bne_iff_ne]
        · by_cases h_i_c : i = c
          · subst h_i_c
            -- c: dya(dya_inv(c.head) + 1) :: c.tail = dya_succ(c.headD) :: c.tail
            simp_all only [htapes₄_def, htapes₃_def, htapes₂_def, htapes₁_def]
            simp [Function.update_self,
              Function.update_of_ne (show pc ≠ c by decide),
              Function.update_of_ne (show result ≠ c by decide),
              Function.update_of_ne (show t ≠ c by decide),
              Function.update_of_ne (show b ≠ c by decide),
              Function.update_of_ne (show a ≠ c by decide),
              dya_succ, List.headD_eq_head?]
          · by_cases h_i_t : i = t
            · subst h_i_t
              -- t: dya(dya_inv(tapes₄ t head) + 1) :: tail → dya(t_val.succ) :: tail
              simp_all only [htapes₄_def, htapes₃_def, htapes₂_def, htapes₁_def]
              simp [Function.update_self,
                Function.update_of_ne (show pc ≠ t by decide),
                Function.update_of_ne (show c ≠ t by decide),
                Function.update_of_ne (show result ≠ t by decide),
                Function.update_of_ne (show b ≠ t by decide),
                Function.update_of_ne (show a ≠ t by decide),
                h_t_sub, dya_inv_dya]
            · by_cases h_i_pc : i = pc
              · subst h_i_pc
                -- pc: l_loopStart :: (tapes₄ pc).tail → l_loopStart :: (tapes pc).tail
                simp only [Function.update_self,
                  Function.update_of_ne (show c ≠ pc by decide),
                  Function.update_of_ne (show result ≠ pc by decide),
                  Function.update_of_ne (show t ≠ pc by decide),
                  Function.update_of_ne (show b ≠ pc by decide),
                  Function.update_of_ne (show a ≠ pc by decide)]
                simp only [htapes₄_def, Function.update_of_ne (show result ≠ pc by decide),
                  Function.update_self]
                simp only [htapes₃_def, Function.update_self]
                simp only [htapes₂_def, Function.update_of_ne (show result ≠ pc by decide),
                  Function.update_self]
                simp [htapes₁_def, Function.update_self]
              · -- Other tapes: a, b need special handling (push/pop)
                by_cases h_i_a : i = a
                · -- a tape: pushed in step 1, popped in step 5 → restored
                  subst h_i_a
                  simp [htapes₄_def, htapes₃_def, htapes₂_def, htapes₁_def,
                    Function.update_self, Function.update_of_ne (show a ≠ pc by decide),
                    Function.update_of_ne (show a ≠ result by decide),
                    Function.update_of_ne (show a ≠ b by decide),
                    Function.update_of_ne (show a ≠ t by decide),
                    Function.update_of_ne (show a ≠ c by decide)]
                · by_cases h_i_b : i = b
                  · -- b tape: pushed in step 1, popped in step 5 → restored
                    subst h_i_b
                    simp [htapes₄_def, htapes₃_def, htapes₂_def, htapes₁_def,
                      Function.update_self, Function.update_of_ne (show b ≠ pc by decide),
                      Function.update_of_ne (show b ≠ result by decide),
                      Function.update_of_ne (show b ≠ a by decide),
                      Function.update_of_ne (show b ≠ t by decide),
                      Function.update_of_ne (show b ≠ c by decide)]
                  · -- All remaining tapes: not a,b,c,t,pc,result → truly unchanged
                    -- Step through each layer of Function.update
                    simp only [Function.update_of_ne h_i_pc, Function.update_of_ne h_i_c,
                      Function.update_of_ne h_i_result, Function.update_of_ne h_i_t,
                      Function.update_of_ne h_i_b, Function.update_of_ne h_i_a]
                    -- Now both sides should reduce to tapes i through tapes₄, ₃, ₂, ₁
                    simp only [htapes₄_def, Function.update_of_ne h_i_result,
                      Function.update_of_ne h_i_pc]
                    simp only [htapes₃_def, Function.update_of_ne h_i_pc,
                      Function.update_of_ne h_i_b, Function.update_of_ne h_i_a]
                    simp only [htapes₂_def, Function.update_of_ne h_i_result,
                      Function.update_of_ne h_i_pc]
                    simp only [htapes₁_def, Function.update_of_ne h_i_pc,
                      Function.update_of_ne h_i_t, Function.update_of_ne h_i_b,
                      Function.update_of_ne h_i_a]
      -- Main inductive step for succ case
      -- iter_count_bound max (t_val+1) = 2 + max*(3 + 2*iter_count_bound max t_val)
      -- Structure: 1 step (funStart, t>0) + max*(3+2n) steps (loop) + 1 step (loopStart, c=max)
      have h_headD : dya_inv ((tapes t).headD []) = t_val.succ := by
        rw [List.headD_eq_head?]; exact h_t
      rw [h_headD]
      simp only [iter_count_bound]
      -- Step 1: funStart with t > 0 (t_val.succ ≠ 0)
      -- Since t ≠ 0, funStart pushes c=[], result=[], pc=l_loopStart
      have h_t_nonzero : (tapes t).head?.getD [] ≠ [] := by
        intro h_eq
        have : dya_inv ((tapes t).head?.getD []) = 0 := by rw [h_eq]; simp
        omega
      unfold edge_semantics at h_edge_semantics
      have h_funstart_eval : (innerLoop edge (dya max)).eval_list tapes =
          Part.some (Function.update (Function.update (Function.update tapes
            c ([] :: tapes c))
            result ([] :: tapes result))
            pc (l_loopStart :: (tapes pc).tail)) := by
        simp [innerLoop, h_pc_funStart, h_t_nonzero, h_edge_semantics]; grind
      have h_funstart := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
        h_edge_semantics _ _ h_funstart_eval
      -- After funStart: c=[]::tapes c, result=[]::tapes result, pc=l_loopStart::tail
      -- Decompose: f^[2 + max*(3+2n)] x = f (f^[max*(3+2n)] (f x))
      conv_lhs => rw [show 2 + max * (3 + 2 * iter_count_bound max t_val) =
        Nat.succ (max * (3 + 2 * iter_count_bound max t_val) + 1) from by omega]
      rw [Function.iterate_succ_apply']
      conv_lhs => arg 1; rw [Function.iterate_add_apply, Function.iterate_one]
      rw [h_funstart]
      -- Post-funStart state
      set tapes_post := Function.update (Function.update (Function.update tapes
        c ([] :: tapes c))
        result ([] :: tapes result))
        pc (l_loopStart :: (tapes pc).tail) with h_tapes_post
      -- Goal: innerLoopFun (innerLoopFun^[max*(3+2n)] tapes_post) = expected
      -- Loop invariant: after k iterations of h_inner, the tape state is predictable
      -- Each h_inner iteration takes (3 + 2*iter_count_bound max t_val) steps
      -- We need max such iterations, followed by one final step
      --
      -- Key steps:
      -- 1. max iterations of h_inner: c increments from dya(0) to dya(max-1),
      --    result accumulates path checks, t and pc preserved
      -- 2. Final innerLoopFun: inner_loop_start with c = dya(max) → pops c and result
      -- 3. The accumulated result matches RelatesInSteps r a b (2^(t_val+1))
      --    via relatesInStepsExp and h_finite (finiteness bounds the search space)
      --
      -- The loop invariant proof requires induction on max, tracking Function.update
      -- chains through each iteration. Each iteration uses h_inner to advance the state.
      -- The final step uses inner_loop_start with the c = max branch.
      -- The accumulated result equivalence uses relatesInStepsExp (sorry) and
      -- h_finite (finiteness) to connect the iterated check to RelatesInSteps.
      constructor
      · -- Main equality: the accumulated result of max h_inner iterations + final step
        -- Proof sketch:
        -- 1. By induction on k ≤ max, show that after k*(3+2n) steps from tapes_post:
        --    c = dya(k) :: tapes c, result = (accumulated_check k) :: tapes result,
        --    t = dya(t_val.succ) :: (tapes t).tail, pc = l_loopStart :: (tapes pc).tail
        --    where accumulated_check k = (∃ c_val with dya_inv < k,
        --      RelatesInSteps r a_val c_val (2^t_val) ∧ RelatesInSteps r c_val b_val (2^t_val))
        --      ∨ (tapes result).headD [] ≠ []
        -- 2. After max iterations (k=max), the final innerLoopFun uses inner_loop_start
        --    with c = dya(max), hitting the "c = max" branch that pops c and result.
        -- 3. The accumulated check for k=max is equivalent to
        --    RelatesInSteps r a_val b_val (2^(t_val+1)) via relatesInStepsExp and h_finite
        --    (finiteness bounds search to dya_inv values < max).
        -- 4. Combined with (tapes result).headD [] = [] (since result was pushed with []),
        --    the final result matches the target.
        sorry
      · -- PC length preservation during all iterations
        intro n' h_n'
        -- tapes pc is non-empty since head = l_funStart ≠ []
        have h_pc_ne : tapes pc ≠ [] := by intro h; simp [h] at h_pc_funStart
        -- n' = 0: trivial (identity)
        by_cases h0 : n' = 0
        · subst h0; simp
        · -- n' ≥ 1: factor out funStart step
          rw [show n' = (n' - 1) + 1 from by omega,
            Function.iterate_add_apply, Function.iterate_one, h_funstart]
          -- tapes_post pc = l_loopStart :: (tapes pc).tail, same length as tapes pc
          have h_post_pc : tapes_post pc = l_loopStart :: (tapes pc).tail := by
            simp [h_tapes_post, Function.update_self]
          have h_post_len : (tapes_post pc).length = (tapes pc).length := by
            rw [h_post_pc]
            rcases h_list : tapes pc with _ | ⟨_, tl⟩
            · exact absurd h_list h_pc_ne
            · simp
          -- Suffices to show preservation from tapes_post
          suffices h_suff : ((innerLoopFun max h_edge_semantics)^[n' - 1]
              tapes_post pc).length ≥ (tapes_post pc).length by omega
          -- Decompose n'-1 into k complete h_inner iterations + j remaining steps
          set step_size := 3 + 2 * iter_count_bound max t_val with h_step_size_def
          have h_step_pos : step_size > 0 := by omega
          have h_n1_bound : n' - 1 ≤ max * step_size := by omega
          -- Loop invariant: after k complete iterations, pc/c/t are preserved
          have h_loop_inv : ∀ ki ≤ max,
              ((innerLoopFun max h_edge_semantics)^[ki * step_size] tapes_post pc) =
                l_loopStart :: (tapes pc).tail ∧
              ((innerLoopFun max h_edge_semantics)^[ki * step_size]
                tapes_post c).head?.getD [] = dya ki ∧
              dya_inv (((innerLoopFun max h_edge_semantics)^[ki * step_size]
                tapes_post t).head?.getD []) = t_val.succ := by
            intro ki
            induction ki with
            | zero =>
              intro _
              simp only [Nat.zero_mul, Function.iterate_zero_apply]
              refine ⟨h_post_pc, ?_, ?_⟩
              · -- (tapes_post c).head?.getD [] = dya 0 = []
                have h_c_val : tapes_post c = [] :: tapes c := by
                  simp [h_tapes_post, Function.update_of_ne (show pc ≠ c from by decide),
                    Function.update_of_ne (show result ≠ c from by decide),
                    Function.update_self]
                simp [h_c_val]
              · -- dya_inv((tapes_post t).head?.getD []) = t_val.succ
                have h_t_val : tapes_post t = tapes t := by
                  simp [h_tapes_post, Function.update_of_ne (show pc ≠ t from by decide),
                    Function.update_of_ne (show result ≠ t from by decide),
                    Function.update_of_ne (show c ≠ t from by decide)]
                rw [h_t_val]; exact h_t
            | succ ki' ih_ki =>
              intro h_ki
              obtain ⟨h_pc_ki, h_c_ki, h_t_ki⟩ := ih_ki (by omega)
              rw [show (ki' + 1) * step_size = step_size + ki' * step_size from
                by simp [Nat.add_mul]; omega,
                Function.iterate_add_apply]
              -- Preconditions for h_inner on the intermediate state
              have h_s_pc : ((innerLoopFun max h_edge_semantics)^[ki' * step_size]
                  tapes_post pc).head?.getD [] = l_loopStart := by
                rw [h_pc_ki]; simp
              have h_s_c : ((innerLoopFun max h_edge_semantics)^[ki' * step_size]
                  tapes_post c).head?.getD [] ≠ dya max := by
                rw [h_c_ki]; intro h_eq
                have := congr_arg dya_inv h_eq
                simp [dya_inv_dya] at this; omega
              -- Apply h_inner
              have h_step := h_inner ((innerLoopFun max h_edge_semantics)^[ki' * step_size]
                tapes_post) h_s_pc h_s_c h_t_ki
              -- Prove each component using congr_fun + Function.update unfolding
              refine ⟨?_, ?_, ?_⟩
              · -- pc = l_loopStart :: (tapes pc).tail
                have := congr_fun h_step pc
                simp [Function.update, show result ≠ pc from by decide,
                  show pc = pc from rfl] at this
                rw [this, h_pc_ki]; simp
              · -- c head = dya (ki' + 1)
                have := congr_fun h_step c
                simp [Function.update, show result ≠ c from by decide,
                  show pc ≠ c from by decide, show t ≠ c from by decide,
                  show c = c from rfl] at this
                rw [this]; simp only [List.head?_cons, Option.getD_some]
                simp only [dya_succ, List.headD_eq_head?, h_c_ki, dya_inv_dya]
              · -- t: dya_inv(head) = t_val.succ
                have := congr_fun h_step t
                simp [Function.update, show result ≠ t from by decide,
                  show pc ≠ t from by decide, show t = t from rfl] at this
                rw [this]; simp [List.head?_cons, Option.getD_some, dya_inv_dya]
          -- Within one h_inner iteration, PC length ≥ input at all intermediate steps
          have h_inner_pc : ∀ (s : Fin tapeCount → List (List OneTwo)),
              (s pc).head?.getD [] = l_loopStart →
              (s c).head?.getD [] ≠ dya max →
              dya_inv ((s t).head?.getD []) = t_val.succ →
              ∀ ji ≤ step_size,
                ((innerLoopFun max h_edge_semantics)^[ji] s pc).length ≥ (s pc).length := by
            intro s h_s_pc h_s_c h_s_t ji h_ji
            set n := iter_count_bound max t_val with hn_def
            have h_s_pc_ne : s pc ≠ [] := by intro h; simp [h] at h_s_pc
            have h_s_pc_tail_len : (s pc).tail.length + 1 = (s pc).length := by
              rcases s pc with _ | ⟨_, _⟩ <;> simp_all
            -- Step 1: inner_loop_start (c ≠ max)
            have h_step1_eval := @inner_loop_start max edge s h_s_pc
            simp only [if_neg h_s_c] at h_step1_eval
            have h_step1 := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
              h_edge_semantics _ _ h_step1_eval
            by_cases h0 : ji = 0
            · subst h0; simp
            · -- ji ≥ 1: factor out Step 1
              rw [show ji = (ji - 1) + 1 from by omega,
                Function.iterate_add_apply, Function.iterate_one, h_step1]
              set s₁ := Function.update (Function.update (Function.update
                (Function.update s
                a ((s a).head?.getD [] :: s a))
                b ((s c).head?.getD [] :: s b))
                t (dya (dya_inv ((s t).head?.getD []) - 1) :: (s t).tail))
                pc (l_funStart :: l_afterFirstRec :: (s pc).tail) with hs₁
              have h_s1_pc_val : s₁ pc = l_funStart :: l_afterFirstRec :: (s pc).tail := by
                simp [hs₁, Function.update_self]
              have h_s1_pc_head : (s₁ pc).head?.getD [] = l_funStart := by
                rw [h_s1_pc_val]; simp
              have h_s1_pc_len : (s₁ pc).length = (s pc).length + 1 := by
                rw [h_s1_pc_val]; simp; omega
              have h_s1_t_val : dya_inv ((s₁ t).head?.getD []) = t_val := by
                simp [hs₁, Function.update_self, dya_inv_dya]; omega
              obtain ⟨h_ih₁_main, h_ih₁_pc⟩ := ih s₁ h_s1_pc_head h_s1_t_val
              have h_n_eq₁ : iter_count_bound max (dya_inv ((s₁ t).headD [])) = n := by
                rw [List.headD_eq_head?, h_s1_t_val]
              rw [h_n_eq₁] at h_ih₁_main h_ih₁_pc
              -- During IH₁: ji-1 < n
              by_cases hlt₁ : ji - 1 < n
              · have := h_ih₁_pc (ji - 1) hlt₁; omega
              · -- After IH₁
                rw [show ji - 1 = (ji - 1 - n) + n from by omega,
                  Function.iterate_add_apply]
                set s₂ := (innerLoopFun max h_edge_semantics)^[n] s₁ with hs₂_def
                have hs₂_eq := hs₂_def.trans h_ih₁_main
                have h_s2_pc_val : s₂ pc = l_afterFirstRec :: (s pc).tail := by
                  rw [hs₂_eq]
                  simp [Function.update_self, h_s1_pc_val]
                have h_s2_pc_len : (s₂ pc).length = (s pc).length := by
                  rw [h_s2_pc_val]; simp; omega
                -- ji-1-n = 0: IH₁ just completed
                by_cases h2 : ji - 1 - n = 0
                · rw [h2]; simp; omega
                · -- Step 3: after_first_rec
                  have h_s2_pc_head : (s₂ pc).head?.getD [] = l_afterFirstRec := by
                    rw [h_s2_pc_val]; simp
                  have h_step3_eval :=
                    @inner_loop_after_first_rec max edge s₂ h_s2_pc_head
                  have h_step3 := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
                    h_edge_semantics _ _ h_step3_eval
                  rw [show ji - 1 - n = (ji - 1 - n - 1) + 1 from by omega,
                    Function.iterate_add_apply, Function.iterate_one]
                  set s₃ := innerLoopFun max h_edge_semantics s₂ with hs₃_def
                  have hs₃_eq := hs₃_def.trans h_step3
                  have h_s3_pc_val :
                      s₃ pc = l_funStart :: l_afterSecondRec :: (s pc).tail := by
                    rw [hs₃_eq]; simp [Function.update_self, h_s2_pc_val]
                  have h_s3_pc_head : (s₃ pc).head?.getD [] = l_funStart := by
                    rw [h_s3_pc_val]; simp
                  have h_s3_pc_len : (s₃ pc).length = (s pc).length + 1 := by
                    rw [h_s3_pc_val]; simp; omega
                  have h_s3_t_val :
                      dya_inv ((s₃ t).head?.getD []) = t_val := by
                    have h_s3_t_eq : s₃ t = s₁ t := by
                      rw [hs₃_eq]; simp
                      rw [hs₂_eq]; simp
                    rw [h_s3_t_eq]; exact h_s1_t_val
                  obtain ⟨h_ih₂_main, h_ih₂_pc⟩ := ih s₃ h_s3_pc_head h_s3_t_val
                  have h_n_eq₂ :
                      iter_count_bound max (dya_inv ((s₃ t).headD [])) = n := by
                    rw [List.headD_eq_head?, h_s3_t_val]
                  rw [h_n_eq₂] at h_ih₂_main h_ih₂_pc
                  -- During IH₂: ji-1-n-1 < n
                  by_cases hlt₂ : ji - 1 - n - 1 < n
                  · have := h_ih₂_pc (ji - 1 - n - 1) hlt₂; omega
                  · -- After IH₂
                    rw [show ji - 1 - n - 1 = (ji - 1 - n - 1 - n) + n from by omega,
                      Function.iterate_add_apply]
                    set s₄ := (innerLoopFun max h_edge_semantics)^[n] s₃ with hs₄_def
                    have hs₄_eq := hs₄_def.trans h_ih₂_main
                    have h_s4_pc_val : s₄ pc = l_afterSecondRec :: (s pc).tail := by
                      rw [hs₄_eq]
                      simp [Function.update_self, h_s3_pc_val]
                    have h_s4_pc_len : (s₄ pc).length = (s pc).length := by
                      rw [h_s4_pc_val]; simp; omega
                    -- ji-1-n-1-n = 0: IH₂ just completed
                    by_cases h4 : ji - 1 - n - 1 - n = 0
                    · rw [h4]; simp; omega
                    · -- Step 5: after_second_rec (ji-1-n-1-n = 1)
                      have h5 : ji - 1 - n - 1 - n = 1 := by omega
                      rw [h5, Function.iterate_one]
                      have h_s4_pc_head :
                          (s₄ pc).head?.getD [] = l_afterSecondRec := by
                        rw [h_s4_pc_val]; simp
                      have h_step5_eval :=
                        @inner_loop_after_second_rec max edge s₄ h_s4_pc_head
                      have h_step5 := @innerLoopFun_eq_of_eval_list r h_r_dec max edge
                        h_edge_semantics _ _ h_step5_eval
                      rw [h_step5]; simp [h_s4_pc_val]; omega
          -- Combine h_loop_inv and h_inner_pc to prove overall preservation
          -- Decompose (n'-1) = ji + ki * step_size using Euclidean division
          have h_div_mod := Nat.div_add_mod (n' - 1) step_size
          have h_ji_lt : (n' - 1) % step_size < step_size := Nat.mod_lt _ h_step_pos
          have h_ki_mul_le : (n' - 1) / step_size * step_size ≤ n' - 1 :=
            Nat.div_mul_le_self _ _
          have h_sum : n' - 1 = (n' - 1) % step_size + (n' - 1) / step_size * step_size := by
            have h := Nat.div_add_mod (n' - 1) step_size
            -- h : step_size * ((n' - 1) / step_size) + (n' - 1) % step_size = n' - 1
            have h2 : step_size * ((n' - 1) / step_size) = (n' - 1) / step_size * step_size :=
              Nat.mul_comm _ _
            omega
          have h_ki_bound : (n' - 1) / step_size ≤ max := by
            have h1 : (n' - 1) / step_size ≤ (max * step_size) / step_size :=
              Nat.div_le_div_right h_n1_bound
            have h2 : max * step_size / step_size = max :=
              Nat.mul_div_cancel max h_step_pos
            omega
          rw [h_sum, Function.iterate_add_apply]
          obtain ⟨h_sk_pc, h_sk_c, h_sk_t⟩ := h_loop_inv _ h_ki_bound
          have h_sk_len : ((innerLoopFun max h_edge_semantics)^[
              (n' - 1) / step_size * step_size] tapes_post pc).length =
              (tapes_post pc).length := by
            rw [h_sk_pc, h_post_pc]
          by_cases hk_max : (n' - 1) / step_size = max
          · -- ki = max: ji must be 0 since n'-1 ≤ max*step_size
            have hj0 : (n' - 1) % step_size = 0 := by
              have h1 : max * step_size ≤ n' - 1 := by
                rw [← hk_max]; exact h_ki_mul_le
              have h3 : n' - 1 = max * step_size := Nat.le_antisymm h_n1_bound h1
              rw [h3, show max * step_size = step_size * max from Nat.mul_comm _ _,
                Nat.mul_mod_right]
            rw [hj0]; simp; omega
          · -- ki < max: apply h_inner_pc to the state after ki iterations
            have hk_lt : (n' - 1) / step_size < max := by omega
            have h_pc_cond : ((innerLoopFun max h_edge_semantics)^[
                (n' - 1) / step_size * step_size] tapes_post pc).head?.getD [] =
                l_loopStart := by
              rw [h_sk_pc]; simp
            have h_c_cond : ((innerLoopFun max h_edge_semantics)^[
                (n' - 1) / step_size * step_size] tapes_post c).head?.getD [] ≠ dya max := by
              rw [h_sk_c]; intro h_eq
              have := congr_arg dya_inv h_eq
              simp [dya_inv_dya] at this; omega
            have h_res := h_inner_pc _ h_pc_cond h_c_cond h_sk_t
              ((n' - 1) % step_size) h_ji_lt.le
            omega


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
