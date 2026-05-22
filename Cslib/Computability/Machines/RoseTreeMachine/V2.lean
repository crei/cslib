/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Part
public import Mathlib.Control.Fix
public import Std

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.Nat.Bits

/-!
-- This is a proposal to define a machine model and related time and space measure
-- such that it is linearly space- and polynomially time-related to multi-tape Turing machines.

-- The goal would be that the machine model is flexible enough to implement algorithms easily,
-- but still close enough to Turing machines to allow defining logspace and even loglogspace.

-- The machine as defined below will allow stateless / pure functional programs.
-- If we store the input tape position as a number, we should be able to define logspace.
-- In order to go down to loglogspace, we need to use the input tape head as a "pointer"
-- and cannot count its position. This could be doable as well, but requires a more stateful
-- model at least for the input tape. The input tape is currently not modeled, but I have some
-- plans to define actions on the input tape as further elementary operations.

-- The main insight over my current work is that it does not hurt to
-- (1) create a new tape for every elementary operation (the program size is constant, so the number
--     of tapes is constant)
-- (2) disallow modifications to existing tapes (work tape space has been spent, it is fine
--     to copy it finitely often
-- (3) if we have a built-in `fold` operation, we should be able to implement the required
--     operations at linear space overhead, because the fold operation implicitly re-uses the
--     space used by the accumulator.
-/

@[expose] public section


namespace Turing

namespace RoseTreeMachine

-- ================= Data structure



-- Rose-tree data structure, it allows us to
-- 1. map most of Lean's data structures in a "natural" manner
-- 2. define a "fold" operation
inductive Data where
  | l : List Data → Data
deriving Repr

mutual
  def Data.decEq : ∀ (a b : Data), Decidable (a = b)
    | .l xs, .l ys =>
      match Data.listDecEq xs ys with
      | isTrue h => isTrue (congrArg Data.l h)
      | isFalse h => isFalse fun heq => h (Data.l.inj heq)
  def Data.listDecEq : ∀ (xs ys : List Data), Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by simp)
    | _ :: _, [] => isFalse (by simp)
    | x :: xs, y :: ys =>
      match Data.decEq x y, Data.listDecEq xs ys with
      | isTrue hxy, isTrue hxys => isTrue (congrArg₂ List.cons hxy hxys)
      | isFalse hxy, _ => isFalse fun h => hxy (List.cons.inj h).1
      | _, isFalse hxys => isFalse fun h => hxys (List.cons.inj h).2
end

instance : DecidableEq Data := Data.decEq
instance : BEq Data := inferInstance
instance : LawfulBEq Data := inferInstance

abbrev Data.empty := Data.l []


@[grind =]
def Data.asList
  | Data.l xs => xs

@[simp]
lemma Data.asList_empty : Data.empty.asList = [] := by rfl

@[simp, grind =]
lemma Data.asList_l (d : Data) : Data.l d.asList = d := by simp [Data.asList]; grind

@[simp, grind =]
lemma Data.l_asList (xs : List Data) : (Data.l xs).asList = xs := by simp [Data.asList]

--- Encoding length of d.
def Data.size : Data → ℕ
  | Data.l xs => 2 + (xs.map Data.size |>.sum)

@[simp, grind =]
lemma Data.size_empty : Data.empty.size = 2 := by simp [Data.empty, Data.size]

@[simp, grind =]
lemma Data.cons_size {h : Data} {t : List Data} :
    (Data.l (h :: t)).size = h.size + (Data.l t).size := by
  simp [Data.size]
  grind

/-- Recursion principle for `Data` that exposes the list-of-children structure:
    a `motive` is built from the empty case and a cons case that combines the
    motive on the head child and on the tail list (viewed as a `Data`).
    Lean's auto-generated `Data.rec` for the nested inductive only iterates once
    through `List.rec`, leaving the recursive call on children to the user;
    `Data.recL` performs both recursions and is the natural elimination principle
    for definitions/proofs that need both IHs. -/
@[elab_as_elim]
def Data.recL {motive : Data → Sort*}
    (nil : motive (Data.l []))
    (cons : ∀ (x : Data) (xs : List Data),
      motive x → motive (Data.l xs) → motive (Data.l (x :: xs))) :
    ∀ d, motive d
  | .l [] => nil
  | .l (x :: xs) =>
      cons x xs (Data.recL nil cons x) (Data.recL nil cons (.l xs))

/-- Induction principle for `Data`, the `Prop`-valued companion to `Data.recL`. -/
@[elab_as_elim]
theorem Data.inductionL {motive : Data → Prop}
    (nil : motive (Data.l []))
    (cons : ∀ (x : Data) (xs : List Data),
      motive x → motive (Data.l xs) → motive (Data.l (x :: xs)))
    (d : Data) : motive d :=
  Data.recL nil cons d

abbrev TapeIndex := ℕ


-- ================= Operations and programs

-- The machine is a "stack" machine, where each stack item represents a tape and holds a Data value.
-- Each operation creates a new stack entry (a new tape) and can read from previous
-- entries by index. Stack entries created in "inner" programs are temporary and deleted
-- once the inner program terminates. This is especially relevant for space complexity of
-- loops since it allows us to re-use the space of one iteration for the next iteration.

def Var := ℕ
deriving Repr

/-- Abstract syntax tree. Binders (`letin`, `elim`'s cons branch, `fold`'s body, `while_`'s body)
are *implicit*: each binder extends `env` with one or more fresh values, and the bound
variable(s) are referred to as `var k` where `k = env.length` at the binding site.
For ergonomic construction with named binders use `PB` below. -/
inductive Prog where
  | var (id : Var)
  /-- `letin val rest`: evaluate `val`, append the result to `env`, then evaluate `rest`. -/
  | letin (val : Prog) (rest : Prog)
  | empty
  | cons (h t : Prog)
  /-- `elim v em cs`: if `v` evaluates to `empty`, run `em`; otherwise destructure into
      `head` and `tail` (both appended to `env`, in that order) and run `cs`. -/
  | elim (v : Prog) (em : Prog) (cs : Prog)
  | eq (a b : Prog)
  /-- `fold body init list`: `init` and `list` produce starting accumulator and the input
      list; `body` runs once per element with `env` extended by `[acc, x]`. -/
  | fold (body : Prog) (init list : Prog)
  /-- `while_ body`: body runs with `env` extended by the current accumulator. -/
  | while_ (body : Prog)
deriving Repr

/-- Evaluates `p` on `env` and returns the result, the time and the space consumption. -/
def Prog.meteredEval (env : List Data) (p : Prog) : Part (Data × ℕ × ℕ) :=
  match p with
    -- TODO charge for copy?
  | .var id => .some (env[(show ℕ from id)]?.getD (Data.l []), 1, 1)
  | .letin val rest => do
    let (v, t, s) ← val.meteredEval env
    let (r, t', s') ← rest.meteredEval (env ++ [v])
    -- TODO charge for copy?
    return (r, 1 + t + t', max s s')
  | .empty => .some (Data.empty, 1, 1)
  | .cons h t => do
    let (head, h_t, h_s) ← h.meteredEval env
    let (tail, t_t, t_s) ← t.meteredEval env
    return (Data.l (head :: tail.asList), 1 + h_t + t_t, max h_s t_s)
  | .elim v em cs => do
    let (v', t, s) ← v.meteredEval env
    match v' with
    | Data.l [] =>
      let (r, t', s') ← em.meteredEval env
      return (r, 1 + t + t', max s s')
    | Data.l (head :: tail) =>
      let (r, t', s') ← cs.meteredEval (env ++ [head, Data.l tail])
      return (r, 1 + t + t', max s s')
  | .eq a b => do
    let (a, a_t, a_s) ← a.meteredEval env
    let (b, b_t, b_s) ← b.meteredEval env
    (if a == b then Data.l [ Data.l [] ] else Data.l [], 1 + a_t + b_t, 1 + max a_s b_s)
  | .fold body init list => do
    let (i, i_t, i_s) ← init.meteredEval env
    let (l, l_t, l_s) ← list.meteredEval env
    l.asList.foldlM
      (fun (acc, t, s) el => do
        let (acc', b_t, b_s) ← body.meteredEval (env ++ [acc, el])
        return (acc', 1 + t + b_t, max s b_s))
      (i, 1 + i_t + l_t, max i_s l_s)
  | .while_ body =>
    -- `body` is evaluated repeatedly with `env` extended by the current accumulator.
    -- The result of `body` is expected to be a cons whose head is the "continue?" flag
    -- (truthy = nonempty) and whose tail is the next accumulator.
    -- The initial accumulator is `Data.empty`.
    let F : ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) →
            (Data × ℕ × ℕ) → Part (Data × ℕ × ℕ) :=
      fun rec d_ts =>
        let (acc, t, s) := d_ts
        (body.meteredEval (env ++ [acc])).bind fun (r, b_t, b_s) =>
          let t' := t + 1 + b_t
          let s' := max s b_s
          if r.asList.headD (Data.l []) != Data.l [] then
            rec (r, t', s')
          else
            .some (r, t', s')
    Part.fix F (Data.empty, 1, 1)
  termination_by (sizeOf p, 0)

------------------------------------
--- We are just handling the semantics for now.
--- Later on, it would probably make sense to define a variation of meteredEval
--- that uses O-classes for the space and time, so we can use equality-transformations
--- instead of inequalities in the semantics proofs.
-------------------------------------------

def Prog.eval (p : Prog) (env : List Data) : Part Data := (p.meteredEval env).map Prod.fst

def Prog.computes (impl : Prog) (f : List Data → Data) : Prop :=
  ∀ env, impl.eval env = .some (f env)

@[simp]
lemma Prog.var_computes {i : ℕ} :
  (Prog.var i).computes (fun env => env[i]?.getD (Data.l [])) := by
  simp [Prog.computes, Prog.eval, Prog.meteredEval]

@[simp]
lemma Prog.empty_computes :
  Prog.empty.computes (fun _ => Data.l []) := by
  simp [Prog.computes, Prog.eval, Prog.meteredEval]

@[simp]
lemma Prog.cons_computes {h t : Prog} {fh ft : List Data → Data}
    (hh : h.computes fh) (ht : t.computes ft) :
    (Prog.cons h t).computes (fun env => Data.l (fh env :: (ft env).asList)) := by
  sorry

/-- Pointwise (single-env) version of `Prog.cons_computes`. -/
lemma Prog.cons_eval {h t : Prog} {env : List Data} {dh dt : Data}
    (hh : h.eval env = .some dh) (ht : t.eval env = .some dt) :
    (Prog.cons h t).eval env = .some (Data.l (dh :: dt.asList)) := by
  sorry

/-- Pointwise (single-env) version for `elim`. -/
lemma Prog.elim_eval {v em cs : Prog} {env : List Data} {dv : Data}
    (hv : v.eval env = .some dv) :
    (Prog.elim v em cs).eval env =
      match dv.asList with
      | [] => em.eval env
      | head :: tail => cs.eval (env ++ [head, Data.l tail]) := by
  sorry

def Prog.Total (p : Prog) : Prop := ∀ env, (p.meteredEval env).Dom

@[simp]
def Prog.WhileFree (p : Prog) : Prop :=
  match p with
  | .var _ => True
  | .letin val rest => Prog.WhileFree val ∧ Prog.WhileFree rest
  | .empty => True
  | .cons h t => Prog.WhileFree h ∧ Prog.WhileFree t
  | .elim v em cs => Prog.WhileFree v ∧ Prog.WhileFree em ∧ Prog.WhileFree cs
  | .eq a b => Prog.WhileFree a ∧ Prog.WhileFree b
  | .fold body init list => Prog.WhileFree body ∧ Prog.WhileFree init ∧ Prog.WhileFree list
  | .while_ _ => False

theorem total_of_whileFree (p : Prog) (h_wf : p.WhileFree) : p.Total := by sorry

/-- Evaluation of while-free programs. Do not expand this, because `Part` is cumbersome to
deal with. -/
def Prog.meteredEvalT (p : Prog) (h_wf : p.WhileFree) (env : List Data) : Data × ℕ × ℕ :=
  (p.meteredEval env).get (total_of_whileFree p h_wf env)

/-! ## Surface syntax with named binders

Define convenience builder functions to allow binding the variables to names.

 -/

/-- A program builder: given the current binder depth (i.e. the size of `env`
at the point of insertion), produce a `Prog`. -/
abbrev PB := ℕ → Prog

namespace PB

def empty : PB := fun _ => .empty
def cons (h t : PB) : PB := fun n => .cons (h n) (t n)
def eq (a b : PB) : PB := fun n => .eq (a n) (b n)

/-- `letIn val (fun x => body)`: bind the value of `val` as a fresh variable `x`
visible in `body`. -/
def letIn (val : PB) (body : PB → PB) : PB := fun n =>
  .letin (val n) (body (fun _ => .var n) (n + 1))

/-- `elim v em (fun head tail => body)`: case-analyse the result of `v`. -/
def elim (v : PB) (em : PB) (cs : PB → PB → PB) : PB := fun n =>
  .elim (v n) (em n) (cs (fun _ => .var n) (fun _ => .var (n + 1)) (n + 2))

/-- `fold (fun acc x => body) init list`: run `body` for each element `x`
threading accumulator `acc`. -/
def fold (body : PB → PB → PB) (init list : PB) : PB := fun n =>
  .fold (body (fun _ => .var n) (fun _ => .var (n + 1)) (n + 2)) (init n) (list n)

/-- `while_ (fun acc => body)`. -/
def while_ (body : PB → PB) : PB := fun n =>
  .while_ (body (fun _ => .var n) (n + 1))

/-- Close a builder into a concrete `Prog`. -/
def build (p : PB) : Prog := p 0


end PB

-------------------------------------
--- Encoding of generic types into Data
--------------------------------------

class DataEncode (α : Type) where
  encode : α → Data
  h_inj : encode.Injective

instance : DataEncode Bool where
  encode b := if b then Data.l [ Data.l [] ] else Data.l []
  h_inj := by intros a b h_eq; grind

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  h_inj := by sorry

@[simp, grind =]
lemma DataEncode_list_nil {α : Type} [DataEncode α] :
  DataEncode.encode ([] : List α) = Data.l [] := by
  simp [DataEncode.encode]

@[simp, grind =]
lemma DataEncode_list_eq_nil_iff_nil {α : Type} [DataEncode α] (xs : List α) :
  DataEncode.encode xs = Data.empty ↔ xs = [] := by
  simp [DataEncode.encode]

@[simp, scoped grind =]
lemma DataEncode_list_tail {α : Type} [DataEncode α] (xs : List α) :
  (DataEncode.encode xs).asList.tail = (DataEncode.encode xs.tail).asList := by
  simp [DataEncode.encode]

instance (α : Type) [DataEncode α] : DataEncode (Option α) where
  encode := fun
    | none => Data.l []
    | some x => Data.l [DataEncode.encode x]
  h_inj := by sorry

@[simp]
lemma DataEncode_Option_empty {α : Type} [DataEncode α] (x : Option α) :
  (DataEncode.encode x == Data.empty) = x.isNone := by
  cases x <;> simp [DataEncode.encode, Data.empty]

instance (α β : Type) [DataEncode α] [DataEncode β] : DataEncode (α × β) where
  encode := fun (a, b) => Data.l [DataEncode.encode a, DataEncode.encode b]
  h_inj := by sorry

lemma DataEncode_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
  DataEncode.encode (a, b) = Data.l [DataEncode.encode a, DataEncode.encode b] := by
  simp [DataEncode.encode]

instance : DataEncode ℕ where
  encode x := DataEncode.encode (Nat.bits x)
  h_inj := by sorry

----------------------------------------------------

def PB.computes (impl : PB) (f : List Data → Data) : Prop :=
  ∀ env, (impl env.length).eval env = .some (f env)

-------------------------------------------------------
--- combinator semantics
----------------------------------------------------

@[simp]
lemma meteredEvalT_var_val {env : List Data} {i : ℕ} :
  ((Prog.var i).meteredEvalT (by simp) env).1 = env[i]?.getD (Data.l []) := by
  simp [Prog.meteredEvalT, Prog.meteredEval]

@[simp]
lemma meteredEvalT_empty_val {env : List Data} :
  ((Prog.empty).meteredEvalT (by simp) env).1 = Data.l [] := by
  simp [Prog.meteredEvalT, Prog.meteredEval]

lemma meteredEvalT_elim_val {env : List Data} {v em cs : Prog}
    {h_wf : (Prog.elim v em cs).WhileFree} :
  ((Prog.elim v em cs).meteredEvalT h_wf env).1 =
    match ((v.meteredEvalT h_wf.1 env).1) with
    | Data.l [] => ((em.meteredEvalT h_wf.2.1 env).1)
    | Data.l (head :: tail) => ((cs.meteredEvalT h_wf.2.2 (env ++ [head, Data.l tail])).1) := by
  sorry
-------------------------------------------------------------------
--- tools
-------------------------------------------

lemma list_getElem_length_add {α : Type} (xs ys : List α) (i : ℕ) (h_lt : i < ys.length) :
  (xs ++ ys)[xs.length + i]'(by grind) = ys[i] := by
  sorry

/-- Example: `tail x` returns the tail of the list bound at variable `x`, or `empty`
    if `x` denotes the empty list. Built with `elim`: the empty branch yields `empty`,
    the cons branch ignores the head and projects the bound tail. -/
def PB.tail (x : PB) : PB := PB.elim x PB.empty (fun _head tl => tl)
def PB.head (x : PB) : PB := PB.elim x PB.empty (fun hd _tl => hd)

/-! ### Compositional `computes` rules for `PB` combinators

The pattern: each combinator takes its `PB` arguments **paired with their `computes`
specs**, and yields a `computes` for the composite. -/

@[simp] lemma PB.empty_computes : PB.empty.computes (fun _ => Data.l []) := by
  intro env
  simp [PB.empty, Prog.eval, Prog.meteredEval]

/-- The "bound-variable look-up" PB: at binder depth `n` it produces `var (n + offset)`. -/
def PB.bound (offset : ℕ) : PB := fun n => Prog.var (n + offset)

lemma PB.bound_computes (offset : ℕ) :
    (PB.bound offset).computes (fun env => env[env.length + offset]?.getD (Data.l [])) := by
  simp [PB.bound, PB.computes, Prog.eval, Prog.meteredEval]

lemma PB.cons_computes {h t : PB} {fh ft : List Data → Data}
    (hh : h.computes fh) (ht : t.computes ft) :
    (PB.cons h t).computes (fun env => Data.l (fh env :: (ft env).asList)) := by
  intro env
  simp only [PB.cons]
  exact Prog.cons_eval (hh env) (ht env)

/-- Inside an `elim cs` branch, the two PBs passed to `cs` are constant closures
returning `.var n` and `.var (n+1)`, where `n = env.length` at the outer call site.
The body is then evaluated under env extended with `[head, Data.l tail]`.

The spec for `cs` must therefore be parametric in the slot `n`: assume that for
every `slot`, the body built with the two constant lookups computes a function
expressed in terms of those two slot positions. -/
lemma PB.elim_computes {v em : PB} {cs : PB → PB → PB}
    {fv fem : List Data → Data}
    {fcs : List Data → Data → Data → Data}
    (hv : v.computes fv) (hem : em.computes fem)
    (hcs : ∀ slot : ℕ,
      (cs (fun _ => .var slot) (fun _ => .var (slot + 1))).computes
        (fun env' => fcs (env'.take slot)
                         (env'[slot]?.getD (Data.l []))
                         (env'[slot + 1]?.getD (Data.l [])))) :
    (PB.elim v em cs).computes (fun env =>
      match (fv env).asList with
      | [] => fem env
      | head :: tail => fcs env head (Data.l tail)) := by
  intro env
  simp only [PB.elim]
  -- Apply pointwise elim eval with hv env.
  rw [Prog.elim_eval (hv env)]
  -- Case split on (fv env).asList.
  match h_fv : (fv env).asList with
  | [] =>
    simp only
    exact hem env
  | head :: tail =>
    simp only
    -- The cs body, instantiated at slot = env.length, computes the right function;
    -- specialise its `computes` hypothesis to env' = env ++ [head, Data.l tail].
    have hcs_inst := hcs env.length (env ++ [head, Data.l tail])
    -- Beta-reduce the spec function on the extended env.
    simp only at hcs_inst
    -- The depth at the body's call site is (env ++ [head, Data.l tail]).length = env.length + 2.
    have hlen : (env ++ [head, Data.l tail]).length = env.length + 2 := by simp
    rw [hlen] at hcs_inst
    have h_take : (env ++ [head, Data.l tail]).take env.length = env := by
      simp
    have h_get0 : (env ++ [head, Data.l tail])[env.length]? = some head := by
      simp [List.getElem?_append_right]
    have h_get1 : (env ++ [head, Data.l tail])[env.length + 1]? = some (Data.l tail) := by
      simp [List.getElem?_append_right]
    rw [h_take, h_get0, h_get1] at hcs_inst
    simp only [Option.getD_some] at hcs_inst
    exact hcs_inst

lemma PB.elim_computes' {v em : PB} {cs : PB → PB → PB}
    {fv fem : List Data → Data}
    {fcs : Data → Data → List Data → Data}
    (hv : v.computes fv) (hem : em.computes fem)
    (hcs : ∀ slot : ℕ,
      (cs (fun _ => .var slot) (fun _ => .var (slot + 1))).computes
        (fun env' => fcs (env'[slot]?.getD (Data.l []))
                         (env'[slot + 1]?.getD (Data.l []))
                         (env'.take slot))) :
    (PB.elim v em cs).computes (fun env =>
      match (fv env).asList with
      | [] => fem env
      | head :: tail => fcs head (Data.l tail) env) := by
  sorry

/-- `PB.tail` computes the tail-of-list function applied to the spec of its argument.
This is the direct combinator-level spec, obtainable from `PB.elim_computes` with
`em := PB.empty` and `cs head tl := tl`. -/
lemma PB.tail_computes {x : PB} {fx : List Data → Data} (hx : x.computes fx) :
    (PB.tail x).computes (fun env => Data.l (fx env).asList.tail) := by
  unfold PB.tail
  have h := PB.elim_computes (cs := fun _head tl => tl)
    (fv := fx) (fem := fun _ => Data.l [])
    (fcs := fun _env _head tl => tl)
    hx PB.empty_computes
    (by
      intro slot env'
      simp [Prog.eval, Prog.meteredEval]
      rfl)
  intro env
  have he := h env
  simp only at he
  show _ = Part.some (Data.l (fx env).asList.tail)
  suffices h_eq :
      (match (fx env).asList with
       | [] => Data.l []
       | _head :: tail => Data.l tail) = Data.l (fx env).asList.tail by
    rw [← h_eq]; exact he
  rcases (fx env).asList with _ | ⟨head, tail⟩
  · rfl
  · rfl

/-- Same for `PB.head`. -/
lemma PB.head_computes {x : PB} {fx : List Data → Data} (hx : x.computes fx) :
    (PB.head x).computes (fun env => (fx env).asList.headD (Data.l [])) := by
  sorry

lemma PB.letIn_computes {val : PB} {body : PB → PB}
    {fv : List Data → Data} {fb : List Data → Data → Data}
    (hv : val.computes fv)
    (hb : (body (PB.bound 0)).computes
            (fun env => fb env.dropLast ((env.getLast?).getD (Data.l [])))) :
    (PB.letIn val body).computes (fun env => fb env (fv env)) := by
  sorry

/-! ## Alternative reasoning layers

The `PB.computes` framework above is awkward because the universal quantification
over `env` is coupled to the depth `env.length` at which the PB is unfolded.
Below are two lighter-weight alternatives. -/

/-! ### Option A: pointwise `Prog`-level `simp` set

Lifting eval rules to `@[simp]` lemmas lets you discharge most goals of the form
`p.eval env = .some d` by `simp` plus at most one `rcases` on a list. -/

@[simp] lemma Prog.var_eval {env : List Data} {i : ℕ} :
    (Prog.var i).eval env = .some (env[i]?.getD (Data.l [])) := by
  sorry

@[simp] lemma Prog.empty_eval {env : List Data} :
    Prog.empty.eval env = .some (Data.l []) := by
  sorry

@[simp] lemma Prog.cons_eval_simp {env : List Data} {h t : Prog} {dh dt : Data}
    (hh : h.eval env = .some dh) (ht : t.eval env = .some dt) :
    (Prog.cons h t).eval env = .some (Data.l (dh :: dt.asList)) := by
  sorry

@[simp] lemma Prog.elim_eval_nil {env : List Data} {v em cs : Prog}
    (hv : v.eval env = .some (Data.l [])) :
    (Prog.elim v em cs).eval env = em.eval env := by
  sorry

@[simp] lemma Prog.elim_eval_cons {env : List Data} {v em cs : Prog}
    {head : Data} {tail : List Data}
    (hv : v.eval env = .some (Data.l (head :: tail))) :
    (Prog.elim v em cs).eval env = cs.eval (env ++ [head, Data.l tail]) := by
  sorry

@[simp] lemma Prog.letin_eval {env : List Data} {val rest : Prog} {dv : Data}
    (hv : val.eval env = .some dv) :
    (Prog.letin val rest).eval env = rest.eval (env ++ [dv]) := by
  sorry

@[simp] lemma Prog.eq_eval {env : List Data} {a b : Prog} {da db : Data}
    (ha : a.eval env = .some da) (hb : b.eval env = .some db) :
    (Prog.eq a b).eval env =
      .some (if da = db then Data.l [Data.l []] else Data.l []) := by
  sorry

/-- Example: with the `simp` set above, the `tail` spec on a concrete env is short. -/
example {env : List Data} {x : Prog} {dx : Data} (hx : x.eval env = .some dx) :
    (Prog.elim x Prog.empty (Prog.var (env.length + 1))).eval env =
      .some (Data.l dx.asList.tail) := by
  rcases h : dx.asList with _ | ⟨head, tail⟩
  · have hx' : x.eval env = .some (Data.l []) := by
      rw [hx]; congr 1; rw [← Data.asList_l dx, h]
    simp [Prog.elim_eval_nil hx']
  · have hx' : x.eval env = .some (Data.l (head :: tail)) := by
      rw [hx]; congr 1; rw [← Data.asList_l dx, h]
    rw [Prog.elim_eval_cons hx', Prog.var_eval]
    have hidx : (env ++ [head, Data.l tail])[env.length + 1]? = some (Data.l tail) := by
      simp [List.getElem?_append_right]
    simp only [hidx, Option.getD_some]
    rfl

/-! ### Option C: per-env `PB.computes_at`

A pointwise version of `PB.computes` that talks about a specific env. -/

/-- `PB.computes_at env impl d`: for every extension `ext` of `env`, when the
program is unfolded at depth `(env ++ ext).length` and evaluated on `env ++ ext`,
it yields `d`. The `∀ ext` quantifier captures the fact that well-formed PBs
preserve their value under env-extension, which is essential for composing them
inside binders. -/
def PB.computes_at (env : List Data) (impl : PB) (d : Data) : Prop :=
  ∀ ext : List Data,
    (impl (env.length + ext.length)).eval (env ++ ext) = .some d

/-- The basic per-env consequence, instantiating `ext := []`. -/
lemma PB.computes_at.here {env : List Data} {impl : PB} {d : Data}
    (h : PB.computes_at env impl d) :
    (impl env.length).eval env = .some d := by
  simpa using h []

/-- Weakening: extending the env preserves `computes_at`. -/
lemma PB.computes_at.extend {env ext : List Data} {impl : PB} {d : Data}
    (h : PB.computes_at env impl d) :
    PB.computes_at (env ++ ext) impl d := by
  intro ext'
  have := h (ext ++ ext')
  simpa [List.append_assoc, Nat.add_assoc] using this

@[simp, grind .]
lemma PB.var_computes_at {env : List Data} {i : ℕ} (h : i < env.length) :
    PB.computes_at env (fun _ => .var i) env[i] := by
  intro ext
  simp [Prog.eval, Prog.meteredEval, List.getElem?_append_left h]
  grind

@[simp, grind .]
lemma PB.empty_computes_at {env : List Data} :
    PB.computes_at env PB.empty (Data.l []) := by
  intro ext
  simp [PB.empty, Prog.eval, Prog.meteredEval]

@[simp, grind .]
lemma PB.cons_computes_at {env : List Data} {h t : PB} {dh dt : Data}
    (hh : PB.computes_at env h dh) (ht : PB.computes_at env t dt) :
    PB.computes_at env (PB.cons h t) (Data.l (dh :: dt.asList)) := by
  intro ext
  simpa [PB.cons] using Prog.cons_eval_simp (hh ext) (ht ext)

/-- `elim` at a fixed env, nil branch. -/
@[grind .]
lemma PB.elim_nil_computes_at {env : List Data} {v em : PB} {cs : PB → PB → PB}
    {dr : Data}
    (hv : PB.computes_at env v (Data.l []))
    (hem : PB.computes_at env em dr) :
    PB.computes_at env (PB.elim v em cs) dr := by
  intro ext
  simp only [PB.elim]
  rw [Prog.elim_eval_nil (hv ext)]
  exact hem ext

/-- `elim` at a fixed env, cons branch. The body hypothesis is a `PB.computes_at`
on the env extended with `[head, Data.l tail]` (and any outer extension `ext`),
applied to `cs` with the two slot-lookup PBs for `head` and `Data.l tail`. -/
@[grind .]
lemma PB.elim_cons_computes_at {env : List Data} {v em : PB} {cs : PB → PB → PB}
    {head : Data} {tail : List Data} {dr : Data}
    (hv : PB.computes_at env v (Data.l (head :: tail)))
    (hcs : ∀ ext, PB.computes_at (env ++ ext ++ [head, Data.l tail])
                    (cs (fun _ => .var (env.length + ext.length))
                        (fun _ => .var (env.length + ext.length + 1))) dr) :
    PB.computes_at env (PB.elim v em cs) dr := by
  intro ext
  simp only [PB.elim]
  rw [Prog.elim_eval_cons (hv ext)]
  have h := (hcs ext).here
  simpa [List.append_assoc] using h

/-- The two slot-lookup PBs appearing as arguments to `cs` in
`PB.elim_cons_computes_at` compute `head` and `Data.l tail` respectively, viewed
as `PB.computes_at` over the env extended with `[head, Data.l tail]`. -/
lemma PB.elim_cons_head_var_computes_at {env ext : List Data}
    {head : Data} {tail : Data} :
    PB.computes_at (env ++ ext ++ [head, tail])
      (fun _ => .var (env.length + ext.length)) head := by
  have hlen : env.length + ext.length
      < (env ++ ext ++ [head, tail]).length := by simp
  grind [PB.var_computes_at hlen]

lemma PB.elim_cons_tail_var_computes_at {env ext : List Data}
    {head : Data} {tail : Data} :
    PB.computes_at (env ++ ext ++ [head, tail])
      (fun _ => .var (env.length + ext.length + 1)) tail := by
  have hlen : env.length + ext.length + 1
      < (env ++ ext ++ [head, tail]).length := by grind
  grind [PB.var_computes_at hlen]

/-- `PB.tail` at a fixed env, derived directly from `PB.elim_*_computes_at`. -/
lemma PB.tail_computes_at {env : List Data} {x : PB} {dx : Data}
    (hx : PB.computes_at env x dx) :
    PB.computes_at env (PB.tail x) (Data.l dx.asList.tail) := by
  cases h : dx.asList with
  | nil =>
    refine PB.elim_nil_computes_at ?_ ?_
    · intro ext; have := hx ext; rw [this]; congr 1
      rw [← Data.asList_l dx, h]
    · simp
  | cons head tail =>
    unfold PB.tail
    apply PB.elim_cons_computes_at (em := PB.empty) (cs := fun _h tl => tl)
    · intro ext; rw [hx ext]; congr 1
      rw [← Data.asList_l dx, h]
    · intro ext
      simpa using PB.elim_cons_tail_var_computes_at

/-- `PB.head` at a fixed env, derived directly from `PB.elim_*_computes_at`. -/
lemma PB.head_computes_at {env : List Data} {x : PB} {dx : Data}
    (hx : PB.computes_at env x dx) :
    PB.computes_at env (PB.head x) (dx.asList.headD (Data.l [])) := by
  cases h : dx.asList with
  | nil =>
    refine PB.elim_nil_computes_at ?_ (by simp)
    · intro ext; have := hx ext; rw [this]; congr 1
      rw [← Data.asList_l dx, h]
  | cons head tail =>
    apply PB.elim_cons_computes_at
    · intro ext; have := hx ext; rw [this]; congr 1
      rw [← Data.asList_l dx, h]
    · intro ext
      simpa using PB.elim_cons_head_var_computes_at

/-! ### Option B (mentioned for completeness): recover the ∀-quantified version

`PB.computes` is implied by the per-env strengthened version pointwise: if `impl`
computes-at every env, it computes the constant value function. -/
lemma PB.computes_of_computes_at {impl : PB} {d : Data}
    (h : ∀ env, PB.computes_at env impl d) :
    impl.computes (fun _ => d) := by
  intro env; exact (h env).here

/-- Program that evaluates to the constant `a`. -/
def constant (a : Data) : PB := match a with
  | Data.l [] => PB.empty
  | Data.l (x :: xs) => PB.cons (constant x) (constant (Data.l xs))

-- @[simp]
-- lemma constant_whileFree (a : Data) (n : ℕ) : (constant a n).WhileFree := by
--   induction a using Data.inductionL with
--   | nil => simp [constant]
--   | cons x xs ihx ihxs => simp [constant, ihx, ihxs]

-- lemma constant.semantics (a : Data) {n : ℕ} :
--     ((constant a n).meteredEvalT (by simp) []).1 = a := by
--   sorry

lemma constant_computes {env : List Data} {a : Data} :
    (constant a).computes_at env a := by
  induction a using Data.inductionL with
  | nil => simp [constant]
  | cons x xs ihx ihxs =>
    simpa [constant] using PB.cons_computes_at ihx ihxs

def encConst {α : Type} [DataEncode α] (a : α) : PB := constant (DataEncode.encode a)

def PB.ifEq (a b : PB) (then_ else_ : PB) : PB :=
  .elim (PB.eq a b)
    else_
    fun _ _ => then_

------------------------------------------------------
----------- Tools
-----------------------------------------------------------


def PB.fst (x : PB) : PB := head x

-- Compute fun x => x.snd
def PB.snd (x : PB) : PB := head (tail x)

-- Compute x => Option.some x
def PB.some (x : PB) : PB := cons x empty

----------------- Typed computation

def PB.computes_at_encoded {α : Type} [DataEncode α] (env : List Data) (x : PB) (a : α) : Prop :=
    PB.computes_at env x (DataEncode.encode a)

lemma PB.fst_computes_at_encoded {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {a : α × β}
    (hx : PB.computes_at_encoded env x a) :
    PB.computes_at_encoded env (PB.fst x) a.fst := by
  obtain ⟨a, b⟩ := a
  simpa [Data.asList] using PB.head_computes_at hx

lemma PB.snd_computes_at_encoded {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {a : α × β}
    (hx : PB.computes_at_encoded env x a) :
    PB.computes_at_encoded env (PB.snd x) a.snd := by
  obtain ⟨a, b⟩ := a
  simpa [Data.asList] using PB.head_computes_at (PB.tail_computes_at hx)

lemma PB.some_computes_at_encoded {α : Type} [DataEncode α]
    {env : List Data} {x : PB} {a : α}
    (hx : PB.computes_at_encoded env x a) :
    PB.computes_at_encoded env (PB.some x) (Option.some a) := by
  apply PB.cons_computes_at hx PB.empty_computes_at

-------------------------------------------------------------------
---------------- Universal Turing Machine (simulation of a SingleTapeTM)
---------------------------------------------------------------------------

variable [Inhabited Symbol] [Fintype Symbol] [DataEncode Symbol]

public instance : DataEncode (Turing.StackTape Symbol) where
  encode t := DataEncode.encode t.toList
  h_inj := by sorry

public instance : DataEncode (Turing.BiTape Symbol) where
  encode t := DataEncode.encode (t.head, t.left, t.right)
  h_inj := by sorry

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encode_biTape (t : Turing.BiTape Symbol) :
    DataEncode.encode t = DataEncode.encode (t.head, t.left, t.right) := by
    simp [DataEncode.encode]

def bitape_write (t v : PB) : PB := PB.cons v t.tail

lemma bitape_write_computes
    {env : List Data} {p_t p_v : PB} {t : BiTape Symbol} {v : Option Symbol}
    (h_t : PB.computes_at_encoded env p_t t)
    (h_v : PB.computes_at_encoded env p_v v) :
    PB.computes_at_encoded env (bitape_write p_t p_v) (t.write v) := by
  simp only [PB.computes_at_encoded, encode_biTape, DataEncode_pair] at h_t h_v ⊢
  apply PB.cons_computes_at h_v (PB.tail_computes_at h_t)

-- /-- Prepend an `Option` to the `StackTape` -/
-- @[scoped grind]
-- def cons (x : Option Symbol) (xs : StackTape Symbol) : StackTape Symbol :=
--   match x, xs with
--   | none, ⟨[], _⟩ => ⟨[], by grind⟩
--   | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
--   | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩

def stackTape_cons (x st : PB) : PB :=
  PB.elim x
    (PB.elim st
      PB.empty
      (fun _ _ => PB.cons x st))
    (fun _ _ => PB.cons x st)

lemma stackTape_cons_computes
    {env : List Data} {p_x p_st : PB} {x : Option Symbol} {st : StackTape Symbol}
    (h_x : PB.computes_at_encoded env p_x x)
    (h_st : PB.computes_at_encoded env p_st st) :
    (stackTape_cons p_x p_st).computes_at_encoded env (st.cons x) := by
  simp only [PB.computes_at_encoded] at h_x h_st ⊢
  -- Outer elim splits on `x`.
  cases x with
  | none =>
    -- encode none = Data.l []
    have hx0 : PB.computes_at env p_x (Data.l []) := by
      simpa [DataEncode.encode] using h_x
    refine PB.elim_nil_computes_at hx0 ?_
    -- Inner elim splits on `st.toList`.
    obtain ⟨l, hl⟩ := st
    cases l with
    | nil =>
      -- encode st = Data.l [], encode (st.cons none) = Data.l []
      have hst0 : PB.computes_at env p_st (Data.l []) := by
        simpa [DataEncode.encode, StackTape.toList] using h_st
      simpa [DataEncode.encode, StackTape.cons, StackTape.toList] using
        PB.elim_nil_computes_at hst0 (PB.empty_computes_at)
    | cons hd tl =>
      -- encode st = Data.l (encode hd :: tl.map encode)
      have hstc : PB.computes_at env p_st
          (Data.l (DataEncode.encode hd :: (tl.map DataEncode.encode))) := by
        simpa [DataEncode.encode, StackTape.toList, List.map] using h_st
      apply PB.elim_cons_computes_at hstc
        (head := DataEncode.encode hd) (tail := tl.map DataEncode.encode)
      intro ext
      -- cs body is `fun _ _ => PB.cons p_x p_st`; evaluate it.
      have hcons := PB.cons_computes_at h_x h_st
        (ext := ext ++ [DataEncode.encode hd, Data.l (tl.map DataEncode.encode)])
      simpa [PB.cons, List.append_assoc] using hcons
  | some a =>
    -- encode (some a) = Data.l [encode a]
    have hxc : PB.computes_at env p_x (Data.l [DataEncode.encode a]) := by
      simpa [DataEncode.encode] using h_x
    apply PB.elim_cons_computes_at hxc
      (head := DataEncode.encode a) (tail := [])
    intro ext
    have hcons := PB.cons_computes_at h_x h_st
      (ext := ext ++ [DataEncode.encode a, Data.l []])
    simpa [PB.cons, List.append_assoc] using hcons

def to_pair (a b : PB) : PB := PB.cons a (PB.cons b PB.empty)

--- The head component of the bitape
def bitape_head (t : PB) : PB := t.fst
--- The left component of the bitape
def bitape_left (t : PB) : PB := t.snd.fst
--- The right component of the bitape
def bitape_right (t : PB) : PB := t.snd.snd

-- def move_left (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

def bitape_move_left (t : PB) : PB :=
  to_pair (bitape_left t).head
    (to_pair
      (bitape_left t).tail
      (stackTape_cons (bitape_head t) (bitape_right t)))

-- def move_right (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

def bitape_move_right (t : PB) : PB :=
  to_pair (bitape_right t).head
    (to_pair
      (stackTape_cons (bitape_head t) (bitape_left t))
      (bitape_right t).tail)

instance : DataEncode Dir where
  encode := fun
    | Dir.left => DataEncode.encode true
    | Dir.right => DataEncode.encode false
  h_inj := by sorry

-- /--
-- Move the head to the left or right, shifting the tape underneath it.
-- -/
-- def move (t : BiTape Symbol) : Dir → BiTape Symbol
--   | .left => t.move_left
--   | .right => t.move_right

def bitape_move (tape dir : PB) : PB :=
  PB.ifEq dir (constant (DataEncode.encode Dir.left))
    (bitape_move_left tape)
    (bitape_move_right tape)

-- /--
-- Optionally perform a `move`, or do nothing if `none`.
-- -/
-- def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
--   | t, none => t
--   | t, some d => t.move d

def bitape_optionMove (t dir : PB) : PB :=
  .elim dir
    t
    (fun d _ => bitape_move t d)

instance (tm : SingleTapeTM Symbol) [DataEncode tm.State] :
    DataEncode (Turing.SingleTapeTM.Cfg tm) where
  encode cfg := DataEncode.encode (cfg.state, cfg.BiTape)
  h_inj := by sorry

-- Evaluate a function `f` at `arg` where the function is given as a graph.
-- Returns `some y` for the first `x` in the graph such that `f x = y` and `none` otherwise.
def eval_fun_graph (graph : PB) (arg : PB) : PB :=
  PB.fold
    (fun acc x =>
      PB.ifEq acc .empty
        (PB.ifEq x.fst arg (PB.some x.snd) PB.empty)
        acc)
    PB.empty graph


def cfg_state (cfg : PB) : PB := cfg.fst
def cfg_bitape (cfg : PB) : PB := cfg.snd

/-- Evaluate the transition function. Returns `((wr, dir), q')`.
 -- The return value is not wrapped inside an `Option` because the transition
 -- function is assumed to be total. -/
def eval_tr (tr : PB) (q c : PB) : PB :=
  (eval_fun_graph (eval_fun_graph tr q).head c).head

-- /-- The step function corresponding to a `SingleTapeTM`. -/
-- @[simp]
-- def step : tm.Cfg → Option tm.Cfg
--   | ⟨none, _⟩ =>
--     -- If in the halting state, there is no next configuration
--     none
--   | ⟨some q', t⟩ =>
--     -- If in state q', perform look up in the transition function
--     match tm.tr q' t.head with
--     -- and enter a new configuration with state q'' (or none for halting)
--     -- and tape updated according to the Stmt
--     | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩

-- Compute the step function given a transition function (as its graph) and a configuration.
-- Returns `Option Cfg`
def singleTapeTM_step (tr : PB) (cfg : PB) : PB :=
  PB.elim (cfg_state cfg)
    PB.empty
    (fun q' _ => PB.letIn (cfg_bitape cfg) (fun tape =>
      PB.letIn (eval_tr tr q' tape.head) (fun tr_val =>
        .some (to_pair
          tr_val.snd
          (bitape_optionMove (bitape_write tape tr_val.fst.fst) tr_val.fst.snd)))))

def tm_main_loop (tr : PB) (cfg : PB) : PB :=
  -- Note that `Cfg` is a pair of `Option State` and `BiTape`,
  -- and the termination condition is that the first element of this pair is none.
  -- This exactly matches our while loop termination condition.
  PB.while_ (fun acc => PB.elim acc
    -- accumulator is empty, initialize
    cfg
    -- accumulator is non-empty, run a single step. Ignore that the result is an option
    (fun _ _ => (singleTapeTM_step tr acc).head))

def string_to_tape (input : PB) : PB :=
  to_pair input.head (to_pair .empty input.tail)

def initial_config (q₀ : PB) (input : PB) : PB :=
  to_pair (PB.some q₀) (string_to_tape input)

/-- Turn the final config to an output, by taking the head and the right part of the tape. -/
def final_config_to_output (cfg : PB) : PB := PB.cons (bitape_head cfg.snd) (bitape_right cfg.snd)

/-- Implements a universal Single-Tape TM, assuming that the input contains the following:
((initialState, transitionFunction), input).
If it terminates, the output is the tape contents under the head and to its right. -/
def universal_tm (input : PB) :=
  final_config_to_output
    (tm_main_loop input.fst.snd (initial_config input.fst.fst input.fst.snd))

end RoseTreeMachine

end Turing
