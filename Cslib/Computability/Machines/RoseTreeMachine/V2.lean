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
public import Mathlib.Data.List.ReduceOption

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
  /-- `while_ init body`: `init` produces the starting accumulator; `body` runs with
      `env` extended by the current accumulator. -/
  | while_ (init body : Prog)
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
  | .while_ init body => do
    let (i, i_t, i_s) ← init.meteredEval env
    -- Real while loop: check the halt condition on the current accumulator first.
    -- If `acc.asList.headD = []` (empty head), halt and return `acc`.
    -- Otherwise run `body` on the accumulator and loop with its result.
    let F : ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) →
            (Data × ℕ × ℕ) → Part (Data × ℕ × ℕ) :=
      fun rec d_ts =>
        let (acc, t, s) := d_ts
        if acc.asList.headD (Data.l []) = Data.l [] then
          .some (acc, t, s)
        else
          (body.meteredEval (env ++ [acc])).bind fun (r, b_t, b_s) =>
            rec (r, t + 1 + b_t, max s b_s)
    Part.fix F (i, 1 + i_t, max 1 i_s)
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

/-- The loop core of `while_`: starting from accumulator `acc` (a `Data`),
halt and return `acc` if its `asList.headD` is empty; otherwise run `body` on
`env ++ [acc]` and recurse on the result. -/
noncomputable def Prog.whileFrom_eval (body : Prog) (env : List Data) : Data → Part Data :=
  Part.fix fun rec acc =>
    if acc.asList.headD (Data.l []) = Data.l [] then
      Part.some acc
    else
      (body.eval (env ++ [acc])).bind rec

/-- Halt-step unrolling for `whileFrom_eval`. -/
lemma Prog.whileFrom_eval_halt {body : Prog} {env : List Data} {acc : Data}
    (h_halt : acc.asList.headD (Data.l []) = Data.l []) :
    Prog.whileFrom_eval body env acc = .some acc := by
  sorry

/-- Body-step unrolling for `whileFrom_eval`. -/
lemma Prog.whileFrom_eval_step {body : Prog} {env : List Data} {acc : Data}
    (h_step : acc.asList.headD (Data.l []) ≠ Data.l []) :
    Prog.whileFrom_eval body env acc =
      (body.eval (env ++ [acc])).bind (Prog.whileFrom_eval body env) := by
  sorry

/-- Pointwise (single-env) version for `while_`: the program evaluates `init`,
then runs the loop body starting from that value. -/
lemma Prog.while_eval {init body : Prog} {env : List Data} :
    (Prog.while_ init body).eval env =
      (init.eval env).bind (Prog.whileFrom_eval body env) := by
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
  | .while_ _ _ => False

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

/-- `while_ init (fun acc => body)`. -/
def while_ (init : PB) (body : PB → PB) : PB := fun n =>
  .while_ (init n) (body (fun _ => .var n) (n + 1))

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
  change _ = Part.some (Data.l (fx env).asList.tail)
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

/-- Semantic spec for `Prog.fold`. Rather than quantifying the body universally
over arbitrary `Data` accumulators/elements, we parameterise by the actually
visited accumulator sequence `acc : ℕ → Data`. This makes the lemma usable both
for untyped and typed/encoded fold reasoning. -/
lemma Prog.fold_eval {env : List Data} {body init list : Prog}
    {da : Data} {dl : List Data} {result : Data}
    (hi : init.eval env = .some da)
    (hl : list.eval env = .some (Data.l dl))
    (acc : ℕ → Data)
    (hacc0 : acc 0 = da)
    (haccN : acc dl.length = result)
    (hstep : ∀ k (h : k < dl.length),
      body.eval (env ++ [acc k, dl[k]]) = .some (acc (k+1))) :
    (Prog.fold body init list).eval env = .some result := by
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
@[simp]
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

@[simp]
lemma PB.var_last_computes_at {env ext : List Data} {d : Data} :
    PB.computes_at (env ++ ext ++ [d])
      (fun _ => Prog.var (env.length + ext.length)) d := by
  have hlen : env.length + ext.length < (env ++ ext ++ [d]).length := by simp
  have h := PB.var_computes_at (env := env ++ ext ++ [d]) hlen
  convert h using 2
  simp [List.getElem_append]

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

lemma PB.eq_computes_at {env : List Data} {a b : PB} {da db : Data}
    (ha : PB.computes_at env a da) (hb : PB.computes_at env b db) :
    PB.computes_at env (PB.eq a b)
      (if da = db then Data.l [Data.l []] else Data.l []) := by
  intro ext
  simpa [PB.eq] using Prog.eq_eval (ha ext) (hb ext)

/-! ### Body-of-binder abstraction

The hypothesis shape arising for the body of a binder (`elim`, `letin`, `fold`,
…) is that the body PB, built from var-lookup PBs for each new binding,
computes the result on the env extended with those bindings, for any outer
extension `ext`. We package this as `PB.computes_at_body` with arity-typed
convenience wrappers. -/

/-- Depth-agnostic var-lookup PB: `PB.atSlot i = fun _ => .var i`. -/
def PB.atSlot (i : ℕ) : PB := fun _ => .var i

@[simp]
lemma PB.atSlot_computes_at {env : List Data} {i : ℕ} (h : i < env.length) :
    PB.computes_at env (PB.atSlot i) env[i] :=
  PB.var_computes_at h

@[simp]
lemma PB.atSlot_last_computes_at {env ext : List Data} {d : Data} :
    PB.computes_at (env ++ ext ++ [d])
      (PB.atSlot (env.length + ext.length)) d :=
  PB.var_last_computes_at

@[simp]
lemma PB.atSlot_last_computes_at_right {env ext : List Data} {d : Data} :
    PB.computes_at (env ++ (ext ++ [d]))
      (PB.atSlot (env.length + ext.length)) d := by
  rw [← List.append_assoc]; exact PB.atSlot_last_computes_at

/-- Body-of-binder hypothesis. `mkBody` is an arity-`bindings.length` body
builder that receives the var-lookup PBs for each binding and produces a PB.
The result must compute `dr` on `env` extended with `bindings` (under any
outer extension `ext`). -/
def PB.computes_at_body (env : List Data) (bindings : List Data)
    (mkBody : (Fin bindings.length → PB) → PB) (dr : Data) : Prop :=
  ∀ ext : List Data,
    PB.computes_at (env ++ ext ++ bindings)
      (mkBody (fun i => PB.atSlot (env.length + ext.length + i))) dr

/-- Arity-1 convenience: one new binding `b`, body `body : PB → PB`. -/
abbrev PB.computes_at_body₁ (env : List Data) (b : Data)
    (body : PB → PB) (dr : Data) : Prop :=
  PB.computes_at_body env [b] (fun a => body (a 0)) dr

/-- Arity-2 convenience: two new bindings `b₁, b₂`, body `body : PB → PB → PB`. -/
abbrev PB.computes_at_body₂ (env : List Data) (b₁ b₂ : Data)
    (body : PB → PB → PB) (dr : Data) : Prop :=
  PB.computes_at_body env [b₁, b₂] (fun a => body (a 0) (a 1)) dr

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

/-- `elim` at a fixed env, cons branch. The body hypothesis is packaged as
`PB.computes_at_body₂`: `cs`, applied to the var-lookup PBs for `head` and
`Data.l tail`, computes `dr` on the env extended with `[head, Data.l tail]`. -/
@[grind .]
lemma PB.elim_cons_computes_at {env : List Data} {v em : PB} {cs : PB → PB → PB}
    {head : Data} {tail : List Data} {dr : Data}
    (hv : PB.computes_at env v (Data.l (head :: tail)))
    (hcs : PB.computes_at_body₂ env head (Data.l tail) cs dr) :
    PB.computes_at env (PB.elim v em cs) dr := by
  intro ext
  simp only [PB.elim]
  rw [Prog.elim_eval_cons (hv ext)]
  have h := (hcs ext).here
  simpa [PB.atSlot, List.append_assoc] using h

/-- The slot-lookup PB for `head` in the body of an `elim` (or any 2-binding
body). -/
lemma PB.elim_cons_head_var_computes_at {env ext : List Data}
    {head : Data} {tail : Data} :
    PB.computes_at (env ++ ext ++ [head, tail])
      (PB.atSlot (env.length + ext.length)) head := by
  show PB.computes_at _ (fun _ => .var (env.length + ext.length)) _
  have hlen : env.length + ext.length
      < (env ++ ext ++ [head, tail]).length := by simp
  grind [PB.var_computes_at hlen]

/-- The slot-lookup PB for the second binding in the body of an `elim`. -/
lemma PB.elim_cons_tail_var_computes_at {env ext : List Data}
    {head : Data} {tail : Data} :
    PB.computes_at (env ++ ext ++ [head, tail])
      (PB.atSlot (env.length + ext.length + 1)) tail := by
  show PB.computes_at _ (fun _ => .var (env.length + ext.length + 1)) _
  have hlen : env.length + ext.length + 1
      < (env ++ ext ++ [head, tail]).length := by simp; omega
  grind [PB.var_computes_at hlen]

/-- `fold` at a fixed env: lifts `Prog.fold_eval` pointwise. The body hypothesis
is packaged as `PB.computes_at_body₂` parameterised over the current
accumulator `acc` and element `el`. -/
lemma PB.fold_computes_at {env : List Data} {init list : PB}
    {body : PB → PB → PB}
    {da : Data} {dl : List Data} {f : Data → Data → Data}
    (hi : PB.computes_at env init da)
    (hl : PB.computes_at env list (Data.l dl))
    (hbody : ∀ acc el, PB.computes_at_body₂ env acc el body (f acc el)) :
    PB.computes_at env (PB.fold body init list) (dl.foldl f da) := by
  intro ext
  simp only [PB.fold]
  refine Prog.fold_eval (hi ext) (hl ext)
    (fun k => (dl.take k).foldl f da) rfl (by simp) ?_
  intro k hk
  have h := (hbody ((dl.take k).foldl f da) dl[k] ext).here
  have hfoldl_succ :
      (dl.take (k+1)).foldl f da = f ((dl.take k).foldl f da) dl[k] := by
    rw [List.take_succ, List.foldl_append]
    simp [List.getElem?_eq_getElem hk]
  simp only [hfoldl_succ]
  simpa [PB.atSlot, List.append_assoc] using h

/-! ### Spec for `PB.while_`

`PB.while_ init body` is a real while loop: it starts from `init`, checks the
halt condition (`asList.headD = []`) on the current accumulator, and either
returns it (halt) or runs `body` and loops with the body's result. -/

/-- Generic iteration spec for `PB.while_`. The result is `f^[N] init` where
`N` is the smallest iteration index whose encoding's `headD` is empty. -/
lemma PB.while_computes_iter {α : Type} [DataEncode α]
    {env : List Data} {p_init : PB} {body : PB → PB}
    (f : α → α) (init : α)
    (h_init : PB.computes_at env p_init (DataEncode.encode init))
    (h_body : ∀ c, PB.computes_at_body₁ env (DataEncode.encode c) body
        (DataEncode.encode (f c)))
    (h_halts : ∃ n, (DataEncode.encode (f^[n] init)).asList.headD (Data.l []) = Data.l []) :
    PB.computes_at env (PB.while_ p_init body) (DataEncode.encode (f^[Nat.find h_halts] init)) := by
  intro ext
  set n := env.length + ext.length with hn
  set bd : Prog := body (fun _ => .var n) (n + 1) with bd_def
  -- Unfold one level of `while_` at depth `n`.
  change (Prog.while_ (p_init n) bd).eval (env ++ ext) = _
  rw [Prog.while_eval]
  rw [show (p_init n).eval (env ++ ext) = .some (DataEncode.encode init) by
        simpa [hn] using h_init ext, Part.bind_some]
  -- Reduce to a statement about `whileFrom_eval`.
  set N := Nat.find h_halts with N_def
  suffices ∀ k, k ≤ N →
      Prog.whileFrom_eval bd (env ++ ext) (DataEncode.encode (f^[k] init))
        = .some (DataEncode.encode (f^[N] init)) from this 0 (Nat.zero_le _)
  intro k hk
  -- Induct on the distance to `N`.
  induction hd : N - k generalizing k with
  | zero =>
    have hkN : k = N := by omega
    subst hkN
    exact Prog.whileFrom_eval_halt (Nat.find_spec h_halts)
  | succ m ih =>
    have hkN : k < N := by omega
    have h_not_halt :
        (DataEncode.encode (f^[k] init)).asList.headD (Data.l []) ≠ Data.l [] :=
      Nat.find_min h_halts hkN
    rw [Prog.whileFrom_eval_step h_not_halt]
    -- The body computes `f` at `f^[k] init`.
    have h_body_eval : bd.eval ((env ++ ext) ++ [DataEncode.encode (f^[k] init)]) =
        .some (DataEncode.encode (f (f^[k] init))) := by
      have h := (h_body (f^[k] init) ext).here
      simpa [bd_def, hn, PB.atSlot] using h
    rw [h_body_eval, Part.bind_some]
    rw [show f (f^[k] init) = f^[k+1] init from (Function.iterate_succ_apply' f k init).symm]
    exact ih (k + 1) (by omega) (by omega)


/-- `letIn` at a fixed env: the body hypothesis is packaged as `PB.computes_at_body₁`. -/
lemma PB.letIn_computes_at {env : List Data} {val : PB} {body : PB → PB}
    {dv dr : Data}
    (hv : PB.computes_at env val dv)
    (hbody : PB.computes_at_body₁ env dv body dr) :
    PB.computes_at env (PB.letIn val body) dr := by
  intro ext
  show (Prog.letin (val (env.length + ext.length))
      (body (fun _ => Prog.var (env.length + ext.length))
        (env.length + ext.length + 1))).eval (env ++ ext) = .some dr
  rw [Prog.letin_eval (hv ext)]
  have h := (hbody ext).here
  simpa [PB.atSlot] using h

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
      exact PB.elim_cons_tail_var_computes_at

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
      exact PB.elim_cons_head_var_computes_at

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

lemma PB.ifEq_computes_at {env : List Data} {a b then_ else_ : PB} {da db dr : Data}
    (ha : PB.computes_at env a da) (hb : PB.computes_at env b db)
    (hthen : da = db → PB.computes_at env then_ dr)
    (helse : da ≠ db → PB.computes_at env else_ dr) :
    (PB.ifEq a b then_ else_).computes_at env dr := by
  unfold PB.ifEq
  by_cases h : da = db
  · have heq : PB.computes_at env (PB.eq a b) (Data.l [Data.l []]) := by
      simpa [h] using PB.eq_computes_at ha hb
    refine PB.elim_cons_computes_at heq ?_
    intro ext
    have h' := (hthen h).extend (ext := ext ++ [Data.l [], Data.l []])
    simpa [List.append_assoc] using h'
  · have heq : PB.computes_at env (PB.eq a b) (Data.l []) := by
      simpa [h] using PB.eq_computes_at ha hb
    exact PB.elim_nil_computes_at heq (helse h)

------------------------------------------------------
----------- Tools
-----------------------------------------------------------


def PB.fst (x : PB) : PB := head x

-- Compute fun x => x.snd
def PB.snd (x : PB) : PB := head (tail x)

-- Compute x => Option.some x
def PB.some (x : PB) : PB := cons x empty

def PB.optionElim (x : PB) (noneCase : PB) (someCase : PB → PB) : PB :=
  elim x noneCase (fun hd _ => someCase hd)

----------------- Typed computation

def PB.computes_at_encoded {α : Type} [DataEncode α] (env : List Data) (x : PB) (a : α) : Prop :=
    PB.computes_at env x (DataEncode.encode a)

@[simp]
lemma PB.atSlot_last_computes_at_encoded {α : Type} [DataEncode α]
    {env ext : List Data} {a : α} :
    PB.computes_at_encoded (env ++ ext ++ [DataEncode.encode a])
      (PB.atSlot (env.length + ext.length)) a :=
  PB.atSlot_last_computes_at

@[simp]
lemma PB.atSlot_last_computes_at_encoded_right {α : Type} [DataEncode α]
    {env ext : List Data} {a : α} :
    PB.computes_at_encoded (env ++ (ext ++ [DataEncode.encode a]))
      (PB.atSlot (env.length + ext.length)) a :=
  PB.atSlot_last_computes_at_right

/-- Encoded body-of-binder hypothesis: the body computes a typed value `a`
under any outer env extension. -/
abbrev PB.computes_at_body_encoded {α : Type} [DataEncode α]
    (env : List Data) (bindings : List Data)
    (mkBody : (Fin bindings.length → PB) → PB) (a : α) : Prop :=
  PB.computes_at_body env bindings mkBody (DataEncode.encode a)

abbrev PB.computes_at_body₁_encoded {α β : Type} [DataEncode α] [DataEncode β]
    (env : List Data) (a : α) (body : PB → PB) (b : β) : Prop :=
  PB.computes_at_body₁ env (DataEncode.encode a) body (DataEncode.encode b)

abbrev PB.computes_at_body₂_encoded {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]
    (env : List Data) (a : α) (b : β) (body : PB → PB → PB) (c : γ) : Prop :=
  PB.computes_at_body₂ env (DataEncode.encode a) (DataEncode.encode b) body (DataEncode.encode c)

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

lemma PB.optionElim_computes_none {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {noneCase : PB} {someCase : PB → PB}
    (hx : x.computes_at_encoded env (none : Option α))
    {a : β}
    (h_none : noneCase.computes_at_encoded env a) :
    (PB.optionElim x noneCase someCase).computes_at_encoded env a := by
  apply PB.elim_nil_computes_at hx h_none

lemma PB.optionElim_computes_some {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {noneCase : PB} {someCase : PB → PB}
    {a : α}
    (hx : x.computes_at_encoded env (Option.some a))
    {b : β}
    (h_some : PB.computes_at_body₁_encoded env a someCase b) :
    (PB.optionElim x noneCase someCase).computes_at_encoded env b := by
  apply PB.elim_cons_computes_at hx
  intro ext
  simpa [List.append_assoc] using (h_some ext).extend

lemma PB.letIn_computes_at_encoded {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {val : PB} {body : PB → PB} {v : α} {b : β}
    (hv : val.computes_at_encoded env v)
    (hbody : PB.computes_at_body₁_encoded env v body b) :
    (PB.letIn val body).computes_at_encoded env b :=
  PB.letIn_computes_at hv hbody

/-- Encoded variant of `PB.fold_computes_at`: typed accumulator `a : α`, typed
list elements of type `β`, and a typed step function `f : α → β → α`. The body
hypothesis is `PB.computes_at_body₂_encoded` parameterised over `acc : α` and
`el : β`. -/
lemma PB.fold_computes_at_encoded
    {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {init list : PB} {body : PB → PB → PB}
    {a : α} {l : List β} {f : α → β → α}
    (hi : init.computes_at_encoded env a)
    (hl : list.computes_at_encoded env l)
    (hbody : ∀ acc el, PB.computes_at_body₂_encoded env acc el body (f acc el)) :
    PB.computes_at_encoded env (PB.fold body init list) (l.foldl f a) := by
  intro ext
  simp only [PB.fold]
  have hl' :
      (list (env.length + ext.length)).eval (env ++ ext)
        = .some (Data.l (l.map DataEncode.encode)) := hl ext
  refine Prog.fold_eval (hi ext) hl'
    (fun k => DataEncode.encode ((l.take k).foldl f a)) rfl (by simp) ?_
  intro k hk
  have hk' : k < l.length := by simpa using hk
  have h := (hbody ((l.take k).foldl f a) l[k] ext).here
  have hfoldl_succ :
      (l.take (k+1)).foldl f a = f ((l.take k).foldl f a) l[k] := by
    rw [List.take_succ, List.foldl_append]
    simp [List.getElem?_eq_getElem hk']
  have hget : (l.map DataEncode.encode)[k] = DataEncode.encode l[k] := by simp
  simp only [hget, hfoldl_succ]
  simpa [PB.atSlot, List.append_assoc] using h
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
  PB.optionElim x
    (PB.elim st
      PB.empty
      (fun _ _ => PB.cons x st))
    (fun _ => PB.cons x st)

omit [Inhabited Symbol] [Fintype Symbol] in
lemma stackTape_cons_computes
    {env : List Data} {p_x p_st : PB} {x : Option Symbol} {st : StackTape Symbol}
    (h_x : PB.computes_at_encoded env p_x x)
    (h_st : PB.computes_at_encoded env p_st st) :
    (stackTape_cons p_x p_st).computes_at_encoded env (st.cons x) := by
  cases x with
  | none =>
    apply PB.optionElim_computes_none h_x
    obtain ⟨l, hl⟩ := st
    cases l with
    | nil =>
      simpa [DataEncode.encode] using
        PB.elim_nil_computes_at (by simpa using h_st) (PB.empty_computes_at)
    | cons hd tl =>
      apply PB.elim_cons_computes_at (by simpa [DataEncode.encode] using h_st)
      intro ext
      simpa using (PB.cons_computes_at h_x h_st).extend
  | some a =>
    apply PB.optionElim_computes_some h_x
    intro ext
    simpa using (PB.cons_computes_at (by simpa [DataEncode.encode] using h_x) h_st).extend

def to_pair (a b : PB) : PB := PB.cons a (PB.cons b PB.empty)

lemma to_pair_computes {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {p_a p_b : PB}
    {a : α} {b : β}
    (h_a : p_a.computes_at_encoded env a)
    (h_b : p_b.computes_at_encoded env b) :
    (to_pair p_a p_b).computes_at_encoded env (a, b) := by
  simpa [DataEncode.encode, to_pair] using
    PB.cons_computes_at h_a (PB.cons_computes_at h_b PB.empty_computes_at)

--- The head component of the bitape
def bitape_head (t : PB) : PB := t.fst
--- The left component of the bitape
def bitape_left (t : PB) : PB := t.snd.fst
--- The right component of the bitape
def bitape_right (t : PB) : PB := t.snd.snd

omit [Inhabited Symbol] [Fintype Symbol]
lemma bitape_head_computes {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    (bitape_head p_t).computes_at_encoded env t.head := PB.head_computes_at h_t

omit [Inhabited Symbol] [Fintype Symbol]
lemma bitape_left_computes {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    (bitape_left p_t).computes_at_encoded env t.left :=
  PB.head_computes_at (PB.head_computes_at (PB.tail_computes_at h_t))

omit [Inhabited Symbol] [Fintype Symbol]
lemma bitape_right_computes {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    (bitape_right p_t).computes_at_encoded env t.right :=
  PB.head_computes_at (PB.tail_computes_at (PB.head_computes_at (PB.tail_computes_at h_t)))

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encode_stackTape_head (st : StackTape Symbol) :
    (DataEncode.encode st).asList.headD (Data.l []) = DataEncode.encode st.head := by
  obtain ⟨l, hl⟩ := st
  cases l <;> simp [DataEncode.encode, StackTape.head, Data.asList]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encode_stackTape_tail (st : StackTape Symbol) :
    Data.l (DataEncode.encode st).asList.tail = DataEncode.encode st.tail := by
  obtain ⟨l, hl⟩ := st
  cases l <;> simp [DataEncode.encode, StackTape.tail, Data.asList]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma stackTape_head_computes_at_encoded {env : List Data} {p_st : PB} {st : StackTape Symbol}
    (h_st : PB.computes_at_encoded env p_st st) :
    (p_st.head).computes_at_encoded env st.head := by
  unfold PB.computes_at_encoded
  simpa [← encode_stackTape_head] using PB.head_computes_at h_st

omit [Inhabited Symbol] [Fintype Symbol] in
lemma stackTape_tail_computes_at_encoded {env : List Data} {p_st : PB} {st : StackTape Symbol}
    (h_st : PB.computes_at_encoded env p_st st) :
    (p_st.tail).computes_at_encoded env st.tail := by
  unfold PB.computes_at_encoded
  simpa [← encode_stackTape_tail] using PB.tail_computes_at h_st

-- def move_left (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

def bitape_move_left (t : PB) : PB :=
  to_pair (bitape_left t).head
    (to_pair
      (bitape_left t).tail
      (stackTape_cons (bitape_head t) (bitape_right t)))

lemma bitape_move_left_computes
    {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    PB.computes_at_encoded env (bitape_move_left p_t) t.move_left := by
  unfold PB.computes_at_encoded
  rw [encode_biTape]
  exact to_pair_computes
    (stackTape_head_computes_at_encoded (bitape_left_computes h_t))
    (to_pair_computes
      (stackTape_tail_computes_at_encoded (bitape_left_computes h_t))
      (stackTape_cons_computes (bitape_head_computes h_t) (bitape_right_computes h_t)))

-- def move_right (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

def bitape_move_right (t : PB) : PB :=
  to_pair (bitape_right t).head
    (to_pair
      (stackTape_cons (bitape_head t) (bitape_left t))
      (bitape_right t).tail)

lemma bitape_move_right_computes
    {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    PB.computes_at_encoded env (bitape_move_right p_t) t.move_right := by
  unfold PB.computes_at_encoded
  rw [encode_biTape]
  exact to_pair_computes
    (stackTape_head_computes_at_encoded (bitape_right_computes h_t))
    (to_pair_computes
      (stackTape_cons_computes (bitape_head_computes h_t) (bitape_left_computes h_t))
      (stackTape_tail_computes_at_encoded (bitape_right_computes h_t)))

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

lemma bitape_move_computes {env : List Data} {p_t p_dir : PB} {t : BiTape Symbol} {d : Dir}
    (h_t : PB.computes_at_encoded env p_t t)
    (h_dir : PB.computes_at_encoded env p_dir d) :
    (bitape_move p_t p_dir).computes_at_encoded env (t.move d) := by
  unfold PB.computes_at_encoded bitape_move
  refine PB.ifEq_computes_at h_dir constant_computes ?_ ?_
  · intro hd_eq
    -- TODO could use injectivity here once we have it.
    cases d with
    | left => exact bitape_move_left_computes h_t
    | right =>
      exfalso
      exact absurd hd_eq (by decide)
  · intro hne
    cases d with
    | left => exact absurd rfl hne
    | right => exact bitape_move_right_computes h_t

-- /--
-- Optionally perform a `move`, or do nothing if `none`.
-- -/
-- def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
--   | t, none => t
--   | t, some d => t.move d

def bitape_optionMove (t dir : PB) : PB :=
  PB.optionElim dir
    t
    (fun d => bitape_move t d)

lemma bitape_optionMove_computes {env : List Data} {p_t p_dir : PB}
    {t : BiTape Symbol} {d : Option Dir}
    (h_t : PB.computes_at_encoded env p_t t)
    (h_dir : PB.computes_at_encoded env p_dir d) :
    (bitape_optionMove p_t p_dir).computes_at_encoded env (t.optionMove d) := by
  unfold PB.computes_at_encoded bitape_optionMove BiTape.optionMove
  match d with
  | none => simpa using PB.optionElim_computes_none h_dir h_t
  | some d =>
    apply PB.optionElim_computes_some h_dir
    intro ext
    exact bitape_move_computes (by simpa using h_t.extend) (by simp)

instance (tm : SingleTapeTM Symbol) [DataEncode tm.State] :
    DataEncode (Turing.SingleTapeTM.Cfg tm) where
  encode cfg := DataEncode.encode (cfg.state, cfg.BiTape)
  h_inj := by sorry

-- Evaluate a function `f` at `arg` where the function is given as a graph.
-- Returns `some y` for the first `x` in the graph such that `f x = y` and `none` otherwise.
def eval_fun_graph (graph : PB) (arg : PB) : PB :=
  PB.fold
    (fun acc x =>
      PB.optionElim acc
        (PB.ifEq x.fst arg (PB.some x.snd) PB.empty)
        fun _ => acc)
    PB.empty graph

/-- Semantic spec of `eval_fun_graph`: given an encoded graph (list of
`(α × β)`-pairs) and an encoded argument `a : α`, returns
`(graph.find? (·.1 = a)).map (·.2)`, i.e. `some y` for the first pair `(a, y)`
in the graph, else `none`. -/
lemma eval_fun_graph_computes
    {α β : Type} [DataEncode α] [DataEncode β] [DecidableEq α]
    {env : List Data} {p_graph p_arg : PB}
    {graph : List (α × β)} {a : α}
    (h_graph : p_graph.computes_at_encoded env graph)
    (h_arg : p_arg.computes_at_encoded env a) :
    (eval_fun_graph p_graph p_arg).computes_at_encoded env
      ((graph.find? (fun p => p.1 = a)).map (·.2)) := by
  -- The Lean-level step function for the fold.
  let step : Option β → α × β → Option β :=
    fun acc x => acc.elim (if x.1 = a then some x.2 else none) (fun _ => acc)
  -- Once the accumulator is `some _`, it stays `some _`.
  have stays : ∀ (l : List (α × β)) (b : β), l.foldl step (some b) = some b := by
    intro l b
    induction l with
    | nil => simp
    | cons hd tl ih => simp [step, ih]
  -- `foldl step none` matches `find?`-then-`map snd`.
  have key : ∀ l : List (α × β),
      l.foldl step none = (l.find? (fun p => p.1 = a)).map (·.2) := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldl_cons, List.find?_cons]
      by_cases h : hd.1 = a
      · simp [step, h, stays]
      · simp [step, h, ih]
  rw [show (graph.find? (fun p => p.1 = a)).map (·.2)
        = graph.foldl step none from (key graph).symm]
  unfold eval_fun_graph
  refine PB.fold_computes_at_encoded (a := (none : Option β)) (f := step)
    (by simp [PB.computes_at_encoded, DataEncode.encode]) h_graph ?_
  intro acc x ext
  rcases acc with _ | v
  · -- acc = none: step none x = if x.1 = a then some x.2 else none
    refine PB.optionElim_computes_none (α := β)
      PB.elim_cons_head_var_computes_at ?_
    refine PB.ifEq_computes_at
      (PB.fst_computes_at_encoded PB.elim_cons_tail_var_computes_at)
      (by simpa using h_arg.extend) ?_ ?_
    · intro h_enc
      have h_eq : x.1 = a := DataEncode.h_inj h_enc
      change PB.computes_at_encoded _ _ (step none x)
      simp only [step, Option.elim_none, if_pos h_eq]
      exact PB.some_computes_at_encoded
        (PB.snd_computes_at_encoded PB.elim_cons_tail_var_computes_at)
    · intro h_enc
      have h_ne : x.1 ≠ a := fun h => h_enc (by rw [h])
      simp [DataEncode.encode, step, h_ne]
  · -- acc = some v: step (some v) x = some v
    refine PB.optionElim_computes_some (α := β)
      (PB.elim_cons_head_var_computes_at
        (head := DataEncode.encode (some v : Option β))) ?_
    intro ext'
    simpa [List.append_assoc, step] using PB.elim_cons_head_var_computes_at.extend

-- def graphOf {α β : Type} [Fintype α] (f : α → β) : List (α × β) :=
--   Fintype.elems.toList.map (fun a => (a, f a))

lemma eval_fun_graph_computes_of_fun
    {α β : Type} [DataEncode α] [DataEncode β] [Fintype α]
    {env : List Data} {p_graph p_arg : PB}
    {a : α}
    {f : α → β}
    (h_graph : p_graph.computes_at_encoded env (Fintype.elems.toList.map (fun a => (a, f a))))
    (h_arg : p_arg.computes_at_encoded env a) :
    (eval_fun_graph p_graph p_arg).head.computes_at_encoded env (f a) := by
  classical
  have heq : ∀ (L : List α), a ∈ L →
      ((L.map (fun a' => (a', f a'))).find?
        (fun p => p.1 = a)).map (·.2) = some (f a) := by
    intro L hmem
    induction L with
    | nil => exact absurd hmem (by simp)
    | cons hd tl ih => grind
  have h := eval_fun_graph_computes h_graph h_arg
  rw [heq _ (Finset.mem_toList.mpr (Fintype.complete a))] at h
  simpa [DataEncode.encode, Data.asList] using PB.head_computes_at h

def cfg_state (cfg : PB) : PB := cfg.fst
def cfg_bitape (cfg : PB) : PB := cfg.snd

lemma cfg_state_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p : PB} {cfg : Turing.SingleTapeTM.Cfg tm}
    (h : p.computes_at_encoded env cfg) :
    (cfg_state p).computes_at_encoded env cfg.state :=
  PB.fst_computes_at_encoded (a := (cfg.state, cfg.BiTape)) h

lemma cfg_bitape_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p : PB} {cfg : Turing.SingleTapeTM.Cfg tm}
    (h : p.computes_at_encoded env cfg) :
    (cfg_bitape p).computes_at_encoded env cfg.BiTape :=
  PB.snd_computes_at_encoded (a := (cfg.state, cfg.BiTape)) h

/-- Evaluate the transition function. Returns `((wr, dir), q')`.
 -- The return value is not wrapped inside an `Option` because the transition
 -- function is assumed to be total. -/
def eval_tr (tr : PB) (q c : PB) : PB :=
  (eval_fun_graph (eval_fun_graph tr q).head c).head

instance : DataEncode (SingleTapeTM.Stmt Symbol) where
  encode stmt := DataEncode.encode (stmt.symbol, stmt.movement)
  h_inj := by sorry

lemma eval_tr_computes {State : Type} [Fintype State] [DataEncode State]
    [DecidableEq State] [Fintype Symbol]
    {env : List Data} {p_tr p_q p_c : PB}
    {tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State}
    {q : State}
    {c : Option Symbol}
    (h_tr : p_tr.computes_at_encoded env
      ((Fintype.elems : Finset State).toList.map (fun q' : State =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' : Option Symbol => (c', tr q' c'))))))
    (h_q : p_q.computes_at_encoded env q)
    (h_c : p_c.computes_at_encoded env c) :
    (eval_tr p_tr p_q p_c).computes_at_encoded env (tr q c) := by
  unfold eval_tr
  exact eval_fun_graph_computes_of_fun (α := Option Symbol) (f := tr q)
    (eval_fun_graph_computes_of_fun (α := State) (f := fun q' =>
      (Fintype.elems : Finset (Option Symbol)).toList.map (fun c' => (c', tr q' c')))
      h_tr h_q) h_c

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
  PB.optionElim (cfg_state cfg)
    PB.empty
    (fun q' => PB.letIn (cfg_bitape cfg) (fun tape =>
      PB.letIn (eval_tr tr q' tape.head) (fun tr_val =>
        .some (to_pair
          tr_val.snd
          (bitape_optionMove (bitape_write tape tr_val.fst.fst) tr_val.fst.snd)))))

lemma singleTapeTM_step_computes [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_tr p_cfg : PB} {cfg : tm.Cfg}
    (h_tr : p_tr.computes_at_encoded env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.computes_at_encoded env cfg) :
    (singleTapeTM_step p_tr p_cfg).computes_at_encoded env (tm.step cfg) := by
  unfold singleTapeTM_step
  obtain ⟨state, t⟩ := cfg
  match hst : state with
  | none =>
    refine PB.optionElim_computes_none (cfg_state_computes h_cfg) ?_
    change PB.empty.computes_at_encoded env (none : Option tm.Cfg)
    simp [PB.computes_at_encoded, DataEncode.encode]
  | some q' =>
    refine PB.optionElim_computes_some (cfg_state_computes h_cfg) ?_
    intro ext1
    -- TODO letin makes this proof complicated.
    -- Outer letIn: bind `tape := cfg_bitape p_cfg`, value `t`.
    apply PB.letIn_computes_at_encoded (v := t)
      (by simpa [List.append_assoc] using cfg_bitape_computes h_cfg.extend)
    intro ext2
    set env2 := env ++ ext1 ++ [DataEncode.encode q'] with env2_def
    -- The slot for `q'` at depth `env.length + ext1.length`.
    have h_q'_slot : PB.computes_at_encoded
        (env2 ++ ext2 ++ [DataEncode.encode t])
        (PB.atSlot (env.length + ext1.length)) q' := by
      simpa [env2_def] using PB.atSlot_last_computes_at_encoded.extend
    -- The slot for `tape` at depth `env2.length + ext2.length`.
    have h_tape_slot : PB.computes_at_encoded
        (env2 ++ ext2 ++ [DataEncode.encode t])
        (PB.atSlot (env2.length + ext2.length)) t :=
      PB.atSlot_last_computes_at_encoded
    apply PB.letIn_computes_at_encoded
      (eval_tr_computes
        (by simpa [env2_def, List.append_assoc] using h_tr.extend)
        h_q'_slot (bitape_head_computes h_tape_slot))
    intro ext3
    set env3 := env2 ++ ext2 ++ [DataEncode.encode t] with env3_def
    set envS := env3 ++ ext3 ++ [DataEncode.encode (tm.tr q' t.head)] with envS_def
    -- Re-derive tape slot at envS.
    have h_tape_slot' : PB.computes_at_encoded envS
        (PB.atSlot (env2.length + ext2.length)) t := by
      simpa [envS_def, env3_def, List.append_assoc] using
        h_tape_slot.extend (ext := ext3 ++ [DataEncode.encode (tm.tr q' t.head)])
    -- Destructure the transition result.
    rcases htr_eq : tm.tr q' t.head with ⟨⟨wr, dir⟩, q''⟩
    have h_trval : PB.computes_at_encoded envS
        (PB.atSlot (env3.length + ext3.length))
        (SingleTapeTM.Stmt.mk (Symbol := Symbol) wr dir, q'') := by
      simp [envS_def, htr_eq]
    unfold SingleTapeTM.step
    simp only [htr_eq]
    exact PB.some_computes_at_encoded
      (to_pair_computes
        (PB.snd_computes_at_encoded h_trval)
        (bitape_optionMove_computes
          (bitape_write_computes h_tape_slot'
            (PB.fst_computes_at_encoded (a := (wr, dir))
              (PB.fst_computes_at_encoded h_trval)))
          (PB.snd_computes_at_encoded (a := (wr, dir))
            (PB.fst_computes_at_encoded h_trval))))

def tm_main_loop (tr : PB) (cfg : PB) : PB :=
  -- The accumulator is the current `Cfg`. The body applies `singleTapeTM_step`
  -- (an `Option Cfg`); on `some next` we continue with `next`, on `none` we keep
  -- the current `acc` (which has `state = none`, signalling halt to `while_`).
  PB.while_ cfg
    (fun acc => PB.optionElim (singleTapeTM_step tr acc) acc (fun next => next))

/-- Spec for `tm_main_loop`: assuming the TM eventually halts when started from
`cfg` (witnessed by some `n` after which iterating `tm.step` reaches a `none`
state), the loop computes the configuration obtained after the *minimal* such
number of steps. Here `tm.step` is lifted to `tm.Cfg → tm.Cfg` by treating the
halt result `none` as a fixed point via `Option.getD`. -/
lemma tm_main_loop_computes [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_tr p_cfg : PB} {cfg : tm.Cfg}
    (h_tr : p_tr.computes_at_encoded env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.computes_at_encoded env cfg)
    (h_halts : ∃ n, (((fun c => (tm.step c).getD c)^[n] cfg)).state = none) :
    (tm_main_loop p_tr p_cfg).computes_at_encoded env
      ((fun c => (tm.step c).getD c)^[Nat.find h_halts] cfg) := by
  -- Lift `tm.step` to a total `tm.Cfg → tm.Cfg` map.
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with step_def
  -- `headD` of an encoded `Cfg` is empty iff the state is `none`.
  have headD_iff : ∀ c : tm.Cfg,
      (DataEncode.encode c).asList.headD (Data.l []) = Data.l [] ↔ c.state = none := by
    rintro ⟨s, t⟩; cases s <;> simp [DataEncode.encode, DataEncode_pair, Data.asList]
  -- Translate the halting hypothesis through the iff.
  have h_halts' : ∃ n, (DataEncode.encode (step^[n] cfg)).asList.headD (Data.l []) = Data.l [] :=
    h_halts.imp fun _ h => (headD_iff _).mpr h
  have find_eq : Nat.find h_halts' = Nat.find h_halts :=
    le_antisymm
      (Nat.find_le ((headD_iff _).mpr (Nat.find_spec h_halts)))
      (Nat.find_le ((headD_iff _).mp (Nat.find_spec h_halts')))
  -- Reduce to a `while_` spec call.
  change PB.computes_at env (tm_main_loop p_tr p_cfg)
    (DataEncode.encode (step^[Nat.find h_halts] cfg))
  rw [← find_eq]
  unfold tm_main_loop
  refine PB.while_computes_iter (env := env) (p_init := p_cfg)
    (body := fun acc => PB.optionElim (singleTapeTM_step p_tr acc) acc (fun next => next))
    step cfg h_cfg ?_ h_halts'
  -- Body computes `step` at every typed accumulator (∀ ext).
  intro c ext
  set E := env ++ ext with E_def
  have hE_len : E.length = env.length + ext.length := by simp [E_def]
  have h_acc : PB.computes_at_encoded (E ++ [DataEncode.encode c])
      (PB.atSlot E.length) c := by
    simpa using PB.atSlot_last_computes_at_encoded (env := E) (ext := []) (a := c)
  have h_step_eval :
      (singleTapeTM_step p_tr (PB.atSlot E.length)).computes_at_encoded
        (E ++ [DataEncode.encode c]) (tm.step c) := by
    have h_tr_ext : PB.computes_at_encoded (E ++ [DataEncode.encode c]) p_tr
        ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))) := by
      have := h_tr.extend (ext := ext ++ [DataEncode.encode c])
      simpa [E_def, List.append_assoc] using this
    exact singleTapeTM_step_computes h_tr_ext h_acc
  -- Show the body computes `step c` at slot `E.length = env.length + ext.length`.
  change PB.computes_at (E ++ [DataEncode.encode c])
    (PB.optionElim (singleTapeTM_step p_tr (PB.atSlot (env.length + ext.length)))
      (PB.atSlot (env.length + ext.length))
      (fun next => next)) (DataEncode.encode (step c))
  rw [← hE_len]
  cases hstep_c : tm.step c with
  | none =>
    rw [show step c = c from by simp only [step_def]; rw [hstep_c]; rfl]
    exact PB.optionElim_computes_none (hstep_c ▸ h_step_eval) h_acc
  | some next =>
    rw [show step c = next from by simp only [step_def]; rw [hstep_c]; rfl]
    refine PB.optionElim_computes_some (hstep_c ▸ h_step_eval) ?_
    intro ext'
    simpa using PB.atSlot_last_computes_at_encoded
      (env := E ++ [DataEncode.encode c]) (ext := ext') (a := next)

def reverse (x : PB) : PB :=
  PB.fold (fun acc el => PB.cons el acc) PB.empty x

lemma reverse_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List α}
    (h : p.computes_at_encoded env l) :
    (reverse p).computes_at_encoded env l.reverse := by
  unfold reverse
  have h_fold : l.reverse = l.foldl (fun acc el => el :: acc) [] := by simp
  rw [h_fold]
  apply PB.fold_computes_at_encoded (by simp [PB.computes_at_encoded]) h
  -- TODO at this point, we should actually be able to just apply a combinator on the semantics
  -- of PB.cons
  intro acc el ext
  have h_el : PB.computes_at
      (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el])
      (PB.atSlot (env.length + ext.length + 1)) (DataEncode.encode el) := by
    simpa using (PB.atSlot_last_computes_at (ext := ext ++ [DataEncode.encode acc])).extend
  simpa [DataEncode.encode, Data.asList] using
    PB.cons_computes_at h_el (by simpa using PB.atSlot_last_computes_at.extend)

def list_map (x : PB) (f : PB → PB) : PB :=
  reverse (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty x)

lemma list_map_computes {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {p : PB} {l : List α}
    {f : PB → PB} {g : α → β}
    (h : p.computes_at_encoded env l)
    (hf : ∀ x : α, PB.computes_at_body₁_encoded env x f (g x)) :
    (list_map p f).computes_at_encoded env (l.map g) := by
  unfold list_map
  -- TODO simplify proof
  have h_fold : (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty p).computes_at_encoded
      env (l.foldl (fun acc el => g el :: acc) []) := by
    apply PB.fold_computes_at_encoded (a := ([] : List β)) (f := fun acc el => g el :: acc)
      (by simp [PB.computes_at_encoded, DataEncode.encode]) h
    intro acc el ext
    have h_acc : PB.computes_at
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el])
        (PB.atSlot (env.length + ext.length)) (DataEncode.encode acc) := by
      simpa using (PB.atSlot_last_computes_at (env := env) (ext := ext)
        (d := DataEncode.encode acc)).extend (ext := [DataEncode.encode el])
    have h_fel : (f (PB.atSlot (env.length + ext.length + 1))).computes_at_encoded
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) (g el) := by
      simpa [List.append_assoc] using hf el (ext ++ [DataEncode.encode acc])
    simpa [DataEncode.encode, Data.asList] using PB.cons_computes_at h_fel h_acc
  have h_rev := reverse_computes h_fold
  have h_eq : (l.foldl (fun acc el => g el :: acc) []).reverse = l.map g := by
    rw [show l.foldl (fun acc el => g el :: acc) []
          = (l.map g).foldl (fun acc el => el :: acc) [] from
        (List.foldl_map (f := g) (g := fun acc el => el :: acc) (l := l) (init := [])).symm]
    simp
  rwa [h_eq] at h_rev

/-- Discards the `none` elements of a list of options, keeping the `some` payloads. -/
def list_reduceOption (x : PB) : PB :=
  reverse (PB.fold
    (fun acc el => PB.optionElim el acc (fun y => PB.cons y acc))
    PB.empty x)

lemma list_reduceOption_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List (Option α)}
    (h : p.computes_at_encoded env l) :
    (list_reduceOption p).computes_at_encoded env l.reduceOption := by
  unfold list_reduceOption
  set step : List α → Option α → List α :=
    fun acc el => match el with | none => acc | some y => y :: acc with step_def
  -- Convert `reduceOption` to the foldl form of `step` (with reversed accumulator). We need
  -- this generalized over the initial accumulator so the induction goes through.
  have h_eq : ∀ (xs : List (Option α)) (init : List α),
      (xs.foldl step init).reverse = init.reverse ++ xs.reduceOption := by
    intro xs
    induction xs with
    | nil => intro init; simp [List.reduceOption]
    | cons hd tl ih =>
      intro init
      cases hd with
      | none => simpa [step_def] using ih init
      | some y =>
        have h1 : List.foldl step init (some y :: tl) = List.foldl step (y :: init) tl := by
          simp [step_def]
        rw [h1, ih (y :: init)]
        simp [List.reduceOption]
  have h_fold : (PB.fold
        (fun acc el => PB.optionElim el acc (fun y => PB.cons y acc)) PB.empty p
      ).computes_at_encoded env (l.foldl step []) := by
    apply PB.fold_computes_at_encoded
      (a := ([] : List α)) (f := step)
      (by simp [PB.computes_at_encoded, DataEncode.encode]) h
    intro acc el ext
    have h_el : (PB.atSlot (env.length + ext.length + 1)).computes_at_encoded
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) el := by
      simpa [PB.computes_at_encoded] using
        (PB.atSlot_last_computes_at (ext := ext ++ [DataEncode.encode acc])).extend
    have h_acc : (PB.atSlot (env.length + ext.length)).computes_at_encoded
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) acc := by
      simpa [PB.computes_at_encoded] using
        (PB.atSlot_last_computes_at (env := env) (ext := ext)
          (d := DataEncode.encode acc)).extend (ext := [DataEncode.encode el])
    cases el with
    | none =>
      simpa [step_def] using
        PB.optionElim_computes_none (α := α) h_el h_acc
    | some y =>
      refine PB.optionElim_computes_some (α := α) h_el ?_
      intro ext'
      -- Inside someCase, the bound `y` lives at slot
      -- `env.length + ext.length + 2 + ext'.length`; `acc` is still at `env.length + ext.length`.
      set ext_inner :=
        ext ++ [DataEncode.encode acc, DataEncode.encode (some y)] ++ ext' with ext_inner_def
      have hlen : ext_inner.length = ext.length + 2 + ext'.length := by
        simp [ext_inner_def, Nat.add_comm, Nat.add_left_comm]
      have h_y :
          PB.computes_at (env ++ ext_inner ++ [DataEncode.encode y])
            (PB.atSlot (env.length + ext.length + 2 + ext'.length))
            (DataEncode.encode y) := by
        have h := PB.atSlot_last_computes_at
          (env := env) (ext := ext_inner) (d := DataEncode.encode y)
        rw [hlen] at h
        convert h using 2
        omega
      have h_acc' :
          PB.computes_at (env ++ ext_inner ++ [DataEncode.encode y])
            (PB.atSlot (env.length + ext.length)) (DataEncode.encode acc) := by
        have h := (h_acc :
          PB.computes_at (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode (some y)])
            _ (DataEncode.encode acc)).extend (ext := ext' ++ [DataEncode.encode y])
        simpa [ext_inner_def, List.append_assoc] using h
      have h_cons := PB.cons_computes_at h_y h_acc'
      simp only [ext_inner_def] at h_cons
      simpa [step_def, DataEncode.encode, Data.asList, List.append_assoc] using h_cons
  have h_rev := reverse_computes h_fold
  have h_eq₀ : (l.foldl step []).reverse = l.reduceOption := by simpa using h_eq l []
  rwa [h_eq₀] at h_rev

def list_head_option (input : PB) : PB :=
  PB.elim input PB.empty (fun hd _tl => PB.some hd)

lemma list_head_option_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List α}
    (h : p.computes_at_encoded env l) :
    (list_head_option p).computes_at_encoded env l.head? := by
  cases l with
  | nil =>
    apply PB.elim_nil_computes_at (em := PB.empty)
    · simpa [DataEncode.encode] using h
    · simp [DataEncode.encode]
  | cons hd tl =>
    apply PB.elim_cons_computes_at (head := DataEncode.encode hd)
      (tail := tl.map DataEncode.encode)
    · simpa [DataEncode.encode] using h
    · intro ext
      simpa [DataEncode.encode] using
        PB.cons_computes_at PB.elim_cons_head_var_computes_at PB.empty_computes_at

def string_to_tape (input : PB) : PB :=
  to_pair (list_head_option input) (to_pair .empty (list_map input.tail PB.some))

lemma string_to_tape_computes {env : List Data} {p_input : PB} {input : List Symbol}
    (h_input : p_input.computes_at_encoded env input) :
    (string_to_tape p_input).computes_at_encoded env (BiTape.mk₁ input) := by
  have h_tail : (PB.tail p_input).computes_at_encoded env input.tail := by
    simpa [PB.computes_at_encoded, DataEncode.encode] using PB.tail_computes_at h_input
  have h_map : (list_map (PB.tail p_input) PB.some).computes_at_encoded env
      (StackTape.map_some input.tail : Turing.StackTape Symbol) := by
    simpa [PB.computes_at_encoded, DataEncode.encode]
      using list_map_computes h_tail (fun _ _ => by
        simpa [DataEncode.encode] using
          PB.cons_computes_at PB.atSlot_last_computes_at PB.empty_computes_at)
  have h_empty : (PB.empty : PB).computes_at_encoded env (∅ : Turing.StackTape Symbol) := by
    simp [PB.computes_at_encoded, DataEncode.encode]
  simpa [PB.computes_at_encoded, encode_biTape, BiTape.mk₁, DataEncode_pair, string_to_tape]
    using to_pair_computes (list_head_option_computes h_input)
      (to_pair_computes h_empty h_map)


def initial_config (q₀ : PB) (input : PB) : PB :=
  to_pair (PB.some q₀) (string_to_tape input)

/-- Turn the final config to an output, by taking the head and the right part of the tape
    and discarding the blank (`none`) cells. -/
def final_config_to_output (cfg : PB) : PB :=
  list_reduceOption (PB.cons (bitape_head cfg.snd) (bitape_right cfg.snd))

/-- Implements a universal Single-Tape TM, assuming that the input contains the following:
((initialState, transitionFunction), input).
If it terminates, the output is the tape contents under the head and to its right. -/
def universal_tm (input : PB) :=
  final_config_to_output
    (tm_main_loop input.fst.snd (initial_config input.fst.fst input.snd))

lemma initial_config_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p_q₀ p_input : PB} {input : List Symbol}
    (h_q₀ : p_q₀.computes_at_encoded env tm.q₀)
    (h_input : p_input.computes_at_encoded env input) :
    (initial_config p_q₀ p_input).computes_at_encoded env (tm.initCfg input) := by
  -- `tm.initCfg input = ⟨some tm.q₀, BiTape.mk₁ input⟩`, and `encode` on `Cfg` goes
  -- through the `(state, BiTape)` pair, so this matches `to_pair`.
  exact to_pair_computes (PB.some_computes_at_encoded h_q₀) (string_to_tape_computes h_input)

lemma final_config_to_output_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p_cfg : PB} {cfg : tm.Cfg}
    (h_cfg : p_cfg.computes_at_encoded env cfg) :
    (final_config_to_output p_cfg).computes_at_encoded env
      (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption := by
  unfold final_config_to_output
  have h_BiTape : (p_cfg.snd).computes_at_encoded env cfg.BiTape :=
    PB.snd_computes_at_encoded (a := (cfg.state, cfg.BiTape)) h_cfg
  have h_head := bitape_head_computes h_BiTape
  have h_right := bitape_right_computes h_BiTape
  -- The inner `cons` builds the encoding of `head :: right.toList` (a `List (Option Symbol)`),
  -- then `list_reduceOption` discards the blanks.
  have h_list : (PB.cons (bitape_head p_cfg.snd) (bitape_right p_cfg.snd)).computes_at_encoded env
      (cfg.BiTape.head :: cfg.BiTape.right.toList) := by
    change PB.computes_at env _ (DataEncode.encode (cfg.BiTape.head :: cfg.BiTape.right.toList))
    simpa [DataEncode.encode, Data.asList] using PB.cons_computes_at h_head h_right
  exact list_reduceOption_computes h_list

lemma universal_tm_computes [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {input : List Symbol}
    (h_input : p_input.computes_at_encoded env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       input))
    (h_halts : ∃ n,
        ((fun c => (tm.step c).getD c)^[n] (tm.initCfg input)).state = none) :
    (universal_tm p_input).computes_at_encoded env
      (let cfg := (fun c => (tm.step c).getD c)^[Nat.find h_halts] (tm.initCfg input)
       (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption) := by
  unfold universal_tm
  have h_fst := PB.fst_computes_at_encoded h_input
  have h_q₀ := PB.fst_computes_at_encoded h_fst
  have h_tr := PB.snd_computes_at_encoded h_fst
  have h_inp := PB.snd_computes_at_encoded h_input
  exact final_config_to_output_computes
    (tm_main_loop_computes h_tr (initial_config_computes h_q₀ h_inp) h_halts)

/-- The output of reading the tape from `BiTape.mk₁ l` (head + right, then discarding
blanks) recovers `l`. -/
private lemma reduceOption_mk₁_tape {Symbol : Type} (l : List Symbol) :
    ((BiTape.mk₁ l).head :: (BiTape.mk₁ l).right.toList).reduceOption = l := by
  have h : ∀ xs : List Symbol, (xs.map Option.some).reduceOption = xs := fun xs => by
    induction xs with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  cases l <;> simp [BiTape.mk₁, Turing.StackTape.map_some_toList, h]

/-- For a `SingleTapeTM` `tm` and any input `w`, if `tm` outputs `w'` on input `w`,
then the universal Turing machine `universal_tm`, when given an encoding of `tm`
together with `w`, computes `w'`.

The encoded input has the shape `((tm.q₀, transitionTable), w)`, where
`transitionTable` enumerates `tm.tr` over all `(state, head symbol)` pairs. -/
theorem universal_tm_simulates [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {w w' : List Symbol}
    (h_input : p_input.computes_at_encoded env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w))
    (h_out : tm.Outputs w w') :
    (universal_tm p_input).computes_at_encoded env w' := by
  -- Lift `tm.step` to a total step function; halting states are fixed points.
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with hstep
  have halt_fix : ∀ {c : tm.Cfg}, c.state = none → step c = c := by
    rintro ⟨_, _⟩ rfl; rfl
  have halt_fix_iter : ∀ (k : ℕ) {c : tm.Cfg}, c.state = none → step^[k] c = c := by
    intro k _ hc
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, halt_fix hc]
  -- Convert `ReflTransGen` into an explicit step count via tail-induction.
  obtain ⟨n, hn⟩ : ∃ n, step^[n] (tm.initCfg w) = tm.haltCfg w' := by
    induction h_out with
    | refl => exact ⟨0, rfl⟩
    | tail _ h' ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply', hn]
      show (tm.step _).getD _ = _
      rw [show tm.step _ = some _ from h']; rfl
  -- The halting hypothesis required by `universal_tm_computes`.
  have h_halts : ∃ k, (step^[k] (tm.initCfg w)).state = none := ⟨n, by rw [hn]⟩
  -- Determinism + stationarity: `Nat.find` of the halt index also reaches `haltCfg w'`.
  have h_find : step^[Nat.find h_halts] (tm.initCfg w) = tm.haltCfg w' := by
    have h_le : Nat.find h_halts ≤ n := Nat.find_le (by rw [hn])
    have h_iter := halt_fix_iter (n - Nat.find h_halts) (Nat.find_spec h_halts)
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h_le, hn] at h_iter
    exact h_iter.symm
  -- Conclude via `universal_tm_computes`.
  have h := universal_tm_computes (tm := tm) h_input h_halts
  rw [show ((fun c => (tm.step c).getD c)^[Nat.find h_halts] (tm.initCfg w)) =
    tm.haltCfg w' from h_find] at h
  simpa [SingleTapeTM.haltCfg, reduceOption_mk₁_tape] using h

end RoseTreeMachine

end Turing
