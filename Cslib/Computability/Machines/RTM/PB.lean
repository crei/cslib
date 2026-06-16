/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Prog
public import Cslib.Computability.Machines.RTM.DataEncode

/-! # Program builder for rose tree machines

This is a thin layer over the `Prog`s of rose tree machines, allowing to better
handle the absolute de-Bruijn levels of variables in `Prog`s.
It contains the main atoms and combinators for constructing rose tree machines.

The main idea is that a `PB` (program builder) receives the current variable depth as an argument
and then returns a `Prog` that may refer to variables at that depth or below.

Furthermore, this file contains routines to help reason about the semantics of constructed
programs both in terms of computations on `Data` but also in terms of computations on arbitrary
lean types that implement` DataEncode`.


## Main definitions and notations

The atoms and combinators mirroring the constructors of `Prog`:
- `PB.var i` - read the `i`-th variable from the environment
- `PB.empty` - the empty list `[]`
- `PB.cons h t` - cons the head `h` and tail `t` into a list
- `PB.elim v em cs` - elimination of `v` into a nil branch `em` and a curried cons branch `cs`
- `PB.ifEq x y then_ else_` - if-then-else on the equality of `x` and `y`
- `PB.while_ init body` - a `while` loop with initializer `init` and body `body`, the body receives
  a builder for the loop body, which is passed the fresh variable for the accumulator
- `PB.fn body` - a literal abstraction (a `let` binding), the body receives a builder for the
  function body, which is passed the fresh variable for the parameter
- `PB.app f a` - application of `f` to `a`

Semantics:

- `PB.Computes` - resource-erased relational semantics for the program builder
- `PB.ComputesEnc` - variant of `PB.Computes` for `DataEncode`-able types.

Resource consumption:

- `PB.OutputsOSize` - the output size of the program is linear in the size of the input environment
- `PB.UsesOTime` - the time used by the program is linear in the size of the input environment
- `PB.UsesOSpace` - the space used by the program is linear in the size of the input environment
- `PB.UsesLinearTimeAndSpace` - the program uses linear time and space in the size of the input

-/


@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- A program builder: given the current binder depth (the size of `env` at the point of
insertion), produce a `Prog`. -/
abbrev PB := ℕ → Prog

namespace PB

def var (i : ℕ) : PB := fun _ => .var i
def empty : PB := fun _ => .empty
def cons (h t : PB) : PB := fun n => .cons (h n) (t n)
def elim (v em : PB) (cs : PB → PB → PB) : PB := fun n =>
  .elim (v n) (em n) (.fn (.fn (cs (var n) (var (n + 1)) (n + 2))))
def ifEq (x y then_ else_ : PB) : PB := fun n => .ifEq (x n) (y n) (then_ n) (else_ n)
def while_ (init : PB) (body : PB → PB) : PB := fun n =>
  .while_ (init n) (.fn (body (var n) (n + 1)))
def fn (body : PB → PB) : PB := fun n => .fn (body (var n) (n + 1))
def app (f a : PB) : PB := fun n => .app (f n) (a n)

/-- Close a builder into a concrete `Prog`. -/
def build (p : PB) : Prog := p 0

/-- A proof that a `PB` that takes another `PB` as input computes a certain value.
This is mainly used for final results. During composition, `computesFun₁` is more useful
since it allows capturing the environment. -/
def ComputesFunInTimeAndSpace (p : PB → PB) (input output : Data) (t s : ℕ) : Prop :=
  ∀ env, ProgSem (env ++ [.data input]) (p (PB.var env.length) (env.length + 1))
    (.data output) t s

/-- The `PB → PB` analogue of `Prog.ComputesInTimeAndSpace`: viewing `p` as a transformation from
an argument builder to a result builder, `p` computes `output` from `input` using `t` time and `s`
space. The input is supplied as the last entry of the environment and read back through a variable,
and the `∀ env` makes the statement hold under any outer environment (so it can be plugged into a
larger program). -/
def ComputesInTimeAndSpace (p : PB → PB) (input output : Data) (t s : ℕ) : Prop :=
  ∀ env, ProgSem (env ++ [.data input]) (p (PB.var env.length) (env.length + 1))
    (.data output) t s

/-- Encoded form of `ComputesInTimeAndSpace`: `p` maps a value encoding `input : α` to one encoding
`output : β`, using `t` time and `s` space. -/
def ComputesEncInTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
    (p : PB → PB) (input : α) (output : β) (t s : ℕ) : Prop :=
  ComputesInTimeAndSpace p (DataEncode.encode input) (DataEncode.encode output) t s

/-- Code that computes a value of type `α` (given the current variable depth), bundled with its
semantics.
TODO also bundle resource usage. -/
structure Routine (α : Type) [DataEncode α] where
  /-- The code -/
  impl (depth : ℕ) : Prog
  /-- A condition on the input under which we make a statement about the semantics. -/
  valid : List Value → Prop := fun _ => True
  /-- The computed value together with a proof that the code computes it. -/
  sem (env : List Value) (h : valid env) :
    -- { v : α // ∀ ext : List Value, -- TODO do we need `ext`?
    --   ∃ t s, ProgSem (env ++ ext) (impl (env.length + ext.length))
    --     (.data (DataEncode.encode v)) t s }
    { v : α // ∃ t s, ProgSem env (impl env.length) (.data (DataEncode.encode v)) t s }

def Routine.var (i : ℕ) : Routine Data where
  impl : PB := PB.var i
  valid env := match env[i]? with | some (.data _) => true | _ => false
  sem env h := ⟨match env[i]? with | some (.data d) => d | _ => Data.empty, sorry⟩

variable {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]

def Routine.varEncoded (i : ℕ) : Routine α where
  impl : PB := PB.var i
  valid env := ∃ x : α, some (.data (DataEncode.encode x)) = env[i]?
  sem env h := match env[i]? with
    | some (.data x) => DataEncode.decode x
    |
   -- TODO use decode here?
    sorry --⟨match env[i]? with | some (.data d) => d | _ => Data.empty, sorry⟩


def Routine.empty : Routine Data where
  impl := PB.empty
  sem _ _ := ⟨.l [], ⟨_, _, ProgSem.empty⟩⟩

def Routine.elim (v : Routine Data) (em : Routine Data)
    (cs : Routine Data → Routine Data → Routine Data) : Routine Data where
  impl n := .elim (v.impl n) (em.impl n) (.fn (.fn ((cs (var n) (var (n + 1))).impl (n + 2))))
  valid env := ∃ h : v.valid env, (match (v.sem env h).val with
    | .l [] => em.valid env
    | .l (hd :: tl) => (cs (Routine.var env.length) (Routine.var (env.length + 1))).valid
        (env ++ [.data hd, .data (Data.l tl)]))
  sem env h := match h_v : (v.sem env h.1).val with
    | .l [] =>
      have h_em_valid := by simp [h_v] at h; exact h.right
      ⟨em.sem env h_em_valid,
        by
        obtain ⟨_, _, h_v'⟩ := (v.sem env h.1).property
        rw [h_v] at h_v'
        obtain ⟨_, _, h_em⟩ := (em.sem env h_em_valid).property
        exact ⟨_, _, ProgSem.elim_nil h_v' h_em⟩⟩
    | .l (hd :: tl) =>
      have h_cs_valid := by simp [h_v] at h; exact h.right
      ⟨(cs (Routine.var env.length) (Routine.var (env.length + 1))).sem
        (env ++ [.data hd, .data (Data.l tl)]) h_cs_valid,
        by
        obtain ⟨_, _, h_v'⟩ := (v.sem env h.1).property
        rw [h_v] at h_v'
        obtain ⟨t_cs, s_cs, h_cs⟩ :=
          ((cs (Routine.var env.length) (Routine.var (env.length + 1))).sem
            (env ++ [.data hd, .data (Data.l tl)]) h_cs_valid).property
        exact ⟨_, _, ProgSem.elim_cons h_v' ProgSem.fn ⟨ProgSem.fn⟩ ⟨by
          rw [List.append_assoc]
          rw [show env.length + 2 = (env ++ [_, _]).length from by simp]
          exact h_cs⟩⟩⟩


def Routine.ifEq {α β : Type} [DataEncode α] [DecidableEq α] [DataEncode β]
    (x y : Routine α) (then_ else_ : Routine β) : Routine β where
  impl n := .ifEq (x.impl n) (y.impl n) (then_.impl n) (else_.impl n)
  valid env := ∃ h_x : x.valid env, ∃ h_y : y.valid env,
    (if (x.sem env h_x).val = (y.sem env h_y).val then
        then_.valid env else else_.valid env)
  sem env h :=
    let r := h.fst


    --let ⟨h_x, h_y⟩ := h
    ⟨if (x.sem env h_x).val = (y.sem env h_y).val then
     then_.sem env sorry else else_.sem env sorry, sorry ⟩


/-- Var-lookup: `PB.var i` reads the `i`-th entry of the environment. -/
@[simp]
lemma var_computes {i : ℕ} (h : i < env.length) :
    Computes env (PB.var i) env[i] := by
  intro ext
  simp only [PB.var]
  have hval : (env ++ ext)[i]?.getD Value.empty = env[i] := by grind
  exact ⟨_, _, hval ▸ ProgSem.var⟩

/-- A freshly-bound first argument: the variable at level `env.length + ext.length` reads the
first of the trailing bindings `v :: binds`. -/
lemma var_computes_fresh {v : Value} (ext binds : List Value) :
    Computes (env ++ ext ++ (v :: binds)) (PB.var (env.length + ext.length)) v := by
  have hlt : env.length + ext.length < (env ++ ext ++ (v :: binds)).length := by
    simp [List.length_append]
  have hget : (env ++ ext ++ (v :: binds))[env.length + ext.length]'hlt = v := by
    rw [List.getElem_append_right (by simp [List.length_append])]
    simp [List.length_append]
  simpa [hget] using var_computes (env := env ++ ext ++ (v :: binds)) hlt

/-- The `j`-th freshly-bound argument: the variable at level `env.length + ext.length + j` reads
`binds[j]` from the trailing bindings `binds`. Generalises `var_computes_fresh` to any position. -/
lemma var_computes_fresh' (ext binds : List Value) {j : ℕ} (hj : j < binds.length) :
    Computes (env ++ ext ++ binds) (PB.var (env.length + ext.length + j)) binds[j] := by
  have hlt : env.length + ext.length + j < (env ++ ext ++ binds).length := by
    simp only [List.length_append]; omega
  have hget : (env ++ ext ++ binds)[env.length + ext.length + j]'hlt = binds[j] := by
    rw [List.getElem_append_right (by simp [List.length_append])]
    simp [List.length_append]
  exact hget ▸ var_computes (env := env ++ ext ++ binds) hlt

/-- A freshly-bound second argument: the variable at level `env.length + ext.length + 1` reads the
second of the trailing bindings `v :: w :: binds`. Specialises `var_computes_fresh'` to `j = 1`. -/
lemma var_computes_fresh2 {v w : Value} (ext binds : List Value) :
    Computes (env ++ ext ++ (v :: w :: binds)) (PB.var (env.length + ext.length + 1)) w := by
  exact var_computes_fresh' ext (v :: w :: binds) (j := 1) (by simp)

@[simp]
lemma empty_computes : Computes env empty (.data (.l [])) := by
  intro ext
  exact ⟨2, 2, ProgSem.empty⟩

@[simp]
lemma empty_computesEnc (α : Type) [DataEncode α] : empty.ComputesEnc env ([] : List α) := by
  intro ext
  exact ⟨2, 2, ProgSem.empty⟩

@[simp]
lemma cons_computes {h t : PB} {dh dt : Data}
    (hh : Computes env h (.data dh)) (ht : Computes env t (.data dt)) :
    Computes env (PB.cons h t) (.data (.l (dh :: dt.asList))) := by
  intro ext
  obtain ⟨th, sh, hh'⟩ := hh ext
  obtain ⟨tt, st, ht'⟩ := ht ext
  exact ⟨_, _, ProgSem.cons hh' ht'⟩

lemma cons_computesEnc {α : Type} [DataEncode α] {p_hd p_tl : PB} {hd : α} {tl : List α}
    (h_hd : p_hd.ComputesEnc env hd) (h_tl : p_tl.ComputesEnc env tl) :
    (PB.cons p_hd p_tl).ComputesEnc env (hd :: tl) := by
  intro ext
  obtain ⟨th, sh, hh'⟩ := h_hd ext
  obtain ⟨tt, st, ht'⟩ := h_tl ext
  exact ⟨_, _, ProgSem.cons hh' ht'⟩

/-- A `PB.var` at the absolute level of the `j`-th freshly-bound variable reads `binds[j]`. -/
@[simp]
lemma var_computesFun {binds : List Value} {j : ℕ} (ext : List Value) :
    ∃ t s, ProgSem (env ++ ext ++ binds)
      (.var (env.length + ext.length + j)) (binds[j]?.getD .empty) t s := by
  have hval : (env ++ ext ++ binds)[env.length + ext.length + j]?.getD Value.empty
      = binds[j]?.getD .empty := by
    have e1 : env.length + ext.length + j = (env ++ ext).length + j := by
      simp [List.length_append]
    rw [e1, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact ⟨_, _, hval ▸ ProgSem.var⟩

/-- The code in `body` computes a function of two arguments `x`, `y` and returns `out`. -/
def computesFun₂ (env : List Value) (x y : Value) (body : PB → PB → PB) (out : Value) : Prop :=
  ∀ ext : List Value, ∃ t s, ProgSem (env ++ ext ++ [x, y])
    (body (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
      (env.length + ext.length + 2))
    out t s

lemma computesFun₂_const {x y : Value} {impl : PB} {out : Value}
    (h : impl.Computes env out) :
    PB.computesFun₂ env x y (fun _ _ => impl) out := by
  intro ext
  simpa [List.append_assoc, Nat.add_assoc] using h (ext ++ [x, y])

/-- To run a one-argument branch `body` on the freshly-bound first argument (ignoring the second
binding), it suffices that `body` applied to the fresh variable computes `out` in the extended
environment. This hides the `Computes.here`/length bookkeeping of `computesFun₂`. -/
lemma computesFun₂_branch {x y : Value} {body : PB → PB} {out : Value}
    (h : ∀ ext, (body (PB.var (env.length + ext.length))).Computes (env ++ ext ++ [x, y]) out) :
    computesFun₂ env x y (fun v _ => body v) out := by
  intro ext
  simpa [List.length_append, Nat.add_assoc] using (h ext).here

/-- Two-argument version of `computesFun₂_branch`: to run a branch `body` that uses both of its
freshly-bound arguments, it suffices that `body` applied to the two fresh variables computes `out`
in the extended environment. This hides the `Computes.here`/length bookkeeping of `computesFun₂`. -/
lemma computesFun₂_branch2 {x y : Value} {body : PB → PB → PB} {out : Value}
    (h : ∀ ext, (body (PB.var (env.length + ext.length))
        (PB.var (env.length + ext.length + 1))).Computes (env ++ ext ++ [x, y]) out) :
    computesFun₂ env x y body out := by
  intro ext
  simpa [List.length_append, Nat.add_assoc] using (h ext).here

/-- The code in `body` computes a function of one argument `x` and returns `out`. -/
def computesFun₁ (env : List Value) (x : Value) (body : PB → PB) (out : Value) : Prop :=
  ∀ ext : List Value, ∃ t s, ProgSem (env ++ ext ++ [x])
    (body (PB.var (env.length + ext.length)) (env.length + ext.length + 1))
    out t s

/-- To run a one-argument body on its freshly-bound argument, it suffices that `body` applied to
the fresh variable computes `out` in the extended environment. This hides the
`Computes.here`/length bookkeeping of `computesFun₁` (the one-argument analogue of
`computesFun₂_branch`). -/
lemma computesFun₁_branch {x : Value} {body : PB → PB} {out : Value}
    (h : ∀ ext, (body (PB.var (env.length + ext.length))).Computes (env ++ ext ++ [x]) out) :
    computesFun₁ env x body out := by
  intro ext
  simpa [List.length_append, Nat.add_assoc] using (h ext).here

/-- `elim`, nil branch: `v` computes `[]`, so the empty branch `em` runs. -/
@[simp]
lemma elim_nil_computes {v em : PB} {cs : PB → PB → PB} {out : Value}
    (hv : Computes env v (.data (.l [])))
    (hem : Computes env em out) :
    Computes env (PB.elim v em cs) out := by
  intro ext
  obtain ⟨tv, sv, hv'⟩ := hv ext
  obtain ⟨tem, sem, hem'⟩ := hem ext
  simp only [PB.elim]
  exact ⟨_, _, ProgSem.elim_nil hv' hem'⟩

/-- `elim`, cons branch: `v` computes `head :: tail`, so the curried branch `cs` is applied to
`head` and then to `tail` (each application running an `fn` body in the extended environment). -/
@[simp]
lemma elim_cons_computes {v em : PB} {cs : PB → PB → PB}
    {head : Data} {tail : List Data} {out : Value}
    (hv : Computes env v (.data (.l (head :: tail))))
    (hcs : computesFun₂ env (.data head) (.data (Data.l tail)) cs out) :
    Computes env (PB.elim v em cs) out := by
  intro ext
  obtain ⟨tv, sv, hv'⟩ := hv ext
  obtain ⟨tr, sr, hb⟩ := hcs ext
  simp only [PB.elim]
  have hmap : ((env ++ ext) ++ [Value.data head]) ++ [Value.data (Data.l tail)]
      = env ++ ext ++ [head, Data.l tail].map Value.data := by
    simp
  have hb' : ProgSem
      (((env ++ ext) ++ [Value.data head]) ++ [Value.data (Data.l tail)])
      (cs (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
        (env.length + ext.length + 2))
      out tr sr := by
    rw [hmap]; exact hb
  exact ⟨_, _, ProgSem.elim_cons hv' ProgSem.fn (AppSem.mk ProgSem.fn) (AppSem.mk hb')⟩

@[simp]
lemma ifeq_eq_computes {x y then_ else_ : PB} {vx : Data} {out : Value}
    (hx : Computes env x (.data vx))
    (hy : Computes env y (.data vx))
    (hthen : Computes env then_ out) :
    Computes env (PB.ifEq x y then_ else_) out := by
  intro ext
  obtain ⟨tx, sx, hx'⟩ := hx ext
  obtain ⟨ty, sy, hy'⟩ := hy ext
  obtain ⟨tthen, sthen, hthen'⟩ := hthen ext
  simp only [PB.ifEq]
  exact ⟨_, _, ProgSem.ifEq_then hx' hy' hthen'⟩


lemma ifeq_eq_computesEnc {α β : Type} [DataEncode α] [DataEncode β]
    {x y then_ else_ : PB} {vx : α} {out : β}
    (hx : ComputesEnc env x vx)
    (hy : ComputesEnc env y vx)
    (hthen : ComputesEnc env then_ out) :
    ComputesEnc env (PB.ifEq x y then_ else_) out := by
  intro ext
  obtain ⟨tx, sx, hx'⟩ := hx ext
  obtain ⟨ty, sy, hy'⟩ := hy ext
  obtain ⟨tthen, sthen, hthen'⟩ := hthen ext
  simp only [PB.ifEq]
  exact ⟨_, _, ProgSem.ifEq_then hx' hy' hthen'⟩

@[simp]
lemma ifeq_ne_computes {x y then_ else_ : PB} {vx vy : Data} {out : Value}
    (hx : Computes env x (.data vx))
    (hy : Computes env y (.data vy))
    (hne : vx ≠ vy)
    (helse : Computes env else_ out) :
    Computes env (PB.ifEq x y then_ else_) out := by
  intro ext
  obtain ⟨tx, sx, hx'⟩ := hx ext
  obtain ⟨ty, sy, hy'⟩ := hy ext
  obtain ⟨telse, selse, helse'⟩ := helse ext
  simp only [PB.ifEq]
  exact ⟨_, _, ProgSem.ifEq_else hx' hy' hne helse'⟩

lemma ifeq_ne_computesEnc {α β : Type} [DataEncode α] [DataEncode β]
    {x y then_ else_ : PB} {vx vy : α} {out : β}
    (hx : ComputesEnc env x vx)
    (hy : ComputesEnc env y vy)
    (hne : vx ≠ vy)
    (helse : ComputesEnc env else_ out) :
    ComputesEnc env (PB.ifEq x y then_ else_) out := by
  intro ext
  obtain ⟨tx, sx, hx'⟩ := hx ext
  obtain ⟨ty, sy, hy'⟩ := hy ext
  obtain ⟨telse, selse, helse'⟩ := helse ext
  simp only [PB.ifEq]
  exact ⟨_, _, ProgSem.ifEq_else hx' hy' (fun heq => hne (DataEncode.h_inj heq)) helse'⟩


/-- In-place application of a literal abstraction (a `let` binding): if `arg` computes `dx`
and `body` computes `out` with its parameter bound to `dx`, then `app (fn body) arg` computes
`out`. -/
lemma app_fn_computes {body : PB → PB} {arg : PB} {dx out : Value}
    (harg : Computes env arg dx)
    (hbody : computesFun₁ env dx body out) :
    Computes env (PB.app (PB.fn body) arg) out := by
  intro ext
  obtain ⟨ta, sa, ha⟩ := harg ext
  obtain ⟨tb, sb, hb⟩ := hbody ext
  simp only [PB.app, fn]
  have hmap : (env ++ ext) ++ [dx]
      = (env ++ ext ++ [dx]) := by
    simp
  have hb' : ProgSem ((env ++ ext) ++ [dx])
      (body (PB.var (env.length + ext.length)) (env.length + ext.length + 1))
      out tb sb := by
    rw [hmap]; exact hb
  exact ⟨_, _, ProgSem.app ProgSem.fn ha (AppSem.mk hb')⟩

/-- Resource-erased iteration of a `while_` loop body. `WhileComputes env body acc r` says that,
under any outer extension `ext`, repeatedly applying the loop-body closure (the closure produced by
`while_ _ body` at the current depth) starting from accumulator `acc` eventually yields `r`.

This mirrors `WhileSem` at the builder level: it has the two introduction rules
`WhileComputes.halt` and `WhileComputes.step`, which together form the case analysis used in
inductive proofs about a `while_` loop. -/
def WhileComputes (env : List Value) (body : PB → PB) (acc r : Data) : Prop :=
  ∀ ext : List Value, ∃ t s,
    WhileSem
      (.closure (body (PB.var (env.length + ext.length)) (env.length + ext.length + 1))
        (env ++ ext))
      acc r t s

/-- Halting case of `WhileComputes`: if the accumulator's head is empty, the loop stops with the
accumulator as result. Mirrors `WhileSem.halt`. -/
lemma WhileComputes.halt {body : PB → PB} {acc : Data}
    (h_stop : acc.asList.head?.getD (Data.l []) = Data.l []) :
    WhileComputes env body acc acc := by
  intro ext
  exact ⟨_, _, WhileSem.halt h_stop⟩

/-- Stepping case of `WhileComputes`: if the accumulator's head is non-empty, applying the body to
`acc` yields `v` (this is exactly a `computesFun₁` for the body run on the freshly-bound argument),
and the loop continues from `v` to `r`, then the whole loop runs from `acc` to `r`. Mirrors
`WhileSem.step`. -/
lemma WhileComputes.step {body : PB → PB} {acc v r : Data}
    (h_cont : acc.asList.head?.getD (Data.l []) ≠ Data.l [])
    (h_body : computesFun₁ env (.data acc) body (.data v))
    (h_rest : WhileComputes env body v r) :
    WhileComputes env body acc r := by
  intro ext
  obtain ⟨tb, sb, hb⟩ := h_body ext
  obtain ⟨tr, sr, hr⟩ := h_rest ext
  exact ⟨_, _, WhileSem.step h_cont (AppSem.mk hb) hr⟩

/-- A `while_` loop computes `r`: evaluate `init` to the starting accumulator `acc`, then iterate
the body via `WhileComputes` from `acc` to `r`. The iteration hypothesis `h_loop` is established by
combining `WhileComputes.halt`/`WhileComputes.step`, typically inside an induction. -/
lemma while_computes {init : PB} {body : PB → PB} {acc r : Data}
    (h_init : Computes env init (.data acc))
    (h_loop : WhileComputes env body acc r) :
    Computes env (PB.while_ init body) (.data r) := by
  intro ext
  obtain ⟨ti, si, hi⟩ := h_init ext
  obtain ⟨tw, sw, hw⟩ := h_loop ext
  simp only [PB.while_]
  exact ⟨_, _, ProgSem.while_ hi ProgSem.fn hw⟩

/-- Recursion principle for building a `WhileComputes`. To show that the loop run from `acc`
produces `result acc`, supply, via a strictly-decreasing measure `μ`:
* `h_halt`: on a halting accumulator (empty head) the result is the accumulator itself;
* `h_step`: on a non-halting accumulator, the body computes a next accumulator `v` (a
  `computesFun₁`), the measure strictly decreases (`μ v < μ acc`, guaranteeing termination), and the
  loop result is preserved (`result v = result acc`).

This packages the `WhileComputes.halt`/`WhileComputes.step` chaining into a single well-founded
recursion, so callers describe one step instead of unrolling the loop. -/
theorem WhileComputes.rec' {body : PB → PB} (μ : Data → ℕ) (result : Data → Data)
    (h_halt : ∀ acc : Data,
      acc.asList.head?.getD (Data.l []) = Data.l [] → result acc = acc)
    (h_step : ∀ acc : Data, acc.asList.head?.getD (Data.l []) ≠ Data.l [] →
      ∃ v : Data, computesFun₁ env (.data acc) body (.data v) ∧
        μ v < μ acc ∧ result v = result acc) :
    ∀ acc : Data, WhileComputes env body acc (result acc) := by
  intro acc
  generalize hn : μ acc = n
  induction n using Nat.strong_induction_on generalizing acc with
  | _ n ih =>
    by_cases h : acc.asList.head?.getD (Data.l []) = Data.l []
    · rw [h_halt acc h]
      exact WhileComputes.halt h
    · obtain ⟨v, hbody, hlt, hres⟩ := h_step acc h
      rw [← hres]
      exact WhileComputes.step h hbody (ih (μ v) (hn ▸ hlt) v rfl)

------------------- Resource Consumption -------------------------

def OutputsOSize (impl : PB) (s : List Value → ℕ) : Prop :=
  ∃ a b, ∀ env, ∃ out,
    impl.Computes env out ∧ out.size ≤ a * (s env) + b

def UsesOTime (impl : PB) (t : List Value → ℕ) : Prop :=
  ∃ a b, ∀ env, ∃ out s, ∃ t' ≤ a * (t env) + b,
    ProgSem env (impl env.length) out t' s

def UsesOSpace (impl : PB) (s : List Value → ℕ) : Prop :=
  ∃ a b, ∀ env, ∃ out t, ∃ s' ≤ a * (s env) + b,
    ProgSem env (impl env.length) out t s'

def UsesLinearTimeAndSpace (impl : PB) : Prop :=
  PB.UsesOTime impl (fun env => (env.map fun x => x.size).sum) ∧
  PB.UsesOSpace impl (fun env => (env.map fun x => x.size).sum)

end PB

end RoseTreeMachine

end Turing
