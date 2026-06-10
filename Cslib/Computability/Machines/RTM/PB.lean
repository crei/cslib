/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Prog
public import Cslib.Computability.Machines.RTM.DataEncode

/-! # RoseTreeMachine — PB (program builder)

A thin builder layer over the de-Bruijn-levelled `Prog`.
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
def fn (body : PB → PB) : PB := fun n => .fn (body (var n) (n + 1))
def app (f a : PB) : PB := fun n => .app (f n) (a n)
def elim (v em : PB) (cs : PB → PB → PB) : PB := fun n =>
  .elim (v n) (em n) (.fn (.fn (cs (var n) (var (n + 1)) (n + 2))))
def ifEq (x y then_ else_ : PB) : PB := fun n => .ifEq (x n) (y n) (then_ n) (else_ n)
def while_ (init : PB) (body : PB → PB) : PB := fun n =>
  .while_ (init n) (.fn (body (var n) (n + 1)))

/-- Close a builder into a concrete `Prog`. -/
def build (p : PB) : Prog := p 0


variable {env : List Value}

/-! ### Resource-erased (`ProgSem`-based) semantics for program builders

`PB.computes env impl out` says that, under any outer extension `ext`, the builder unfolded at
the current variable depth `(env ++ ext).length` evaluates (via `ProgSem`) to the first-order
value `out` for *some* time and space. The first-order environment `env : List Data` is lifted
into the value space via `Value.data`. The `∀ ext` quantifier lets a builder be plugged into a
binder body where the environment later grows. -/

/-- Resource-erased relational semantics of a program builder. -/
def Computes (env : List Value) (impl : PB) (out : Value) : Prop :=
  ∀ ext : List Value,
    ∃ t s, ProgSem (env ++ ext) (impl (env.length + ext.length))
      out t s

/-- The basic per-env consequence, instantiating `ext := []`. -/
lemma Computes.here {impl : PB} {out : Value}
    (h : Computes env impl out) :
    ∃ t s, ProgSem env (impl env.length) out t s := by
  simpa using h []

/-- `Computes` is preserved when the environment is extended with extra trailing bindings:
the trailing bindings are invisible to a program that only reaches into `env`. -/
lemma Computes.extend {impl : PB} {out : Value} (more : List Value)
    (h : Computes env impl out) :
    Computes (env ++ more) impl out := by
  intro ext
  simpa [List.append_assoc, List.length_append, Nat.add_assoc] using h (more ++ ext)

/-- Variant of `Computes.extend` matching the left-associated environment shape `env ++ a ++ b`
produced by the eliminator combinators. -/
lemma Computes.extend_append {impl : PB} {out : Value} (a b : List Value)
    (h : Computes env impl out) :
    Computes (env ++ a ++ b) impl out := by
  rw [List.append_assoc]; exact h.extend (a ++ b)

/-- Analogon of `Computes`, but as a statement of the pre-encoded value.
This allows statements that `PB`s compute functions on lean datatypes. -/
def ComputesEnc {α : Type} [DataEncode α] (env : List Value) (impl : PB) (x : α) :=
  Computes env impl (.data (DataEncode.encode x))

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

@[simp]
lemma empty_computes : Computes env empty (.data (.l [])) := by
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

/-- The code in `body` computes a function of one argument `x` and returns `out`. -/
def computesFun₁ (env : List Value) (x : Value) (body : PB → PB) (out : Value) : Prop :=
  ∀ ext : List Value, ∃ t s, ProgSem (env ++ ext ++ [x])
    (body (PB.var (env.length + ext.length)) (env.length + ext.length + 1))
    out t s

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
