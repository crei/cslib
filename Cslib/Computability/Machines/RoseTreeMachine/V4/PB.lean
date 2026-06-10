/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.Prog

/-! # RoseTreeMachine V4 — PB (program builder)

A thin builder layer over the de-Bruijn-levelled `Prog`. Because V4 has a single binder
(`fn`), the builder needs exactly one HOAS combinator, `PB.fn`; every other construct is a
trivial structural lift. The env-extending binders `elim`/`while_` keep the *same ergonomic
HOAS signatures* as in the first-order development, but now emit the in-place functional form
(`fn`/`fn (fn …)`), so existing program-construction code ports almost verbatim while
compiling to the functional language.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

/-- A program builder: given the current binder depth (the size of `env` at the point of
insertion), produce a `Prog`. -/
abbrev PB := ℕ → Prog

namespace PB

/-- Reference the variable at (absolute) de Bruijn level `i`. -/
def var (i : ℕ) : PB := fun _ => .var i
/-- The empty rose tree. -/
def empty : PB := fun _ => .empty
/-- Prepend `h` to the list `t`. -/
def cons (h t : PB) : PB := fun n => .cons (h n) (t n)
/-- The single HOAS binder: build an abstraction whose bound variable is supplied to `body`.
The bound variable lives at the current depth `n`; the body is built at depth `n + 1`. -/
def fn (body : PB → PB) : PB := fun n => .fn (body (var n) (n + 1))
/-- Function application. -/
def app (f a : PB) : PB := fun n => .app (f n) (a n)
/-- `elim v em cs`: eliminate the list value of `v`; on `[]` run `em`, otherwise bind the
`head` and `tail` and run `cs head tail`. The branch is emitted as the in-place curried
function `fn (fn …)`. -/
def elim (v em : PB) (cs : PB → PB → PB) : PB := fun n =>
  .elim (v n) (em n) (.fn (.fn (cs (var n) (var (n + 1)) (n + 2))))
/-- `while_ init body`: iterate `body` over the accumulator. The body is emitted as the
in-place one-argument function `fn …`. -/
def while_ (init : PB) (body : PB → PB) : PB := fun n =>
  .while_ (init n) (.fn (body (var n) (n + 1)))

/-- Close a builder into a concrete `Prog`. -/
def build (p : PB) : Prog := p 0

end PB

/-! ### Resource-erased (`ProgSem`-based) semantics for program builders

`PB.computes env impl out` says that, under any outer extension `ext`, the builder unfolded at
the current variable depth `(env ++ ext).length` evaluates (via `ProgSem`) to the first-order
value `out` for *some* time and space. The first-order environment `env : List Data` is lifted
into the value space via `Value.data`. The `∀ ext` quantifier lets a builder be plugged into a
binder body where the environment later grows. -/

/-- Resource-erased relational semantics of a program builder. -/
def PB.computes (env : List Data) (impl : PB) (out : Data) : Prop :=
  ∀ ext : List Data,
    ∃ t s, ProgSem ((env ++ ext).map Value.data) (impl (env.length + ext.length))
      (.data out) t s

/-- The basic per-env consequence, instantiating `ext := []`. -/
lemma PB.computes.here {env : List Data} {impl : PB} {out : Data}
    (h : PB.computes env impl out) :
    ∃ t s, ProgSem (env.map Value.data) (impl env.length) (.data out) t s := by
  simpa using h []

/-- Var-lookup: `PB.var i` reads the `i`-th entry of the environment. -/
@[simp]
lemma PB.var_computes {env : List Data} {i : ℕ} (h : i < env.length) :
    PB.computes env (PB.var i) env[i] := by
  intro ext
  simp only [PB.var]
  have hval : ((env ++ ext).map Value.data)[i]?.getD Value.empty = Value.data env[i] := by
    rw [List.getElem?_map, List.getElem?_append_left h, List.getElem?_eq_getElem h]
    rfl
  exact ⟨_, _, hval ▸ ProgSem.var⟩

@[simp]
lemma PB.empty_computes {env : List Data} :
    PB.computes env PB.empty (Data.l []) := by
  intro ext
  exact ⟨2, 2, ProgSem.empty⟩

@[simp]
lemma PB.cons_computes {env : List Data} {h t : PB} {dh dt : Data}
    (hh : PB.computes env h dh) (ht : PB.computes env t dt) :
    PB.computes env (PB.cons h t) (Data.l (dh :: dt.asList)) := by
  intro ext
  obtain ⟨th, sh, hh'⟩ := hh ext
  obtain ⟨tt, st, ht'⟩ := ht ext
  exact ⟨_, _, ProgSem.cons hh' ht'⟩

/-- A `PB.var` at the absolute level of the `j`-th freshly-bound variable reads `binds[j]`. -/
@[simp]
lemma PB.var_computesFun {env binds : List Data} {j : ℕ} (ext : List Data) :
    ∃ t s, ProgSem ((env ++ ext ++ binds).map Value.data)
      (.var (env.length + ext.length + j)) (.data (binds[j]?.getD (Data.l []))) t s := by
  have hval : ((env ++ ext ++ binds).map Value.data)[env.length + ext.length + j]?.getD Value.empty
      = Value.data (binds[j]?.getD (Data.l [])) := by
    rw [List.getElem?_map]
    have e1 : env.length + ext.length + j = (env ++ ext).length + j := by
      simp [List.length_append]
    rw [e1, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    cases binds[j]? <;> rfl
  exact ⟨_, _, hval ▸ ProgSem.var⟩

/-- The code in `body` computes a function of two arguments `x`, `y` and returns `out`. -/
def PB.computesFun₂ (env : List Data) (x y : Data) (body : PB → PB → PB) (out : Data) : Prop :=
  ∀ ext : List Data, ∃ t s, ProgSem ((env ++ ext ++ [x, y]).map Value.data)
    (body (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
      (env.length + ext.length + 2))
    (.data out) t s

/-- The code in `body` computes a function of one argument `x` and returns `out`. -/
def PB.computesFun₁ (env : List Data) (x : Data) (body : PB → PB) (out : Data) : Prop :=
  ∀ ext : List Data, ∃ t s, ProgSem ((env ++ ext ++ [x]).map Value.data)
    (body (PB.var (env.length + ext.length)) (env.length + ext.length + 1))
    (.data out) t s

/-- `elim`, nil branch: `v` computes `[]`, so the empty branch `em` runs. -/
@[simp]
lemma PB.elim_nil_computes {env : List Data} {v em : PB} {cs : PB → PB → PB} {out : Data}
    (hv : PB.computes env v (Data.l []))
    (hem : PB.computes env em out) :
    PB.computes env (PB.elim v em cs) out := by
  intro ext
  obtain ⟨tv, sv, hv'⟩ := hv ext
  obtain ⟨tem, sem, hem'⟩ := hem ext
  simp only [PB.elim]
  exact ⟨_, _, ProgSem.elim_nil hv' hem'⟩

/-- `elim`, cons branch: `v` computes `head :: tail`, so the curried branch `cs` is applied to
`head` and then to `tail` (each application running an `fn` body in the extended environment). -/
@[simp]
lemma PB.elim_cons_computes {env : List Data} {v em : PB} {cs : PB → PB → PB}
    {head : Data} {tail : List Data} {out : Data}
    (hv : PB.computes env v (Data.l (head :: tail)))
    (hcs : PB.computesFun₂ env head (Data.l tail) cs out) :
    PB.computes env (PB.elim v em cs) out := by
  intro ext
  obtain ⟨tv, sv, hv'⟩ := hv ext
  obtain ⟨tr, sr, hb⟩ := hcs ext
  simp only [PB.elim]
  have hmap : ((env ++ ext).map Value.data ++ [Value.data head]) ++ [Value.data (Data.l tail)]
      = (env ++ ext ++ [head, Data.l tail]).map Value.data := by
    simp
  have hb' : ProgSem
      (((env ++ ext).map Value.data ++ [Value.data head]) ++ [Value.data (Data.l tail)])
      (cs (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
        (env.length + ext.length + 2))
      (.data out) tr sr := by
    rw [hmap]; exact hb
  exact ⟨_, _, ProgSem.elim_cons hv' ProgSem.fn (AppSem.mk ProgSem.fn) (AppSem.mk hb')⟩

/-- In-place application of a literal abstraction (a `let` binding): if `arg` computes `dx`
and `body` computes `out` with its parameter bound to `dx`, then `app (fn body) arg` computes
`out`. -/
lemma PB.app_fn_computes {env : List Data} {body : PB → PB} {arg : PB} {dx out : Data}
    (harg : PB.computes env arg dx)
    (hbody : PB.computesFun₁ env dx body out) :
    PB.computes env (PB.app (PB.fn body) arg) out := by
  intro ext
  obtain ⟨ta, sa, ha⟩ := harg ext
  obtain ⟨tb, sb, hb⟩ := hbody ext
  simp only [PB.app, PB.fn]
  have hmap : (env ++ ext).map Value.data ++ [Value.data dx]
      = (env ++ ext ++ [dx]).map Value.data := by
    simp
  have hb' : ProgSem ((env ++ ext).map Value.data ++ [Value.data dx])
      (body (PB.var (env.length + ext.length)) (env.length + ext.length + 1))
      (.data out) tb sb := by
    rw [hmap]; exact hb
  exact ⟨_, _, ProgSem.app ProgSem.fn ha (AppSem.mk hb')⟩

end V4

end RoseTreeMachine

end Turing
