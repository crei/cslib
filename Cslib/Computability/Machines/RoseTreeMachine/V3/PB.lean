/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V3.Prog
public import Cslib.Computability.Machines.RoseTreeMachine.V3.DataEncode

/-! # RoseTreeMachine V2 — PB

Part of the RoseTreeMachine V2 development; see
`Cslib/Computability/Machines/RoseTreeMachine/V2.lean` for an overview.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- A program builder: given the current binder depth (i.e. the size of `env`
at the point of insertion), produce a `Prog`. -/
abbrev PB := ℕ → Prog

namespace PB

/-- Reference the variable at (absolute) de Bruijn level `i`. -/
def var (i : ℕ) : PB := fun _ => .var i
def empty : PB := fun _ => .empty
def cons (h t : PB) : PB := fun n => .cons (h n) (t n)
def ifEq (a b then_ else_ : PB) : PB := fun n => .ifEq (a n) (b n) (then_ n) (else_ n)
def elim (v em : PB) (cs : PB → PB → PB) : PB := fun n =>
  .elim (v n) (em n) (cs (var n) (var (n + 1)) (n + 2))
def fold (body : PB → PB → PB) (init list : PB) : PB := fun n =>
  .fold (body (var n) (var (n + 1)) (n + 2)) (init n) (list n)
def while_ (init : PB) (body : PB → PB) : PB := fun n =>
  .while_ (init n) (body (var n) (n + 1))

/-- Close a builder into a concrete `Prog`. -/
def build (p : PB) : Prog := p 0


end PB

/-! ### Resource-erased (`ProgSem`-based) semantics for program builders

`PB.computes env impl out` says that, under any outer extension `ext`, the builder
unfolded at the current variable depth `(env ++ ext).length` evaluates (via `ProgSem`) to
`out` for *some* time and space. Time and space bounds are intentionally ignored here; only
the returned value is tracked. The `∀ ext` quantifier lets a builder be plugged into a
binder body where the environment later grows. -/

/-- Resource-erased relational semantics of a program builder. -/
def PB.computes (env : List Data) (impl : PB) (out : Data) : Prop :=
  ∀ ext : List Data,
    ∃ t s, ProgSem (env ++ ext) (impl (env.length + ext.length)) out t s

def PB.computes_enc {α : Type} [DataEncode α] (env : List Data) (x : PB) (a : α) : Prop :=
    PB.computes env x (DataEncode.encode a)

/-- The basic per-env consequence, instantiating `ext := []`. -/
lemma PB.computes.here {env : List Data} {impl : PB} {out : Data}
    (h : PB.computes env impl out) :
    ∃ t s, ProgSem env (impl env.length) out t s := by
  simpa using h []

@[simp]
lemma PB.computes.extend {env ext : List Data} {impl : PB} {d : Data}
    (h : PB.computes env impl d) :
    PB.computes (env ++ ext) impl d := by
  intro ext'
  simpa [List.append_assoc, Nat.add_assoc] using (h (ext ++ ext'))

/-- Var-lookup: `PB.var i` reads the `i`-th entry of the environment. -/
@[simp, grind .]
lemma PB.var_computes {env : List Data} {i : ℕ} (h : i < env.length) :
    PB.computes env (PB.var i) env[i] := by
  intro ext
  refine ⟨env[i].size, env[i].size, ?_⟩
  simp only [PB.var]
  have hval : (env ++ ext)[i]?.getD (Data.l []) = env[i] := by
    rw [List.getElem?_append_left h, List.getElem?_eq_getElem h]
    rfl
  rw [← hval]
  exact ProgSem.var

@[simp, grind .]
lemma PB.empty_computes {env : List Data} :
    PB.computes env PB.empty (Data.l []) := by
  intro ext
  exact ⟨2, 2, ProgSem.empty⟩

@[simp, grind .]
lemma PB.cons_computes {env : List Data} {h t : PB} {dh dt : Data}
    (hh : PB.computes env h dh) (ht : PB.computes env t dt) :
    PB.computes env (PB.cons h t) (Data.l (dh :: dt.asList)) := by
  intro ext
  obtain ⟨th, sh, hh'⟩ := hh ext
  obtain ⟨tt, st, ht'⟩ := ht ext
  exact ⟨_, _, ProgSem.cons hh' ht'⟩

/-- The code in `body` computes a function of one argument and returns `out`. -/
@[simp, grind .]
def PB.computesFun₁ (env : List Data) (x : Data) (body : PB → PB) (out : Data) : Prop :=
  ∀ ext : List Data, ∃ t s, ProgSem
    (env ++ ext ++ [x])
    (body (PB.var (env.length + ext.length))
    (env.length + ext.length + 1))
    out
    t
    s

/-- The code in `body` computes a function of two arguments `x`, `y` and returns `out`. -/
@[simp, grind .]
def PB.computesFun₂ (env : List Data) (x y : Data) (body : PB → PB → PB) (out : Data) : Prop :=
  ∀ ext : List Data, ∃ t s, ProgSem
    (env ++ ext ++ [x, y])
    (body (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
      (env.length + ext.length + 2))
    out
    t
    s

/-- A `PB.var` at the absolute level of the `j`-th freshly-bound variable reads `binds[j]`.
This is the additive lookup used to discharge HOAS branch bodies (see `PB.elim_cons_computes`):
the `j`-th binding introduced after `env ++ ext` sits at level `(env ++ ext).length + j`. -/
@[simp]
lemma PB.var_computesFun {env binds : List Data} {j : ℕ} (ext : List Data) :
    ∃ t s,
      ProgSem (env ++ ext ++ binds) (.var (env.length + ext.length + j))
        (binds[j]?.getD (Data.l [])) t s := by
  refine ⟨(binds[j]?.getD (Data.l [])).size, (binds[j]?.getD (Data.l [])).size, ?_⟩
  have hval : (env ++ ext ++ binds)[env.length + ext.length + j]?.getD (Data.l [])
      = binds[j]?.getD (Data.l []) := by
    have e1 : env.length + ext.length + j = (env ++ ext).length + j := by
      simp only [List.length_append]
    rw [e1, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rw [← hval]
  exact ProgSem.var

/-- Specialisation of `PB.var_computesFun` to the first freshly-bound variable (`j = 0`):
a `PB.var` at the absolute level `(env ++ ext).length` reads `binds[0]`. -/
@[simp]
lemma PB.var_computesFun_zero {env binds : List Data} (ext : List Data) :
    ∃ t s,
      ProgSem (env ++ ext ++ binds) (.var (env.length + ext.length))
        (binds[0]?.getD (Data.l [])) t s := by
  simpa using PB.var_computesFun (j := 0) ext

/-- `elim`, nil branch: `v` computes `[]`, so the empty branch `em` runs. -/
@[simp, grind .]
lemma PB.elim_nil_computes {env : List Data} {v em : PB} {cs : PB → PB → PB} {out : Data}
    (hv : PB.computes env v (Data.l []))
    (hem : PB.computes env em out) :
    PB.computes env (PB.elim v em cs) out := by
  intro ext
  obtain ⟨tv, sv, hv'⟩ := hv ext
  obtain ⟨tem, sem, hem'⟩ := hem ext
  simp only [PB.elim]
  exact ⟨_, _, ProgSem.elim_nil hv' hem'⟩

/-- `elim`, cons branch: `v` computes `head :: tail`, so the body `cs` runs on the env
extended with `[head, Data.l tail]`. -/
@[simp, grind .]
lemma PB.elim_cons_computes {env : List Data} {v em : PB} {cs : PB → PB → PB}
    {head : Data} {tail : List Data} {out : Data}
    (hv : PB.computes env v (Data.l (head :: tail)))
    (hcs : PB.computesFun₂ env head (Data.l tail) cs out) :
    PB.computes env (PB.elim v em cs) out := by
  intro ext
  obtain ⟨tv, sv, hv'⟩ := hv ext
  obtain ⟨tr, sr, hb⟩ := hcs ext
  simp only [PB.elim]
  have hb' : ProgSem (env ++ ext ++ [head, Data.l tail])
      (cs (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
        (env.length + ext.length + 2)) out tr sr := by
    simpa using hb
  exact ⟨_, _, ProgSem.elim_cons hv' hb'⟩

------------------- Resource Consumption -------------------------

-- TODO these are harder to use now because we don't know that the RHS of the
-- relation is unique.

def PB.outputsOSize (impl : PB) (s : List Data → ℕ) : Prop :=
  ∃ a b, ∀ env : List Data, ∃ out,
    PB.computes env impl out ∧ out.size ≤ a * (s env) + b

def PB.usesOTime (impl : PB) (t : List Data → ℕ) : Prop :=
  ∃ a b, ∀ env, ∃ out s, ∃ t' ≤ a * (t env) + b,
    ProgSem env (impl env.length) out t' s

def PB.usesOSpace (impl : PB) (s : List Data → ℕ) : Prop :=
  ∃ a b, ∀ env, ∃ out t, ∃ s' ≤ a * (s env) + b,
    ProgSem env (impl env.length) out t s'

@[simp]
def PB.usesLinearTimeAndSpace (impl : PB) : Prop :=
  PB.usesOTime impl (fun env => (Data.l env).size) ∧
  PB.usesOSpace impl (fun env => (Data.l env).size)



@[simp, grind .]
lemma PB.var_usesOTime {i : ℕ} :
    PB.usesOTime (PB.var i) 1 := by
  use 1, 0
  intro ext
  sorry

@[simp, grind .]
lemma PB.var_usesLinearTimeAndSpace {i : ℕ} :
    PB.usesLinearTimeAndSpace (PB.var i) := by
  sorry



@[simp, grind .]
lemma PB.empty_outputsOSize : PB.outputsOSize PB.empty (fun _ => 1) := by
  use 2, 0
  intro env
  refine ⟨Data.l [], by simp, by simp⟩

@[simp, grind .]
lemma PB.empty_usesOTime : PB.usesOTime PB.empty 1 := by
  use 2, 0
  intro env
  use Data.l [], 2, 2
  simpa using ProgSem.empty

@[simp, grind .]
lemma PB.empty_usesOSpace : PB.usesOSpace PB.empty 1 := by
  use 2, 0
  intro env
  use Data.l [], 2, 2
  simpa using ProgSem.empty

@[simp, grind .]
lemma PB.empty_usesLinearTimeAndSpace : PB.usesLinearTimeAndSpace PB.empty := by
  sorry

@[simp, grind .]
lemma PB.cons_outputsOSize {h t : PB} {s_h s_t : List Data → ℕ}
    (hh : PB.outputsOSize h s_h) (ht : PB.outputsOSize t s_t) :
    PB.outputsOSize (PB.cons h t) (s_h + s_t) := by
  sorry

@[simp, grind .]
lemma PB.cons_usesOTime {h t : PB} {t_h t_t : List Data → ℕ}
    (hh : PB.usesOTime h t_h) (ht : PB.usesOTime t t_t) :
    PB.usesOTime (PB.cons h t) (t_h + t_t) := by
  sorry

@[simp, grind .]
lemma PB.cons_usesOSpace {h t : PB} {s_h s_t : List Data → ℕ}
    (hh : PB.usesOSpace h s_h) (ht : PB.usesOSpace t s_t) :
    PB.usesOSpace (PB.cons h t) (fun env => max (s_h env) (s_t env)) := by
  sorry

@[simp, grind .]
lemma PB.cons_preserves_linearity {h t : PB}
    (hh : PB.usesLinearTimeAndSpace h) (ht : PB.usesLinearTimeAndSpace t) :
    PB.usesLinearTimeAndSpace (PB.cons h t) := by
  sorry

@[simp, grind .]
lemma PB.elim_preserves_linearity {v em : PB} {cs : PB → PB → PB}
    (hv : PB.usesLinearTimeAndSpace v) (hem : PB.usesLinearTimeAndSpace em)
    -- TODO is this correct?
    (hcs : ∀ i j, PB.usesLinearTimeAndSpace (cs (PB.var i) (PB.var j))) :
    PB.usesLinearTimeAndSpace (PB.elim v em cs) := by
  sorry


end RoseTreeMachine

end Turing
