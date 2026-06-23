/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Prog
public import Cslib.Computability.Machines.RTM.DataEncode
import Mathlib.Tactic.Linarith

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

-- TODO we should distinguish at the type level between Var (a variable / reference to a slot)
-- and ℕ (the environment depth)

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
def fn (body : ℕ → PB) : PB := fun n => .fn (body n (n + 1))
def app (f a : PB) : PB := fun n => .app (f n) (a n)

def letIn (e : PB) (body : ℕ → PB) : PB := app (fn body) e

macro "PBlet " x:ident ":=" e:term " in " body:term : term => do
  `(PB.letIn $e (fun $x => $body))

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

/-- Analogon of `Computes`, but as a statement of the pre-encoded value.
This allows statements that `PB`s compute functions on lean datatypes. -/
def ComputesEnc {α : Type} [DataEncode α] (env : List Value) (impl : PB) (x : α) :=
  Computes env impl (.data (DataEncode.encode x))

def EnvEnc {α : Type} [DataEncode α] (env : List Value) (var : ℕ) (x : α) :=
  ∀ ext, (env ++ ext)[var]?.getD Value.empty = .data (DataEncode.encode x)


------------------- Resource Consumption -------------------------

/-- The sum of the sizes of the values in an environment. -/
@[scoped grind =]
def envSize (env : List Value) : ℕ := env.map (fun x : Value => x.size) |>.sum

/-- The sum of the sizes of the variables accessed by `impl`.. This is essentially the size of the
closure, so it is implemented via that. -/
def accessedEnvSize (impl : PB) (env : List Value) :=
  (Value.closure (impl env.length) env).size

def accessedEnvSizeFun₂ (impl : PB → PB → PB) (env : List Value) (x y : Value) :=
  (Value.closure
    (impl (.var env.length) (.var (env.length + 1)) (env.length + 2))
    (env ++ [x, y])).size

/-- An upper bound on the runtime of the program `impl`. Note that this assumes that the program
always halts. -/
def TimeBounded (env : List Value) (impl : PB) (t : ℕ) :=
  ∀ x t' s, ProgSem env (impl env.length) x t' s → t' ≤ t

def TimeBoundedFun₁ (env : List Value) (impl : PB → PB) (t : ℕ) :=
  ∀ e, env <+: e → ∀ x, TimeBounded (e ++ [x]) (impl (.var e.length)) t

def SpaceBounded (env : List Value) (impl : PB) (s : ℕ) :=
  ∀ x t s', ProgSem env (impl env.length) x t s' → s' ≤ s

def OTime (impl : PB) (t : List Value → ℕ) :=
  ∃ k, ∀ env, TimeBounded env impl (k * (t env) + k)

def OSpace (impl : PB) (s : List Value → ℕ) :=
  ∃ k, ∀ env, SpaceBounded env impl (k * (s env) + k)

def OTimeFun₁ (impl : PB → PB) (t : List Value → ℕ) :=
  ∃ k, ∀ env x y t' s, ProgSem (env ++ [x]) (impl (.var env.length) (env.length + 1)) y t' s →
    t' ≤ k * (t (env ++ [x])) + k

def OSpaceFun₁ (impl : PB → PB) (s : List Value → ℕ) :=
  ∃ k, ∀ env x y t s', ProgSem (env ++ [x]) (impl (.var env.length) (env.length + 1)) y t s' →
    s' ≤ k * (s (env ++ [x])) + k

def OTimeFun₂ (impl : PB → PB → PB) (t : List Value → Value → Value → ℕ) :=
  ∃ k, ∀ env x y z t' s, ProgSem (env ++ [x, y])
    (impl (.var env.length) (.var (env.length + 1)) (env.length + 2)) z t' s →
      t' ≤ k * (t env x y) + k

def OSpaceFun₂ (impl : PB → PB → PB) (s : List Value → Value → Value → ℕ) :=
  ∃ k, ∀ env x y z t s', ProgSem (env ++ [x, y])
    (impl (.var env.length) (.var (env.length + 1)) (env.length + 2)) z t s' →
      s' ≤ k * (s env x y) + k

/-- The space and time complexity of `impl` is linear in the size of the accessed environment.
Note that this is more or less the best complexity we can have. -/
def Linear (impl : PB) := OTime impl (accessedEnvSize impl) ∧ OSpace impl (accessedEnvSize impl)

def LinearFun₂ (impl : PB → PB → PB) :=
  OTimeFun₂ impl (accessedEnvSizeFun₂ impl) ∧ OSpaceFun₂ impl (accessedEnvSizeFun₂ impl)

--------------------- Lemmas for combinators -------------------------------

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

lemma var_computes_of_envEnc {α : Type} [DataEncode α] {var : ℕ} {x : α} (h : EnvEnc env var x) :
    Computes env (PB.var var) (.data (DataEncode.encode x)) := by
  intro ext
  exact ⟨_, _, (h ext) ▸ ProgSem.var⟩

lemma empty_linear : Linear (PB.empty) := by
  have hcs : ∀ env, accessedEnvSize PB.empty env = 0 := fun env => by
    simp only [accessedEnvSize, PB.empty, Value.size]
    exact closureSize_of_noVar (fun i => by simp [Prog.hasVar])
  refine ⟨⟨2, fun env => ?_⟩, ⟨2, fun env => ?_⟩⟩
  · unfold TimeBounded
    intro x t' s h
    simp only [PB.empty] at h
    cases h
    simp [hcs]
  · unfold SpaceBounded
    intro x t s' h
    simp only [PB.empty] at h
    cases h
    simp [hcs]

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

lemma cons_linear {h t : PB} (hh : Linear h) (ht : Linear t) :
    Linear (PB.cons h t) := by
  sorry

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

/-- Inversion for a variable lookup: a `.var i` derivation reads `σ[i]` and charges exactly its
size for both time and space. -/
lemma ProgSem.var_inv {σ : List Value} {i : ℕ} {v : Value} {t s : ℕ}
    (h : ProgSem σ (.var i) v t s) :
    v = σ[i]?.getD Value.empty ∧ t = v.size ∧ s = v.size := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

lemma var_linear {i : ℕ} : Linear (PB.var i) := by
  constructor <;>
  · use 2
    intro env x t s h
    cases h
    simp only [accessedEnvSize, var, Value.size, closureSize_of_var]
    cases env[i]? with
    | none => simp
    | some v => grind

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

/-- The code in `body` computes a function of one argument `x` and returns `out`.
-- TODO use this instead of the above -/
def computesFun₁v (env : List Value) (x : Value) (body : ℕ → PB) (out : Value) : Prop :=
  ∀ ext : List Value, ∃ t s, ProgSem (env ++ ext ++ [x])
    (body (env.length + ext.length) (env.length + ext.length + 1))
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

/-- Shared core for the linearity of `PB.elim`: bounds a single cost dimension (selected by the
additive projection `π`, instantiated as `fun t _ => t` for time and `fun _ s => s` for space). -/
private lemma elim_linear_aux
    {v em : PB} {cs : PB → PB → PB} {k_v k_e k_c : ℕ}
    (π : ℕ → ℕ → ℕ)
    (πadd : ∀ a b c d, π (a + b) (c + d) = π a c + π b d)
    (πid : ∀ a, π a a = a)
    (hv : ∀ env x t s, ProgSem env (v env.length) x t s
      → π t s ≤ k_v * accessedEnvSize v env + k_v)
    (he : ∀ env x t s, ProgSem env (em env.length) x t s
      → π t s ≤ k_e * accessedEnvSize em env + k_e)
    (hc : ∀ env x y z t s, ProgSem (env ++ [x, y])
        (cs (.var env.length) (.var (env.length + 1)) (env.length + 2)) z t s
      → π t s ≤ k_c * accessedEnvSizeFun₂ cs env x y + k_c)
    (hsize : ∀ env p out t s, ProgSem env p out t s → out.size ≤ π t s) :
    ∃ K, ∀ env x t s, ProgSem env ((PB.elim v em cs) env.length) x t s
      → π t s ≤ K * accessedEnvSize (PB.elim v em cs) env + K := by
  refine ⟨((2+k_c)*(1+k_v) + ((2+k_c)*k_v + k_c)) + (k_v + k_e), fun env x t s h => ?_⟩
  set A := accessedEnvSize (PB.elim v em cs) env with hA
  have hA_cs : A = closureSize ((PB.elim v em cs) env.length) env := by
    simp only [hA, accessedEnvSize, Value.size]
  have hBcs : ∀ i, (cs (PB.var env.length) (PB.var (env.length+1)) (env.length+2)).hasVar i
      → ((PB.elim v em cs) env.length).hasVar i := by
    intro i hi; simp only [PB.elim, Prog.hasVar]; simp [hi]
  have aes_v : accessedEnvSize v env ≤ A := by
    simp only [hA, accessedEnvSize, Value.size]
    exact closureSize_mono env (by intro i hi; simp only [PB.elim, Prog.hasVar]; simp [hi])
  have aes_em : accessedEnvSize em env ≤ A := by
    simp only [hA, accessedEnvSize, Value.size]
    exact closureSize_mono env (by intro i hi; simp only [PB.elim, Prog.hasVar]; simp [hi])
  simp only [PB.elim] at h
  cases h with
  | elim_nil h₁ h₂ =>
      simp only [πadd]
      have hv2 := hv env _ _ _ h₁
      have he2 := he env _ _ _ h₂
      nlinarith [hv2, he2, Nat.mul_le_mul_left k_v aes_v, Nat.mul_le_mul_left k_e aes_em,
        Nat.zero_le A, Nat.zero_le k_c, Nat.zero_le k_v]
  | elim_cons h_v' h_cs' h_app₁ h_app₂ =>
      cases h_cs'
      cases h_app₁ with
      | mk hb1 =>
        cases hb1
        cases h_app₂ with
        | mk hb2 =>
          rename_i hd tl t_v s_v t₂ s₂
          set X := cs (PB.var env.length) (PB.var (env.length+1)) (env.length+2) with hXdef
          simp only [πadd, πid]
          set a := π t_v s_v with ha_def
          have ha : a ≤ k_v * A + k_v := by
            have h0 : a ≤ k_v * accessedEnvSize v env + k_v := hv env _ _ _ h_v'
            have := Nat.mul_le_mul_left k_v aes_v; omega
          have hsize_v : hd.size + (Data.l tl).size ≤ a := by
            have h0 := hsize env _ _ _ _ h_v'
            simp only [Value.size_data, Data.cons_size] at h0; omega
          have hb : (Value.closure (Prog.fn X) env).size ≤ A := by
            simp only [Value.size]; rw [hA_cs]
            exact closureSize_mono env (fun i hi => hBcs i (by simpa [Prog.hasVar] using hi))
          have hc1 : (Value.closure X (env ++ [Value.data hd])).size ≤ A + a := by
            simp only [Value.size, closureSize_append]
            have h2 : closureSize.go X env.length [Value.data hd] ≤ hd.size := by
              have := closureSize.go_le_sum X env.length [Value.data hd]; simpa using this
            have h1 : closureSize X env ≤ A := by rw [hA_cs]; exact closureSize_mono env hBcs
            omega
          have hb2' : ProgSem (env ++ [Value.data hd, Value.data (Data.l tl)]) X x t₂ s₂ := by
            have e : env ++ [Value.data hd] ++ [Value.data (Data.l tl)]
                   = env ++ [Value.data hd, Value.data (Data.l tl)] := by simp
            rw [e] at hb2; exact hb2
          have haef : accessedEnvSizeFun₂ cs env (Value.data hd) (Value.data (Data.l tl))
              ≤ A + a := by
            simp only [accessedEnvSizeFun₂, Value.size, closureSize_append]
            rw [← hXdef]
            have h2 : closureSize.go X env.length [Value.data hd, Value.data (Data.l tl)]
                ≤ hd.size + (Data.l tl).size := by
              have := closureSize.go_le_sum X env.length [Value.data hd, Value.data (Data.l tl)]
              simpa using this
            have h1 : closureSize X env ≤ A := by rw [hA_cs]; exact closureSize_mono env hBcs
            omega
          have hd2 : π t₂ s₂ ≤ k_c * (A + a) + k_c := by
            have h0 : π t₂ s₂ ≤ k_c
                * accessedEnvSizeFun₂ cs env (Value.data hd) (Value.data (Data.l tl))
                + k_c := hc env _ _ _ _ _ hb2'
            have := Nat.mul_le_mul_left k_c haef; omega
          nlinarith [ha, hb, hc1, hd2, Nat.zero_le A, Nat.zero_le k_c, Nat.zero_le k_v,
            Nat.zero_le k_e]

lemma elim_linear
    {v em : PB} {cs : PB → PB → PB}
    (h_v : Linear v) (h_em : Linear em) (h_cs : LinearFun₂ cs) :
    Linear (PB.elim v em cs) := by
  obtain ⟨⟨k_vt, hvt⟩, ⟨k_vs, hvs⟩⟩ := h_v
  obtain ⟨⟨k_et, het⟩, ⟨k_es, hes⟩⟩ := h_em
  obtain ⟨⟨k_ct, hct⟩, ⟨k_cs, hcs⟩⟩ := h_cs
  refine ⟨?_, ?_⟩
  · exact elim_linear_aux (fun t _ => t) (fun _ _ _ _ => rfl) (fun _ => rfl)
      (fun env x t s h => hvt env x t s h) (fun env x t s h => het env x t s h)
      (fun env x y z t s h => hct env x y z t s h)
      (fun _ _ _ _ _ h => (ProgSem.size_le h).1)
  · exact elim_linear_aux (fun _ s => s) (fun _ _ _ _ => rfl) (fun _ => rfl)
      (fun env x t s h => hvs env x t s h) (fun env x t s h => hes env x t s h)
      (fun env x y z t s h => hcs env x y z t s h)
      (fun _ _ _ _ _ h => (ProgSem.size_le h).2)


lemma elim_time {v em : PB} {cs : PB → PB → PB}
    {t_v t_em : List Value → ℕ} {t_cs : List Value → Value → Value → ℕ}
    (h_v : OTime v t_v)
    (h_em : OTime em t_em)
    (h_cs : OTimeFun₂ cs t_cs) :
  OTime (PB.elim v em cs) (fun env => t_v env + t_em env) := by sorry


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

lemma ifeq_computes {x y then_ else_ : PB} {vx vy : Data} {out₁ out₂ : Value}
    (hx : Computes env x (.data vx))
    (hy : Computes env y (.data vy))
    (hthen : Computes env then_ out₁)
    (helse : Computes env else_ out₂) :
    Computes env (PB.ifEq x y then_ else_) (if vx == vy then out₁ else out₂) := by
  by_cases h : vx = vy
  · exact ifeq_eq_computes hx (h ▸ hy) (by simpa [h] using hthen)
  · exact ifeq_ne_computes hx hy h (by simpa [h] using helse)

/-- In-place application of a literal abstraction (a `let` binding): if `arg` computes `dx`
and `body` computes `out` with its parameter bound to `dx`, then `app (fn body) arg` computes
`out`. -/
lemma app_fn_computes {body : ℕ → PB} {arg : PB} {dx out : Value}
    (harg : Computes env arg dx)
    (hbody : computesFun₁v env dx body out) :
    Computes env (PB.app (PB.fn body) arg) out := by
  intro ext
  obtain ⟨ta, sa, ha⟩ := harg ext
  obtain ⟨tb, sb, hb⟩ := hbody ext
  simp only [PB.app, fn]
  have hmap : (env ++ ext) ++ [dx]
      = (env ++ ext ++ [dx]) := by
    simp
  have hb' : ProgSem ((env ++ ext) ++ [dx])
      (body (env.length + ext.length) (env.length + ext.length + 1))
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

/-- Core complexity lemma for `WhileSem`: if each body application on input of size `s` takes
time at most `T s` (with `T` monotone) and grows the accumulator size by at most `k`, then
there exist `n` steps such that `r.size ≤ acc.size + n * k` and the total time satisfies
`t ≤ ∑ i < n, T (acc.size + i * k) + r.size`.

The monotonicity of `T` is needed to handle the ≤ in `h_size`: when shifting the inductive
hypothesis's sum from `v.size` to `acc.size`, we use `v.size + i * k ≤ acc.size + (i+1) * k`
together with monotonicity to bound each summand upward. -/
lemma WhileSem.time_bound
    {bodyVal : Value} {acc r : Data} {t s : ℕ}
    (h : WhileSem bodyVal acc r t s)
    {k : ℕ} {T : ℕ → ℕ}
    (h_mono : Monotone T)
    (h_time : ∀ v w t' s', AppSem bodyVal (.data v) (.data w) t' s' → t' ≤ T v.size)
    (h_size : ∀ v w t' s', AppSem bodyVal (.data v) (.data w) t' s' → w.size ≤ v.size + k) :
    ∃ n : ℕ, r.size ≤ acc.size + n * k ∧
      t ≤ ((List.range n).map (fun i => T (acc.size + i * k))).sum + r.size := by
  sorry

/-- Complexity of a `while_` loop whose body runs in time ≤ `c * envSize e + c` on any
environment `e`, and grows the accumulator size by at most `k` per step.

For any outer extension `ext`, there exist a step count `n` and a time `T` such that
`T ≤ acc.size + envSize (env ++ ext) +
    ∑ i < n, (c * (envSize (env ++ ext) + acc.size + i * k) + c) + r.size`
and the program evaluates to `r` in time `T`. The three additive components are:
- `acc.size`: cost of evaluating the initial variable (via `ProgSem.var`);
- `envSize (env ++ ext)`: cost of forming the body closure (closure size ≤ env size);
- the sum: accumulated body cost at each iteration (each step at size `acc.size + i * k`);
- `r.size`: the final halt check cost in `WhileSem.halt`. -/
theorem while_complexity
    {init : ℕ} {body : PB → PB} {c k : ℕ}
    (h_body_time : ∀ (e : List Value) (x : Value) y t' s',
      ProgSem (e ++ [x]) (body (.var e.length) (e.length + 1)) y t' s' →
      t' ≤ c * envSize (e ++ [x]) + c)
    (h_body_size : ∀ (e : List Value) (x : Value) y t' s',
      ProgSem (e ++ [x]) (body (.var e.length) (e.length + 1)) y t' s' →
      y.size ≤ x.size + k)
    {acc r : Data}
    (h_init : EnvEnc env init acc)
    (h_loop : WhileComputes env body acc r) :
    ∀ ext : List Value, ∃ n : ℕ,
      ∃ T ≤ acc.size + envSize (env ++ ext) +
            ((List.range n).map (fun i => c * (envSize (env ++ ext) + acc.size + i * k) + c)).sum +
            r.size,
        ∃ S, ProgSem (env ++ ext)
          (PB.while_ (.var init) body (env.length + ext.length)) (.data r) T S := by
  sorry
------------------- Resource Consumption -------------------------

-- /-- Resource-erased relational semantics of a program builder. -/
-- def UsesTimeAndSpace (env : List Value) (impl : PB) (t s : ℕ) : Prop :=
--   ∀ ext : List Value,
--     ∃ out, ProgSem (env ++ ext) (impl (env.length + ext.length))
--       out t s

-- def LinearOverhead (impl : PB → PB) : Prop :=
--   ∃ k, ∀ env p t s,
--     UsesTimeAndSpace env p t s →
--     ∃ t' ≤ k * t + k, ∃ s' ≤ k * s + k,
--     UsesTimeAndSpace env (impl p) t' s'

-- def LinearOverhead₂ (impl : PB → PB → PB) : Prop :=
--   ∃ k, ∀ env p₁ p₂ t₁ s₁ t₂ s₂,
--     UsesTimeAndSpace env p₁ t₁ s₁ →
--     UsesTimeAndSpace env p₂ t₂ s₂ →
--     ∃ t' ≤ k * (t₁ + t₂) + k, ∃ s' ≤ k * (s₁ + s₂) + k,
--     UsesTimeAndSpace env (impl p₁ p₂) t' s'


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

-- def ComputesInTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
--     (env : List Value) (p : PB) (y : β) (t s : ℕ) : Prop :=
--   ∀ ext, ProgSem (env ++ ext) (p (env.length + ext.length))
--       (.data (DataEncode.encode y)) t s

def ComputesFunInAdditionalTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
    (env : List Value) (p : PB → PB) (x : α) (y : β) (t s : α → ℕ) : Prop :=
  ∀ (a : PB) (ta sa : ℕ),
    (∀ ext, ProgSem (env ++ ext) (a (env.length + ext.length))
      (.data (DataEncode.encode x)) ta sa) →
    (∀ ext, ∃ t' ≤ t x, ∃ s' ≤ s x, ProgSem (env ++ ext) (p a (env.length + ext.length))
      (.data (DataEncode.encode y)) (t' + ta) (s' + sa))

-- def ComputesFunInTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
--     (p : PB → PB) (φ : α → β) (t s : α → ℕ) : Prop :=
--   ∀ x, ComputesFunInAdditionalTimeAndSpace p x (φ x) t s

-- def ComputesFunInLinearTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
--     (p : PB → PB) (φ : α → β) : Prop :=
--   ∃ k, ComputesFunInTimeAndSpace p φ
--     (fun x => k * (DataEncode.encode x).size + k)
--     (fun x => k * (DataEncode.encode x).size + k)

end PB

end RoseTreeMachine

end Turing
