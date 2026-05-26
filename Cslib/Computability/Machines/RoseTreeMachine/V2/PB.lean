/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V2.Prog
public import Cslib.Computability.Machines.RoseTreeMachine.V2.DataEncode

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

----------------------------------------------------

def PB.computes (impl : PB) (f : List Data → Data) : Prop :=
  ∀ env, (impl env.length).eval env = .some (f env)

-------------------------------------------------------------------
--- tools
-------------------------------------------

/-- Example: `tail x` returns the tail of the list bound at variable `x`, or `empty`
    if `x` denotes the empty list. Built with `elim`: the empty branch yields `empty`,
    the cons branch ignores the head and projects the bound tail. -/
def PB.tail (x : PB) : PB := PB.elim x PB.empty (fun _head tl => tl)
def PB.head (x : PB) : PB := PB.elim x PB.empty (fun hd _tl => hd)

/-! ### Per-env `PB.computes_at`

A pointwise version of `PB.computes` that talks about a specific env. -/

/-- `PB.computes_at env impl d`: for every extension `ext` of `env`, when the
program is unfolded at depth `(env ++ ext).length` and evaluated on `env ++ ext`,
it yields `d`. The `∀ ext` quantifier captures the fact that well-formed PBs
preserve their value under env-extension, which is essential for composing them
inside binders. -/
def PB.computes_at (env : List Data) (impl : PB) (d : Data) : Prop :=
  ∀ ext : List Data,
    (impl (env.length + ext.length)).eval (env ++ ext) = .some d

-- TODO mabe we should think about using the following version of `computes_at`,
-- which should be sufficient for most cases:
-- (I think this was problematic at the binder bodies,
-- where the body PB is parameterised over var-lookup PBs for the bindings,
-- so the body PB itself needs to be depth-agnostic. But maybe we can still use this version for
-- the body hypotheses, and then show that the body PBs are depth-agnostic as a consequence of
-- their own `computes_at` hypotheses?)
def PB.computes_at_v2 (impl : PB) (f : List Data → Data) : Prop :=
  ∀ env : List Data, (impl (env.length)).eval env = .some (f env)

def PB.outputsOSize (impl : PB) (s : List Data → ℕ) : Prop :=
  ∃ a b, ∀ env : List Data, ∃ s' ≤ a * (s env) + b,
    (((impl env.length).meteredEval env).map fun (d, _, _) => d.size) = .some s'

def PB.usesOTime (impl : PB) (t : List Data → ℕ) : Prop :=
  ∃ a b, ∀ env : List Data, ∃ t' ≤ a * (t env) + b,
    (((impl env.length).meteredEval env).map fun (_, t'', _) => t'') = .some t'

def PB.usesOSpace (impl : PB) (s : List Data → ℕ) : Prop :=
  ∃ a b, ∀ env : List Data, ∃ s' ≤ a * (s env) + b,
    (((impl env.length).meteredEval env).map fun (_, _, s'') => s'') = .some s'

def PB.usesLinearTimeAndSpace (impl : PB) : Prop :=
  PB.usesOTime impl (fun env => (Data.l env).size) ∧
  PB.usesOSpace impl (fun env => (Data.l env).size)

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
lemma PB.var_computes_at_v2 {i : ℕ} :
    PB.computes_at_v2 (fun _ => .var i) fun env => env[i]?.getD (Data.l []) := by
  intro ext
  simp [Prog.eval, Prog.meteredEval]

@[simp]
lemma PB.var_last_computes_at {env ext : List Data} {d : Data} :
    PB.computes_at (env ++ ext ++ [d])
      (fun _ => Prog.var (env.length + ext.length)) d := by
  have hlen : env.length + ext.length < (env ++ ext ++ [d]).length := by simp
  have h := PB.var_computes_at (env := env ++ ext ++ [d]) hlen
  convert h using 2
  simp

@[simp, grind .]
lemma DB.var_usesOTime {env : List Data} {i : ℕ} (h : i < env.length) :
    PB.usesOTime (fun _ => .var i) 1 := by
  use 1, 0
  intro ext
  simp [Prog.meteredEval]

@[simp]
lemma PB.var_usesLinearTimeAndSpace {i : ℕ} :
    PB.usesLinearTimeAndSpace (fun _ => .var i) := by
  sorry


@[simp, grind .]
lemma PB.empty_computes_at {env : List Data} : PB.computes_at env PB.empty (Data.l []) := by
  intro ext
  simp [PB.empty, Prog.eval, Prog.meteredEval]

@[simp, grind .]
lemma PB.empty_outputsOSize : PB.outputsOSize PB.empty (fun _ => 1) := by
  use 2, 0
  simp [PB.empty, Prog.meteredEval]

@[simp, grind .]
lemma PB.empty_usesOTime : PB.usesOTime PB.empty 1 := by
  use 1, 0
  simp [PB.empty, Prog.meteredEval]

@[simp, grind .]
lemma PB.empty_usesOSpace : PB.usesOSpace PB.empty 1 := by
  use 1, 0
  simp [PB.empty, Prog.meteredEval]

@[simp, grind .]
lemma PB.empty_usesLinearTimeAndSpace : PB.usesLinearTimeAndSpace PB.empty := by
  sorry

@[simp, grind .]
lemma PB.cons_computes_at {env : List Data} {h t : PB} {dh dt : Data}
    (hh : PB.computes_at env h dh) (ht : PB.computes_at env t dt) :
    PB.computes_at env (PB.cons h t) (Data.l (dh :: dt.asList)) := by
  intro ext
  simpa [PB.cons] using Prog.cons_eval_simp (hh ext) (ht ext)

@[simp, grind .]
lemma PB.cons_computes_at_v2 {h t : PB} {fh ft : List Data → Data}
    (hh : PB.computes_at_v2 h fh) (ht : PB.computes_at_v2 t ft) :
    PB.computes_at_v2 (PB.cons h t) (fun env => Data.l ((fh env) :: (ft env).asList)) := by
  intro ext
  simpa [PB.cons] using Prog.cons_eval_simp (hh ext) (ht ext)

@[simp, grind .]
lemma PB.cons_outputsOSize {h t : PB} {s_h s_t : List Data → ℕ}
    (hh : PB.outputsOSize h s_h) (ht : PB.outputsOSize t s_t) :
    PB.outputsOSize (PB.cons h t) (s_h + s_t) := by
  obtain ⟨ah, bh, hh⟩ := hh
  obtain ⟨a_t, b_t, ht⟩ := ht
  refine ⟨max ah a_t, bh + b_t, fun env => ?_⟩
  obtain ⟨sh', hsh_le, hsh_eq⟩ := hh env
  obtain ⟨st', hst_le, hst_eq⟩ := ht env
  -- TODO this proof can be simplified if we introduce 'Prog.sizeOfOutput' similar to 'Prog.eval'
  rw [Part.eq_some_iff, Part.mem_map_iff] at hsh_eq hst_eq
  obtain ⟨⟨dh, th, sph⟩, hh_mem, rfl⟩ := hsh_eq
  obtain ⟨⟨dt, tt, spt⟩, ht_mem, rfl⟩ := hst_eq
  refine ⟨dh.size + dt.size, ?_, ?_⟩
  · calc dh.size + dt.size
        ≤ (ah * s_h env + bh) + (a_t * s_t env + b_t) := Nat.add_le_add hsh_le hst_le
      _ ≤ max ah a_t * s_h env + max ah a_t * s_t env + (bh + b_t) := by
          have h1 := Nat.mul_le_mul_right (s_h env) (le_max_left ah a_t)
          have h2 := Nat.mul_le_mul_right (s_t env) (le_max_right ah a_t)
          omega
      _ = max ah a_t * ((s_h + s_t) env) + (bh + b_t) := by
          simp [Pi.add_apply, Nat.mul_add]
  · have hh_eq : Prog.meteredEval env (h env.length) = .some (dh, th, sph) :=
      Part.eq_some_iff.mpr hh_mem
    have ht_eq : Prog.meteredEval env (t env.length) = .some (dt, tt, spt) :=
      Part.eq_some_iff.mpr ht_mem
    simp [PB.cons, Prog.meteredEval, hh_eq, ht_eq]

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

@[simp, grind .]
lemma PB.atSlot_usesLinearTimeAndSpace {i : ℕ} :
    PB.usesLinearTimeAndSpace (PB.atSlot i) := by
  unfold PB.atSlot
  simp [PB.var_usesLinearTimeAndSpace]

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

@[simp, grind .]
lemma PB.elim_preserves_linearity {v em : PB} {cs : PB → PB → PB}
    (hv : PB.usesLinearTimeAndSpace v) (hem : PB.usesLinearTimeAndSpace em)
    (hcs : ∀ i j, PB.usesLinearTimeAndSpace (cs (PB.atSlot i) (PB.atSlot j))) :
    PB.usesLinearTimeAndSpace (PB.elim v em cs) := by
  sorry


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


end RoseTreeMachine

end Turing
