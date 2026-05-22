/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V2.Data
public import Mathlib.Control.Fix
public import Mathlib.Control.LawfulFix

/-! # RoseTreeMachine V2 — Prog

Part of the RoseTreeMachine V2 development; see
`Cslib/Computability/Machines/RoseTreeMachine/V2.lean` for an overview.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

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

/-- `Prog.eval` returns `.some d` iff the underlying metered evaluation returns some triple
with first component `d`. -/
lemma Prog.eval_some_iff_meteredEval {p : Prog} {env : List Data} {d : Data} :
    p.eval env = .some d ↔ ∃ t s, p.meteredEval env = .some (d, t, s) := by
  rw [Prog.eval]
  constructor
  · intro h
    rw [Part.eq_some_iff, Part.mem_map_iff] at h
    obtain ⟨⟨d', t, s⟩, hm, heq⟩ := h
    cases heq
    exact ⟨t, s, Part.eq_some_iff.mpr hm⟩
  · rintro ⟨t, s, h⟩; rw [h]; rfl

/-- Pointwise (single-env) version of `Prog.cons_computes`. -/
lemma Prog.cons_eval {h t : Prog} {env : List Data} {dh dt : Data}
    (hh : h.eval env = .some dh) (ht : t.eval env = .some dt) :
    (Prog.cons h t).eval env = .some (Data.l (dh :: dt.asList)) := by
  obtain ⟨th, sh, hmh⟩ := Prog.eval_some_iff_meteredEval.mp hh
  obtain ⟨tt, st, hmt⟩ := Prog.eval_some_iff_meteredEval.mp ht
  show (Prog.meteredEval env (Prog.cons h t)).map Prod.fst = _
  rw [Prog.meteredEval, hmh]
  simp only [bind, Part.bind_some, hmt, pure, Part.map_some]

/-- Pointwise (single-env) version for `elim`. -/
lemma Prog.elim_eval {v em cs : Prog} {env : List Data} {dv : Data}
    (hv : v.eval env = .some dv) :
    (Prog.elim v em cs).eval env =
      match dv.asList with
      | [] => em.eval env
      | head :: tail => cs.eval (env ++ [head, Data.l tail]) := by
  obtain ⟨t, s, hmv⟩ := Prog.eval_some_iff_meteredEval.mp hv
  show (Prog.meteredEval env (Prog.elim v em cs)).map Prod.fst = _
  rw [Prog.meteredEval, hmv]
  simp only [bind, Part.bind_some]
  rcases h : dv.asList with _ | ⟨head, tail⟩
  · have hdv : dv = Data.l [] := by rw [← Data.asList_l dv, h]
    rw [hdv]; simp only; rw [Prog.eval]; ext d
    simp [Part.mem_map_iff, Part.mem_bind_iff]
  · have hdv : dv = Data.l (head :: tail) := by rw [← Data.asList_l dv, h]
    rw [hdv]; simp only; rw [Prog.eval]; ext d
    simp [Part.mem_map_iff, Part.mem_bind_iff]

/-- The loop core of `while_`: starting from accumulator `acc` (a `Data`),
halt and return `acc` if its `asList.headD` is empty; otherwise run `body` on
`env ++ [acc]` and recurse on the result. -/
noncomputable def Prog.whileFrom_eval (body : Prog) (env : List Data) : Data → Part Data :=
  Part.fix fun rec acc =>
    if acc.asList.headD (Data.l []) = Data.l [] then
      Part.some acc
    else
      (body.eval (env ++ [acc])).bind rec

/-- The loop body for `whileFrom_eval` is `ωScottContinuous`, which gives us access
to `Part.fix_eq` for unrolling. -/
lemma Prog.whileFrom_eval_continuous (body : Prog) (env : List Data) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun (rec : Data → Part Data) (acc : Data) =>
        if acc.asList.headD (Data.l []) = Data.l [] then
          Part.some acc
        else
          (body.eval (env ++ [acc])).bind rec) := by
  apply OmegaCompletePartialOrder.ωScottContinuous.of_apply₂
  intro a
  by_cases h : a.asList.headD (Data.l []) = Data.l []
  · simp only [h, if_true]
    exact OmegaCompletePartialOrder.ωScottContinuous.const
  · simp only [h, if_false]
    exact OmegaCompletePartialOrder.ContinuousHom.ωScottContinuous.bind
      OmegaCompletePartialOrder.ωScottContinuous.const
      (OmegaCompletePartialOrder.ωScottContinuous.of_apply₂
        (fun _ => OmegaCompletePartialOrder.ωScottContinuous.id.apply₂ _))

/-- Halt-step unrolling for `whileFrom_eval`. -/
lemma Prog.whileFrom_eval_halt {body : Prog} {env : List Data} {acc : Data}
    (h_halt : acc.asList.headD (Data.l []) = Data.l []) :
    Prog.whileFrom_eval body env acc = .some acc := by
  unfold Prog.whileFrom_eval
  conv_lhs =>
    rw [Part.fix_eq_of_ωScottContinuous (Prog.whileFrom_eval_continuous body env)]
  simp only [h_halt, if_true]

/-- Body-step unrolling for `whileFrom_eval`. -/
lemma Prog.whileFrom_eval_step {body : Prog} {env : List Data} {acc : Data}
    (h_step : acc.asList.headD (Data.l []) ≠ Data.l []) :
    Prog.whileFrom_eval body env acc =
      (body.eval (env ++ [acc])).bind (Prog.whileFrom_eval body env) := by
  conv_lhs => unfold Prog.whileFrom_eval
  conv_lhs =>
    rw [Part.fix_eq_of_ωScottContinuous (Prog.whileFrom_eval_continuous body env)]
  simp only [h_step, if_false]
  rfl

/-! ### Auxiliary metered/non-metered correspondence for `Prog.while_eval`.

These private helpers factor out the metered and non-metered loop bodies and
establish that the metered fix, projected to its data component, equals the
non-metered `whileFrom_eval`. This is the key ingredient for `Prog.while_eval`.
-/

private noncomputable def Prog.metered_F (body : Prog) (env : List Data) :
    ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) → (Data × ℕ × ℕ) → Part (Data × ℕ × ℕ) :=
  fun rec d_ts =>
    let (acc, t, s) := d_ts
    if acc.asList.headD (Data.l []) = Data.l [] then
      .some (acc, t, s)
    else
      (body.meteredEval (env ++ [acc])).bind fun y =>
        rec (y.1, t + 1 + y.2.1, max s y.2.2)

private noncomputable def Prog.nonmet_G (body : Prog) (env : List Data) :
    (Data → Part Data) → Data → Part Data :=
  fun rec acc =>
    if acc.asList.headD (Data.l []) = Data.l [] then
      Part.some acc
    else
      (body.eval (env ++ [acc])).bind rec

private lemma Prog.metered_F_monotone (body : Prog) (env : List Data) :
    Monotone (Prog.metered_F body env) := by
  intro f g hfg ⟨acc, t, s⟩ x hx
  unfold Prog.metered_F at hx ⊢
  simp only at hx ⊢
  by_cases h : acc.asList.headD (Data.l []) = Data.l []
  · rw [if_pos h] at hx ⊢; exact hx
  · rw [if_neg h] at hx ⊢
    rw [Part.mem_bind_iff] at hx ⊢
    obtain ⟨y, hy1, hy2⟩ := hx
    exact ⟨y, hy1, hfg _ _ hy2⟩

private lemma Prog.nonmet_G_monotone (body : Prog) (env : List Data) :
    Monotone (Prog.nonmet_G body env) := by
  intro f g hfg acc x hx
  unfold Prog.nonmet_G at hx ⊢
  by_cases h : acc.asList.headD (Data.l []) = Data.l []
  · rw [if_pos h] at hx ⊢; exact hx
  · rw [if_neg h] at hx ⊢
    rw [Part.mem_bind_iff] at hx ⊢
    obtain ⟨y, hy1, hy2⟩ := hx
    exact ⟨y, hy1, hfg _ _ hy2⟩

private lemma Prog.approx_metered_to_nonmet (body : Prog) (env : List Data) :
    ∀ (n : ℕ) (i : Data) (t s : ℕ) (r : Data) (t' s' : ℕ),
      (r, t', s') ∈ Part.Fix.approx (Prog.metered_F body env) n (i, t, s) →
      r ∈ Part.Fix.approx (Prog.nonmet_G body env) n i := by
  intro n
  induction n with
  | zero => intro i t s r t' s' h; exact absurd h (Part.notMem_none _)
  | succ n ih =>
    intro i t s r t' s' h
    show r ∈ (Prog.nonmet_G body env) (Part.Fix.approx (Prog.nonmet_G body env) n) i
    have hF : (r, t', s') ∈
        (Prog.metered_F body env) (Part.Fix.approx (Prog.metered_F body env) n) (i, t, s) := h
    unfold Prog.metered_F at hF
    unfold Prog.nonmet_G
    simp only at hF
    by_cases hh : i.asList.headD (Data.l []) = Data.l []
    · rw [if_pos hh] at hF; rw [if_pos hh]
      rw [Part.mem_some_iff] at hF
      have : r = i := (Prod.mk.injEq ..).mp hF |>.1
      subst this
      exact Part.mem_some _
    · rw [if_neg hh] at hF; rw [if_neg hh]
      rw [Part.mem_bind_iff] at hF
      obtain ⟨⟨r0, bt, bs⟩, hb, hrec⟩ := hF
      rw [Part.mem_bind_iff]
      refine ⟨r0, ?_, ih r0 _ _ r t' s' hrec⟩
      show r0 ∈ (body.meteredEval (env ++ [i])).map Prod.fst
      rw [Part.mem_map_iff]
      exact ⟨(r0, bt, bs), hb, rfl⟩

private lemma Prog.approx_nonmet_to_metered (body : Prog) (env : List Data) :
    ∀ (n : ℕ) (i : Data) (t s : ℕ) (r : Data),
      r ∈ Part.Fix.approx (Prog.nonmet_G body env) n i →
      ∃ t' s', (r, t', s') ∈ Part.Fix.approx (Prog.metered_F body env) n (i, t, s) := by
  intro n
  induction n with
  | zero => intro i t s r h; exact absurd h (Part.notMem_none _)
  | succ n ih =>
    intro i t s r h
    show ∃ t' s', (r, t', s') ∈
        (Prog.metered_F body env) (Part.Fix.approx (Prog.metered_F body env) n) (i, t, s)
    have hG : r ∈ (Prog.nonmet_G body env) (Part.Fix.approx (Prog.nonmet_G body env) n) i := h
    unfold Prog.nonmet_G at hG
    unfold Prog.metered_F
    simp only
    by_cases hh : i.asList.headD (Data.l []) = Data.l []
    · rw [if_pos hh] at hG; rw [if_pos hh]
      rw [Part.mem_some_iff] at hG; subst hG
      exact ⟨t, s, Part.mem_some _⟩
    · rw [if_neg hh] at hG; rw [if_neg hh]
      rw [Part.mem_bind_iff] at hG
      obtain ⟨r0, hbody, hrec⟩ := hG
      have hbody' : r0 ∈ (body.meteredEval (env ++ [i])).map Prod.fst := hbody
      rw [Part.mem_map_iff] at hbody'
      obtain ⟨⟨r0', bt, bs⟩, hmev, heq⟩ := hbody'
      simp only at heq
      have : r0' = r0 := heq
      subst this
      obtain ⟨t', s', hF⟩ := ih r0' (t + 1 + bt) (max s bs) r hrec
      refine ⟨t', s', ?_⟩
      rw [Part.mem_bind_iff]
      exact ⟨(r0', bt, bs), hmev, hF⟩

private lemma Prog.proj_fix_eq (body : Prog) (env : List Data) (i : Data) (t s : ℕ) :
    (Part.fix (Prog.metered_F body env) (i, t, s)).map Prod.fst =
      Prog.whileFrom_eval body env i := by
  apply Part.ext
  intro r
  rw [Part.mem_map_iff]
  let F_oh : ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) →o
      ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) :=
    ⟨Prog.metered_F body env, Prog.metered_F_monotone body env⟩
  let G_oh : (Data → Part Data) →o (Data → Part Data) :=
    ⟨Prog.nonmet_G body env, Prog.nonmet_G_monotone body env⟩
  have hF_eq : ∀ {a b}, b ∈ Part.fix (Prog.metered_F body env) a ↔ b ∈ Part.fix (⇑F_oh) a := by
    intros; rfl
  have hG_eq : ∀ {a b}, b ∈ Part.fix (Prog.nonmet_G body env) a ↔ b ∈ Part.fix (⇑G_oh) a := by
    intros; rfl
  constructor
  · rintro ⟨⟨r', t', s'⟩, hmem, rfl⟩
    rw [hF_eq, Part.Fix.mem_iff F_oh] at hmem
    obtain ⟨n, hn⟩ := hmem
    show r' ∈ Prog.whileFrom_eval body env i
    unfold Prog.whileFrom_eval
    show r' ∈ Part.fix (Prog.nonmet_G body env) i
    rw [hG_eq, Part.Fix.mem_iff G_oh]
    exact ⟨n, Prog.approx_metered_to_nonmet body env n i t s r' _ _ hn⟩
  · intro hr
    have hr' : r ∈ Part.fix (Prog.nonmet_G body env) i := hr
    rw [hG_eq, Part.Fix.mem_iff G_oh] at hr'
    obtain ⟨n, hn⟩ := hr'
    obtain ⟨t', s', hF⟩ := Prog.approx_nonmet_to_metered body env n i t s r hn
    refine ⟨(r, t', s'), ?_, rfl⟩
    rw [hF_eq, Part.Fix.mem_iff F_oh]
    exact ⟨n, hF⟩

/-- Pointwise (single-env) version for `while_`: the program evaluates `init`,
then runs the loop body starting from that value. -/
lemma Prog.while_eval {init body : Prog} {env : List Data} :
    (Prog.while_ init body).eval env =
      (init.eval env).bind (Prog.whileFrom_eval body env) := by
  show (Prog.meteredEval env (Prog.while_ init body)).map Prod.fst = _
  have hmEq : Prog.meteredEval env (Prog.while_ init body) =
      (init.meteredEval env).bind (fun x =>
        Part.fix (Prog.metered_F body env) (x.1, 1 + x.2.1, max 1 x.2.2)) := by
    rw [Prog.meteredEval]; rfl
  rw [hmEq]
  apply Part.ext
  intro r
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨⟨r', t', s'⟩, hmem, rfl⟩
    rw [Part.mem_bind_iff] at hmem
    obtain ⟨⟨i, it, is⟩, hmi, hf⟩ := hmem
    rw [Part.mem_bind_iff]
    refine ⟨i, ?_, ?_⟩
    · show i ∈ (init.meteredEval env).map Prod.fst
      rw [Part.mem_map_iff]; exact ⟨_, hmi, rfl⟩
    · rw [← Prog.proj_fix_eq body env i (1 + it) (max 1 is), Part.mem_map_iff]
      exact ⟨_, hf, rfl⟩
  · intro hr
    rw [Part.mem_bind_iff] at hr
    obtain ⟨i, hi, hr2⟩ := hr
    have hi' : i ∈ (init.meteredEval env).map Prod.fst := hi
    rw [Part.mem_map_iff] at hi'
    obtain ⟨⟨i', it, is⟩, hmi, heq⟩ := hi'
    simp only at heq
    have hii : i' = i := heq
    subst hii
    rw [← Prog.proj_fix_eq body env i' (1 + it) (max 1 is), Part.mem_map_iff] at hr2
    obtain ⟨⟨r', t', s'⟩, hF, rfl⟩ := hr2
    refine ⟨(r', t', s'), ?_, rfl⟩
    rw [Part.mem_bind_iff]
    exact ⟨(i', it, is), hmi, hF⟩

/-- Termination-extraction for `whileFrom_eval`: if the loop returns `.some r`,
then there exists an iteration index `n` such that running the body `n` times
from `acc` along the (deterministic) trajectory yields `r`, the halt condition
holds at `r`, and the halt condition does not hold at any intermediate value. -/
lemma Prog.whileFrom_eval_some {body : Prog} {env : List Data} {acc r : Data}
    (h : Prog.whileFrom_eval body env acc = .some r) :
    ∃ (n : ℕ) (traj : ℕ → Data),
      traj 0 = acc ∧
      traj n = r ∧
      (r.asList.headD (Data.l []) = Data.l []) ∧
      (∀ k < n,
          (traj k).asList.headD (Data.l []) ≠ Data.l [] ∧
          body.eval (env ++ [traj k]) = .some (traj (k+1))) := by
  -- Helper: induct on approx index to extract a trajectory.
  have approx_some_traj : ∀ (n : ℕ) (acc r : Data),
      r ∈ Part.Fix.approx (Prog.nonmet_G body env) n acc →
      ∃ (k : ℕ) (traj : ℕ → Data),
        traj 0 = acc ∧ traj k = r ∧
        (r.asList.headD (Data.l []) = Data.l []) ∧
        (∀ j < k, (traj j).asList.headD (Data.l []) ≠ Data.l [] ∧
                  body.eval (env ++ [traj j]) = .some (traj (j+1))) := by
    intro n
    induction n with
    | zero => intro acc r h; exact absurd h (Part.notMem_none _)
    | succ n ih =>
      intro acc r h
      have hG : r ∈ (Prog.nonmet_G body env)
          (Part.Fix.approx (Prog.nonmet_G body env) n) acc := h
      unfold Prog.nonmet_G at hG
      by_cases hh : acc.asList.headD (Data.l []) = Data.l []
      · rw [if_pos hh] at hG
        rw [Part.mem_some_iff] at hG
        cases hG
        refine ⟨0, fun _ => acc, rfl, rfl, hh, ?_⟩
        intro j hj; omega
      · rw [if_neg hh] at hG
        rw [Part.mem_bind_iff] at hG
        obtain ⟨r0, hbody, hrec⟩ := hG
        obtain ⟨k, traj', htraj0, htrajk, hr_halt, hsteps⟩ := ih r0 r hrec
        refine ⟨k + 1, fun j => if j = 0 then acc else traj' (j - 1),
                by simp, ?_, hr_halt, ?_⟩
        · show (if k + 1 = 0 then acc else traj' (k + 1 - 1)) = r
          rw [if_neg (by omega)]
          have : k + 1 - 1 = k := by omega
          rw [this]; exact htrajk
        · intro j hj
          cases j with
          | zero =>
            show (if (0 : ℕ) = 0 then acc else traj' (0 - 1)).asList.headD (Data.l []) ≠ Data.l [] ∧
                 body.eval (env ++ [if (0 : ℕ) = 0 then acc else traj' (0 - 1)]) =
                  .some (if (0 + 1 : ℕ) = 0 then acc else traj' (0 + 1 - 1))
            simp only [if_true, if_neg (Nat.succ_ne_zero 0)]
            refine ⟨hh, ?_⟩
            have heval : body.eval (env ++ [acc]) = .some r0 :=
              (Part.eq_some_iff.mpr hbody)
            rw [heval]; congr 1
            show r0 = traj' 0
            exact htraj0.symm
          | succ j =>
            show (if (j + 1 : ℕ) = 0 then acc else traj' (j + 1 - 1)).asList.headD
                  (Data.l []) ≠ Data.l [] ∧
                 body.eval (env ++ [if (j + 1 : ℕ) = 0 then acc else traj' (j + 1 - 1)]) =
                  .some (if (j + 1 + 1 : ℕ) = 0 then acc else traj' (j + 1 + 1 - 1))
            rw [if_neg (Nat.succ_ne_zero _), if_neg (Nat.succ_ne_zero _)]
            have hjk : j < k := by omega
            have h_idx1 : (j + 1 - 1 : ℕ) = j := by omega
            have h_idx2 : (j + 1 + 1 - 1 : ℕ) = j + 1 := by omega
            rw [h_idx1, h_idx2]
            exact hsteps j hjk
  have hmem : r ∈ Prog.whileFrom_eval body env acc := by rw [h]; exact Part.mem_some _
  have hmem' : r ∈ Part.fix (Prog.nonmet_G body env) acc := hmem
  let G_oh : (Data → Part Data) →o (Data → Part Data) :=
    ⟨Prog.nonmet_G body env, Prog.nonmet_G_monotone body env⟩
  have hmem'' : r ∈ Part.fix (⇑G_oh) acc := hmem'
  rw [Part.Fix.mem_iff G_oh] at hmem''
  obtain ⟨n, hn⟩ := hmem''
  exact approx_some_traj n acc r hn

/-! ## Surface syntax with named binders

Define convenience builder functions to allow binding the variables to names.

 -/


/-! ### Pointwise `Prog`-level `simp` set

Lifting eval rules to `@[simp]` lemmas lets you discharge most goals of the form
`p.eval env = .some d` by `simp` plus at most one `rcases` on a list. -/

@[simp] lemma Prog.var_eval {env : List Data} {i : ℕ} :
    (Prog.var i).eval env = .some (env[i]?.getD (Data.l [])) := by
  simp [Prog.eval, Prog.meteredEval]

@[simp] lemma Prog.empty_eval {env : List Data} :
    Prog.empty.eval env = .some (Data.l []) := by
  simp [Prog.eval, Prog.meteredEval, Data.empty]

@[simp] lemma Prog.cons_eval_simp {env : List Data} {h t : Prog} {dh dt : Data}
    (hh : h.eval env = .some dh) (ht : t.eval env = .some dt) :
    (Prog.cons h t).eval env = .some (Data.l (dh :: dt.asList)) :=
  Prog.cons_eval hh ht

@[simp] lemma Prog.elim_eval_nil {env : List Data} {v em cs : Prog}
    (hv : v.eval env = .some (Data.l [])) :
    (Prog.elim v em cs).eval env = em.eval env := by
  have := Prog.elim_eval (em := em) (cs := cs) hv
  simpa using this

@[simp] lemma Prog.elim_eval_cons {env : List Data} {v em cs : Prog}
    {head : Data} {tail : List Data}
    (hv : v.eval env = .some (Data.l (head :: tail))) :
    (Prog.elim v em cs).eval env = cs.eval (env ++ [head, Data.l tail]) := by
  have := Prog.elim_eval (em := em) (cs := cs) hv
  simpa using this

@[simp] lemma Prog.letin_eval {env : List Data} {val rest : Prog} {dv : Data}
    (hv : val.eval env = .some dv) :
    (Prog.letin val rest).eval env = rest.eval (env ++ [dv]) := by
  obtain ⟨t, s, hmv⟩ := Prog.eval_some_iff_meteredEval.mp hv
  show (Prog.meteredEval env (Prog.letin val rest)).map Prod.fst = _
  rw [Prog.meteredEval, hmv]
  simp only [bind, Part.bind_some]
  rw [Prog.eval]; ext d
  simp [Part.mem_map_iff, Part.mem_bind_iff]

@[simp] lemma Prog.eq_eval {env : List Data} {a b : Prog} {da db : Data}
    (ha : a.eval env = .some da) (hb : b.eval env = .some db) :
    (Prog.eq a b).eval env =
      .some (if da = db then Data.l [Data.l []] else Data.l []) := by
  obtain ⟨ta, sa, hma⟩ := Prog.eval_some_iff_meteredEval.mp ha
  obtain ⟨tb, sb, hmb⟩ := Prog.eval_some_iff_meteredEval.mp hb
  show (Prog.meteredEval env (Prog.eq a b)).map Prod.fst = _
  rw [Prog.meteredEval, hma]
  simp only [bind, Part.bind_some, hmb, beq_iff_eq]
  by_cases h : da = db <;> simp [h, Part.map_some]

/-- Helper for `Prog.fold_eval`: chained `foldlM` over `meteredEval`. -/
private lemma Prog.foldlM_chain (body : Prog) (env : List Data)
    (acc : ℕ → Data) :
    ∀ (dl : List Data) (start : ℕ) (t s : ℕ),
      (∀ k (h : k < dl.length),
        body.eval (env ++ [acc (start + k), dl[k]]) = .some (acc (start + k + 1))) →
      ∃ t' s', List.foldlM
        (fun x el => (body.meteredEval (env ++ [x.1, el])).bind fun y =>
          pure (y.1, 1 + x.2.1 + y.2.1, max x.2.2 y.2.2))
        (acc start, t, s) dl = .some (acc (start + dl.length), t', s') := by
  intro dl
  induction dl with
  | nil => intro start t s _hstep
           refine ⟨t, s, ?_⟩
           simp [List.foldlM]
  | cons hd tl ih =>
    intro start t s hstep
    have h0 : body.eval (env ++ [acc start, hd]) = .some (acc (start + 1)) := by
      have := hstep 0 (by simp)
      simpa using this
    obtain ⟨bt, bs, hmb⟩ := Prog.eval_some_iff_meteredEval.mp h0
    simp only [List.foldlM_cons, List.length_cons, hmb, Part.bind_some, pure, bind]
    have hstep' : ∀ k (h : k < tl.length),
        body.eval (env ++ [acc ((start + 1) + k), tl[k]]) = .some (acc ((start + 1) + k + 1)) := by
      intro k hk
      have hh : k + 1 < (hd :: tl).length := by rw [List.length_cons]; omega
      have := hstep (k + 1) hh
      have h_eq : (hd :: tl)[k + 1] = tl[k] := by simp
      rw [h_eq] at this
      have h1 : start + 1 + k = start + (k + 1) := by omega
      rw [h1]; exact this
    obtain ⟨t', s', ih_res⟩ := ih (start + 1) (1 + t + bt) (max s bs) hstep'
    refine ⟨t', s', ?_⟩
    have h_len : start + (tl.length + 1) = (start + 1) + tl.length := by omega
    rw [h_len]; exact ih_res

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
  obtain ⟨it, is, hmi⟩ := Prog.eval_some_iff_meteredEval.mp hi
  obtain ⟨lt, ls, hml⟩ := Prog.eval_some_iff_meteredEval.mp hl
  rw [← hacc0] at hmi
  have hstep' : ∀ k (h : k < dl.length),
      body.eval (env ++ [acc (0 + k), dl[k]]) = .some (acc (0 + k + 1)) := by
    intro k hk; simpa using hstep k hk
  obtain ⟨t', s', hfold⟩ := Prog.foldlM_chain body env acc dl 0 (1 + it + lt) (max is ls) hstep'
  show (Prog.meteredEval env (Prog.fold body init list)).map Prod.fst = _
  rw [Prog.meteredEval, hmi]
  simp only [bind, Part.bind_some, hml, Data.l_asList]
  rw [hfold]
  simp [haccN]

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

end RoseTreeMachine

end Turing
