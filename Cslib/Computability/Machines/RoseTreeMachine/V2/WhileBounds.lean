/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V2.Tools
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred

/-! # RoseTreeMachine V2 — Resource bounds for `while_`

Foundation lemmas describing how `Prog.while_` / `PB.while_` consume time and
space along a known trajectory, and a high-level complexity spec saying that a
linear-cost body with constant accumulator growth yields linear-space and
quadratic-time loops.

Part of the RoseTreeMachine V2 development; see
`Cslib/Computability/Machines/RoseTreeMachine/V2.lean` for an overview.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-! ### Foundation lemma: metered `while_` along a known trajectory

Given a trajectory `acc 0, acc 1, …, acc N` such that `body.meteredEval` carries
`acc k` to `acc (k+1)` with cost `(bt k, bs k)` for each `k < N`, that the halt
condition fails at every `acc k` for `k < N` and holds at `acc N`, and that
`init` evaluates to `acc 0` with metered cost `(i_t, i_s)`, then
`(Prog.while_ init body).meteredEval env` is fully determined.

All future `PB.usesO*`/`outputsOSize` lemmas about `PB.while_` factor through
this.
-/

/-- Continuity of `metered_F`, parallel to `Prog.whileFrom_eval_continuous`. -/
private lemma Prog.metered_F_continuous (body : Prog) (env : List Data) :
    OmegaCompletePartialOrder.ωScottContinuous (Prog.metered_F body env) := by
  apply OmegaCompletePartialOrder.ωScottContinuous.of_apply₂
  intro ⟨acc, t, s⟩
  unfold Prog.metered_F
  simp only
  by_cases h : acc.asList.headD (Data.l []) = Data.l []
  · simp only [h, if_true]
    exact OmegaCompletePartialOrder.ωScottContinuous.const
  · simp only [h, if_false]
    exact OmegaCompletePartialOrder.ContinuousHom.ωScottContinuous.bind
      OmegaCompletePartialOrder.ωScottContinuous.const
      (OmegaCompletePartialOrder.ωScottContinuous.of_apply₂
        (fun _ => OmegaCompletePartialOrder.ωScottContinuous.id.apply₂ _))

/-- Halt-step unrolling for `Part.fix (metered_F …)`. -/
lemma Prog.metered_fix_halt {body : Prog} {env : List Data}
    {acc : Data} {t s : ℕ}
    (h_halt : acc.asList.headD (Data.l []) = Data.l []) :
    Part.fix (Prog.metered_F body env) (acc, t, s) = .some (acc, t, s) := by
  conv_lhs =>
    rw [Part.fix_eq_of_ωScottContinuous (Prog.metered_F_continuous body env)]
  unfold Prog.metered_F
  simp only [h_halt, if_true]

/-- Body-step unrolling for `Part.fix (metered_F …)`. -/
lemma Prog.metered_fix_step {body : Prog} {env : List Data}
    {acc : Data} {t s : ℕ}
    (h_step : acc.asList.headD (Data.l []) ≠ Data.l []) :
    Part.fix (Prog.metered_F body env) (acc, t, s) =
      (body.meteredEval (env ++ [acc])).bind fun y =>
        Part.fix (Prog.metered_F body env) (y.1, t + 1 + y.2.1, max s y.2.2) := by
  conv_lhs =>
    rw [Part.fix_eq_of_ωScottContinuous (Prog.metered_F_continuous body env)]
  unfold Prog.metered_F
  simp only [h_step, if_false]

/-- **Foundation lemma.** Metered evaluation of `Part.fix (metered_F body env)`
starting from `(acc 0, t₀, s₀)` along a known body-trajectory of length `N`. -/
lemma Prog.metered_fix_trajectory {body : Prog} {env : List Data}
    (acc : ℕ → Data) (bt bs : ℕ → ℕ) (N : ℕ)
    (h_step : ∀ k < N,
        (acc (k + 1), bt k, bs k) ∈ body.meteredEval (env ++ [acc k]))
    (h_no_halt : ∀ k < N, (acc k).asList.headD (Data.l []) ≠ Data.l [])
    (h_halt : (acc N).asList.headD (Data.l []) = Data.l []) :
    ∀ k ≤ N, ∀ t s,
      Part.fix (Prog.metered_F body env) (acc k, t, s) =
        .some
          ( acc N
          , (Finset.Ico k N).sum (fun j => 1 + bt j) + t
          , (Finset.Ico k N).fold max s bs ) := by
  -- Helper: pushing an extra max-arg into the fold accumulator.
  have fold_max_acc : ∀ (S : Finset ℕ) (b c : ℕ),
      S.fold max (max b c) bs = max c (S.fold max b bs) := by
    intro S b c
    induction S using Finset.induction with
    | empty => simp [max_comm]
    | insert _ _ hmem ih =>
      simp [Finset.fold_insert hmem, ih, max_left_comm]
  intro k hk
  induction hd : N - k generalizing k with
  | zero =>
    have hkN : k = N := by omega
    subst hkN
    intro t s
    simp [Prog.metered_fix_halt h_halt]
  | succ m ih =>
    have hk' : k < N := by omega
    intro t s
    rw [Prog.metered_fix_step (h_no_halt k hk')]
    rw [Part.eq_some_iff.mpr (h_step k hk')]
    simp only [Part.bind_some]
    rw [ih (k+1) (by omega) (by omega) (t + 1 + bt k) (max s (bs k))]
    congr 1
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · rw [show Finset.Ico k N = insert k (Finset.Ico (k+1) N) from
            (Finset.insert_Ico_succ_left_eq_Ico hk').symm,
          Finset.sum_insert (by simp)]
      ac_rfl
    · rw [show Finset.Ico k N = insert k (Finset.Ico (k+1) N) from
            (Finset.insert_Ico_succ_left_eq_Ico hk').symm,
          Finset.fold_insert (by simp), fold_max_acc]

/-- **Foundation lemma (entry point).** Metered evaluation of `Prog.while_ init body`
along a known trajectory: if `init` produces `acc 0` with cost `(i_t, i_s)` and
`body` carries `acc k` to `acc (k+1)` with cost `(bt k, bs k)` for `k < N`,
halting exactly at `acc N`, then the whole metered cost is fully determined. -/
lemma Prog.while_meteredEval_trajectory {init body : Prog} {env : List Data}
    (acc : ℕ → Data) (i_t i_s : ℕ) (bt bs : ℕ → ℕ) (N : ℕ)
    (h_init : (acc 0, i_t, i_s) ∈ init.meteredEval env)
    (h_step : ∀ k < N,
        (acc (k+1), bt k, bs k) ∈ body.meteredEval (env ++ [acc k]))
    (h_no_halt : ∀ k < N, (acc k).asList.headD (Data.l []) ≠ Data.l [])
    (h_halt : (acc N).asList.headD (Data.l []) = Data.l []) :
    (Prog.while_ init body).meteredEval env =
      .some
        ( acc N
        , (Finset.Ico 0 N).sum (fun j => 1 + bt j) + (1 + i_t)
        , (Finset.Ico 0 N).fold max (max 1 i_s) bs ) := by
  have hmEq : (Prog.while_ init body).meteredEval env =
      (init.meteredEval env).bind (fun x =>
        Part.fix (Prog.metered_F body env) (x.1, 1 + x.2.1, max 1 x.2.2)) := by
    rw [Prog.meteredEval]; rfl
  rw [hmEq, Part.eq_some_iff.mpr h_init, Part.bind_some]
  simpa using Prog.metered_fix_trajectory acc bt bs N h_step h_no_halt h_halt 0
      (Nat.zero_le _) (1 + i_t) (max 1 i_s)

/-! ### Complexity spec for `PB.while_`

Conjecture: if `init` and `body` each use linear time and space, the body
semantically computes `f` (uniformly in the env), and `f` grows the encoded
accumulator by at most a constant `Δ` per iteration, then running
`PB.while_ p_init body` for `N` iterations uses

* **space**  linear in `|env| + N`
* **time**   quadratic in `|env| + N`  (≈ `|env|·N + N²`)

Intuition: at iteration `k` the accumulator has size `≤ |init| + k·Δ`, so the
body's per-iteration cost (linear in the env-with-accumulator) is `O(|env| + k)`;
summing for `k = 0 … N-1` gives `O(|env|·N + N²)` time and `O(|env| + N)` peak
space.
-/

/-- Generic complexity spec for `PB.while_`. -/
lemma PB.while_uses_linear_space_quadratic_time
    {α : Type} [DataEncode α]
    {p_init : PB} {body : PB → PB}
    {f : α → α} {init : α}
    -- Body semantically computes `f` on every env (env-uniform link f ↔ body).
    (h_init_sem : ∀ env, p_init.computes_at_encoded env init)
    (h_body_sem : ∀ env c, PB.computes_at_body₁_encoded env c body (f c))
    -- Linearity of `init`. The body needs *uniform-in-`i`* concrete constants
    -- (not big-O), since the loop spans many slots and we need a single bound.
    (h_init_lin : p_init.usesLinearTimeAndSpace)
    (h_body_lin : ∃ a b, ∀ i env,
        ∃ d t s, ((body (PB.atSlot i)) env.length).meteredEval env = .some (d, t, s) ∧
          t ≤ a * (Data.l env).size + b ∧ s ≤ a * (Data.l env).size + b)
    -- Constant accumulator-size growth per body iteration (semantic side).
    (Δ : ℕ)
    (h_growth : ∀ c : α,
        (DataEncode.encode (f c)).size ≤ (DataEncode.encode c).size + Δ)
    -- The loop halts after exactly `N` iterations starting from `init`.
    (N : ℕ)
    (h_halt : (DataEncode.encode (f^[N] init)).asList.headD (Data.l []) = Data.l [])
    (h_min  : ∀ k < N,
        (DataEncode.encode (f^[k] init)).asList.headD (Data.l []) ≠ Data.l []) :
    PB.usesOSpace (PB.while_ p_init body)
        (fun env => (Data.l env).size + N) ∧
    PB.usesOTime (PB.while_ p_init body)
        (fun env => (Data.l env).size * N + N * N + 1) := by
  -- Convenient abbreviation for the trajectory.
  let acc : ℕ → Data := fun k => DataEncode.encode (f^[k] init)
  -- Per-iteration accumulator-size bound.
  have h_acc_size : ∀ k, (acc k).size ≤ (DataEncode.encode init).size + k * Δ := by
    intro k
    induction k with
    | zero => simp [acc]
    | succ k ih =>
      have hgrow := h_growth (f^[k] init)
      have heq : acc (k+1) = DataEncode.encode (f (f^[k] init)) := by
        simp [acc, Function.iterate_succ_apply']
      rw [heq]
      have : (acc k) = DataEncode.encode (f^[k] init) := rfl
      have h1 : (DataEncode.encode (f (f^[k] init))).size ≤
          (DataEncode.encode (f^[k] init)).size + Δ := hgrow
      have h2 : (DataEncode.encode (f^[k] init)).size = (acc k).size := rfl
      rw [Nat.succ_mul]
      omega
  -- Unpack the linearity hypotheses into explicit constants.
  obtain ⟨a_it, b_it, h_init_t⟩ := h_init_lin.1
  obtain ⟨a_is, b_is, h_init_s⟩ := h_init_lin.2
  obtain ⟨a_b, b_b, h_body_lin'⟩ := h_body_lin
  -- Convenience: the initial encoded value's size as a constant.
  set Si : ℕ := (DataEncode.encode init).size with Si_def
  -- ------------------------------------------------------------------
  -- Per-env construction of the trajectory using the foundation lemma.
  -- This builds, for any `env`, a metered evaluation of `PB.while_ p_init body`
  -- at depth `env.length`, returning the explicit cost tuple.
  -- ------------------------------------------------------------------
  have trajectory_eval :
      ∀ env : List Data,
      ∃ (bt bs : ℕ → ℕ),
        (∀ k < N,
            bt k ≤ a_b * ((Data.l env).size + (acc k).size) + b_b ∧
            bs k ≤ a_b * ((Data.l env).size + (acc k).size) + b_b) ∧
        ∃ (i_t i_s : ℕ),
          i_t ≤ a_it * (Data.l env).size + b_it ∧
          i_s ≤ a_is * (Data.l env).size + b_is ∧
          ((PB.while_ p_init body) env.length).meteredEval env =
            .some
              ( acc N
              , (Finset.Ico 0 N).sum (fun j => 1 + bt j) + (1 + i_t)
              , (Finset.Ico 0 N).fold max (max 1 i_s) bs ) := by
    intro env
    let n := env.length
    have h_init_eval : (p_init n).eval env = .some (acc 0) :=
      PB.computes_at.here (h_init_sem env)
    obtain ⟨i_t, i_s, h_init_m⟩ := Prog.eval_some_iff_meteredEval.mp h_init_eval
    obtain ⟨i_t', h_i_t_le, h_i_t_eval⟩ := h_init_t env
    obtain ⟨i_s', h_i_s_le, h_i_s_eval⟩ := h_init_s env
    have h_it_eq : i_t = i_t' := by
      rw [h_init_m, Part.map_some] at h_i_t_eval; exact Part.some_inj.mp h_i_t_eval
    have h_is_eq : i_s = i_s' := by
      rw [h_init_m, Part.map_some] at h_i_s_eval; exact Part.some_inj.mp h_i_s_eval
    -- Specialize body's uniform metered-bound to slot `n`.
    -- For each k, get the body's metered eval at env ++ [acc k] and its bound.
    have body_step_data : ∀ k,
        ∃ bt_k bs_k : ℕ,
          (body (PB.atSlot n) (n + 1)).meteredEval (env ++ [acc k]) =
            .some (acc (k+1), bt_k, bs_k) ∧
          bt_k ≤ a_b * (Data.l (env ++ [acc k])).size + b_b ∧
          bs_k ≤ a_b * (Data.l (env ++ [acc k])).size + b_b := by
      intro k
      have h_body_eval :
          (body (PB.atSlot n) (n + 1)).eval (env ++ [acc k]) = .some (acc (k+1)) := by
        have h1 := PB.computes_at.here ((h_body_sem env (f^[k] init)) [])
        simp only [List.append_nil, List.length_append, List.length_singleton,
                   Nat.add_zero] at h1
        have hacc : acc (k+1) = DataEncode.encode (f (f^[k] init)) := by
          show DataEncode.encode (f^[k+1] init) = _
          rw [Function.iterate_succ_apply']
        rw [hacc]; exact h1
      obtain ⟨bt_k, bs_k, h_body_m⟩ := Prog.eval_some_iff_meteredEval.mp h_body_eval
      obtain ⟨d', t', s', h_body_eval', h_t_le, h_s_le⟩ :=
        h_body_lin' n (env ++ [acc k])
      have hlen : (env ++ [acc k]).length = n + 1 := by
        rw [List.length_append, List.length_singleton]
      rw [hlen] at h_body_eval'
      have htriple : (acc (k+1), bt_k, bs_k) = (d', t', s') :=
        Part.some_inj.mp (h_body_m.symm.trans h_body_eval')
      refine ⟨bt_k, bs_k, h_body_m, ?_, ?_⟩ <;> grind
    -- Collect the per-step data into functions.
    choose bt bs h_meval h_bt_le h_bs_le using body_step_data
    refine ⟨bt, bs, ?_, i_t, i_s, h_it_eq ▸ h_i_t_le, h_is_eq ▸ h_i_s_le, ?_⟩
    · intro k _hk
      have hsize : (Data.l (env ++ [acc k])).size =
          (Data.l env).size + (acc k).size := by
        simp [Data.size, List.map_append]; omega
      have ht := h_bt_le k
      have hs := h_bs_le k
      grind
    · show (Prog.while_ (p_init n) (body (PB.atSlot n) (n + 1))).meteredEval env = _
      apply Prog.while_meteredEval_trajectory acc i_t i_s bt bs N
        (Part.eq_some_iff.mp h_init_m)
      · intro k _; rw [h_meval k]; exact Part.mem_some _
      · exact h_min
      · exact h_halt
  -- Helper: bound `Finset.fold max` by a uniform bound on initial and elements.
  have fold_max_le : ∀ (S : Finset ℕ) (b : ℕ) (g : ℕ → ℕ) (M : ℕ),
      b ≤ M → (∀ k ∈ S, g k ≤ M) → S.fold max b g ≤ M := by
    intro S b g M hb hg
    induction S using Finset.induction with
    | empty => simpa
    | insert a S ha ih =>
      rw [Finset.fold_insert ha]
      have hgm := hg a (by simp)
      have := ih (fun k hk => hg k (by simp [hk]))
      exact max_le hgm this
  -- ============================ SPACE ============================
  refine ⟨?_, ?_⟩
  · -- Choose the linear-bound constants.
    refine ⟨max a_is a_b,
            1 + b_is + a_b * (Si + N * Δ) + b_b + 1, ?_⟩
    intro env
    obtain ⟨bt, bs, h_step_le, i_t, i_s, h_it_le, h_is_le, h_eval⟩ :=
      trajectory_eval env
    -- The space output is `fold max (max 1 i_s) bs (Ico 0 N)`.
    refine ⟨_, ?_, by rw [h_eval, Part.map_some]⟩
    -- Bound the fold by a uniform linear bound on initial and elements.
    have h_a_b_le : a_b ≤ max a_is a_b := le_max_right _ _
    have h_a_is_le : a_is ≤ max a_is a_b := le_max_left _ _
    have hmul_env : ∀ c : ℕ, c * (Data.l env).size ≤ c * ((Data.l env).size + N) :=
      fun _ => Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    apply fold_max_le
    · -- Bound `max 1 i_s`.
      have := Nat.mul_le_mul_right ((Data.l env).size + N) h_a_is_le
      grind
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hsum : (acc k).size ≤ Si + N * Δ := by
        have := h_acc_size k
        have := Nat.mul_le_mul_right Δ (le_of_lt hk.2)
        omega
      have hmul_acc : a_b * ((Data.l env).size + (acc k).size) ≤
          a_b * (Data.l env).size + a_b * (Si + N * Δ) :=
        le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hsum _))
          (Nat.mul_add _ _ _).le
      have := Nat.mul_le_mul_right (Data.l env).size h_a_b_le
      grind
  · -- ============================ TIME =============================
    sorry

end RoseTreeMachine

end Turing
