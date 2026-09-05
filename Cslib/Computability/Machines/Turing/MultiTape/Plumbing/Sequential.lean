/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.PFun
public import Mathlib.Data.List.Infix
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic

/-!
# Sequential composition of Turing machines

`seq tm₁ tm₂` runs `tm₁` and, instead of halting, continues with `tm₂` on the configuration
reached by `tm₁`: the input head position, the work tapes, the work tape heads and the output
produced so far are all handed over unchanged. This is not composition of the computed functions,
but composition of the machines as transformers of configurations.

## Main definitions

* `Turing.MultiTapeTM.seq`: the sequential composition of two machines.
* `Turing.MultiTapeTM.Cfg.withState`: a configuration with its state replaced, used to relate
  configurations of `tm₁` and `tm₂` with those of `seq tm₁ tm₂`.

## Main results

* `Turing.MultiTapeTM.runFrom_seq`: if `tm₁` halts after `t₁` steps, then after `t₁ + t₂` steps
  `seq tm₁ tm₂` is in the configuration that `tm₂` reaches after `t₂` steps when started in the
  configuration left behind by `tm₁`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State₁ State₂ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₁` and `tm₂`: it behaves like `tm₁` until `tm₁` would halt,
at which point it switches to the initial state of `tm₂` and behaves like `tm₂`. All other
components of the configuration are left untouched by the switch. -/
@[expose]
public def seq (tm₁ : MultiTapeTM k Symbol State₁) (tm₂ : MultiTapeTM k Symbol State₂) :
    MultiTapeTM k Symbol (State₁ ⊕ State₂) where
  q₀ := .inl tm₁.q₀
  tr q input work :=
    match q with
    | .inl q₁ =>
      let action := tm₁.tr q₁ input work
      { action with q' := some (action.q'.elim (.inr tm₂.q₀) .inl) }
    | .inr q₂ =>
      let action := tm₂.tr q₂ input work
      { action with q' := action.q'.map .inr }

variable {tm₁ : MultiTapeTM k Symbol State₁} {tm₂ : MultiTapeTM k Symbol State₂}

/-- `seq tm₁ tm₂` starts in the initial configuration of `tm₁`. -/
@[simp]
public lemma initCfg_seq (input : List Symbol) :
    (tm₁.seq tm₂).initCfg input = (tm₁.initCfg input).withState (some (Sum.inl tm₁.q₀)) := rfl

/-- In the second phase, `seq tm₁ tm₂` performs the steps of `tm₂`. -/
public lemma step_seq_inr (cfg : Cfg k Symbol State₂ input) :
    (tm₁.seq tm₂).step (cfg.withState (cfg.state.map Sum.inr)) =
      (tm₂.step cfg).withState ((tm₂.step cfg).state.map Sum.inr) := by
  cases h : cfg.state with
  | none => simp [step, h]
  | some q => refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [step, seq, h]

/-- In the second phase, `seq tm₁ tm₂` performs the runs of `tm₂`. -/
public lemma runFrom_seq_inr (cfg : Cfg k Symbol State₂ input) (t : ℕ) :
    (tm₁.seq tm₂).runFrom (cfg.withState (cfg.state.map Sum.inr)) t =
      (tm₂.runFrom cfg t).withState ((tm₂.runFrom cfg t).state.map Sum.inr) := by
  induction t with
  | zero => simp [runFrom_zero]
  | succ t ih =>
    rw [runFrom_succ_eq_step', ih, step_seq_inr, ← runFrom_succ_eq_step' (tm := tm₂)]

/-- As long as `tm₁` does not halt, `seq tm₁ tm₂` performs the steps of `tm₁`. -/
public lemma step_seq_inl_of_ne_none {cfg : Cfg k Symbol State₁ input}
    (h : (tm₁.step cfg).state ≠ none) :
    (tm₁.seq tm₂).step (cfg.withState (cfg.state.map Sum.inl)) =
      (tm₁.step cfg).withState ((tm₁.step cfg).state.map Sum.inl) := by
  cases hcfg : cfg.state with
  | none => simp [step, hcfg]
  | some q =>
    have hq : (tm₁.tr q cfg.inputSymbol cfg.workTapeSymbols).q' ≠ none := by
      simpa [step, hcfg] using h
    cases hq' : (tm₁.tr q cfg.inputSymbol cfg.workTapeSymbols).q' with
    | none => exact absurd hq' hq
    | some q' => refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [step, seq, hcfg, hq']

/-- The step in which `tm₁` halts is the step in which `seq tm₁ tm₂` switches to `tm₂`. -/
public lemma step_seq_inl_of_halt {cfg : Cfg k Symbol State₁ input} (hcfg : cfg.state ≠ none)
    (h : (tm₁.step cfg).state = none) :
    (tm₁.seq tm₂).step (cfg.withState (cfg.state.map Sum.inl)) =
      (tm₁.step cfg).withState (some (Sum.inr tm₂.q₀)) := by
  cases hq : cfg.state with
  | none => exact absurd hq hcfg
  | some q =>
    have hq' : (tm₁.tr q cfg.inputSymbol cfg.workTapeSymbols).q' = none := by
      simpa [step, hq] using h
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [step, seq, hq, hq']

/-- As long as `tm₁` does not halt, `seq tm₁ tm₂` performs the runs of `tm₁`. -/
public lemma runFrom_seq_inl {cfg : Cfg k Symbol State₁ input} {t : ℕ}
    (h : ∀ τ ≤ t, (tm₁.runFrom cfg τ).state ≠ none) :
    (tm₁.seq tm₂).runFrom (cfg.withState (cfg.state.map Sum.inl)) t =
      (tm₁.runFrom cfg t).withState ((tm₁.runFrom cfg t).state.map Sum.inl) := by
  induction t with
  | zero => simp [runFrom_zero]
  | succ t ih =>
    rw [runFrom_succ_eq_step', ih fun τ hτ => h τ (by omega), runFrom_succ_eq_step' (tm := tm₁)]
    exact step_seq_inl_of_ne_none (by
      rw [← runFrom_succ_eq_step']
      exact h (t + 1) le_rfl)

/-- **Correctness of sequential composition.** If `tm₁` halts after exactly `t₁` steps, then after
`t₁ + t₂` steps `seq tm₁ tm₂` is in the configuration reached by `tm₂` after `t₂` steps, started
in the configuration `tm₁` left behind. -/
public theorem runFrom_seq {cfg : Cfg k Symbol State₁ input} {t₁ : ℕ} (hcfg : cfg.state ≠ none)
    (hmin : ∀ τ < t₁, (tm₁.runFrom cfg τ).state ≠ none)
    (hhalt : (tm₁.runFrom cfg t₁).state = none) (t₂ : ℕ) :
    (tm₁.seq tm₂).runFrom (cfg.withState (cfg.state.map Sum.inl)) (t₁ + t₂) =
      (tm₂.runFrom ((tm₁.runFrom cfg t₁).withState (some tm₂.q₀)) t₂).withState
        ((tm₂.runFrom ((tm₁.runFrom cfg t₁).withState (some tm₂.q₀)) t₂).state.map Sum.inr) := by
  obtain ⟨m, rfl⟩ : ∃ m, t₁ = m + 1 := by
    cases t₁ with
    | zero => exact absurd (by simpa [runFrom_zero] using hhalt) hcfg
    | succ m => exact ⟨m, rfl⟩
  have hstep : (tm₁.step (tm₁.runFrom cfg m)).state = none := by
    rwa [← runFrom_succ_eq_step']
  have hswitch : (tm₁.seq tm₂).runFrom (cfg.withState (cfg.state.map Sum.inl)) (m + 1) =
      (tm₁.runFrom cfg (m + 1)).withState (some (Sum.inr tm₂.q₀)) := by
    rw [runFrom_add _ m 1, runFrom_seq_inl (fun τ hτ => hmin τ (by omega)),
      runFrom_succ_eq_step', runFrom_zero,
      step_seq_inl_of_halt (hmin m (by omega)) hstep, ← runFrom_succ_eq_step']
  rw [runFrom_add _ (m + 1) t₂, hswitch]
  exact runFrom_seq_inr ((tm₁.runFrom cfg (m + 1)).withState (some tm₂.q₀)) t₂

/-- **Sequential composition of two transformations.** If `tm₁` transforms configurations
satisfying `P₁` into configurations satisfying `Q₁`, and `tm₂` continues from there, then
`seq tm₁ tm₂` performs both transformations one after the other. -/
proof_wanted transformsCfg_seq {k : ℕ} {Symbol State₁ State₂ : Type*}
    {tm₁ : MultiTapeTM k Symbol State₁} {tm₂ : MultiTapeTM k Symbol State₂} {S₁ S₂ : Finset (Fin k)}
    {P₁ : (input : List Symbol) → Tapes k Symbol input → Prop}
    {Q₁ Q₂ : (input : List Symbol) → Tapes k Symbol input → Tapes k Symbol input → Prop}
    {P₂ : (input : List Symbol) → Tapes k Symbol input → Prop} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : TransformsCfg tm₁ S₁ P₁ Q₁ t₁ s₁) (h₂ : TransformsCfg tm₂ S₂ P₂ Q₂ t₂ s₂)
    (hmid : ∀ input tp tp', P₁ input tp → Q₁ input tp tp' → P₂ input tp') :
    TransformsCfg (tm₁.seq tm₂) (S₁ ∪ S₂) P₁
      (fun input tp tp'' => ∃ tp', Q₁ input tp tp' ∧ Q₂ input tp' tp'') (t₁ + t₂) (s₁ + s₂)

end Turing.MultiTapeTM
