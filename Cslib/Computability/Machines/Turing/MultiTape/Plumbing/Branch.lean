/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.StepLemmas
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Sum

/-!
# Branching on a work-tape symbol

`branch i x tm₁ tm₂` first reads the symbol under the head of work tape `i` and then, depending on
whether that symbol equals `some x`, behaves like `tm₁` or like `tm₂`, each started in its initial
state on the tapes as they were. This is a control combinator analogous to sequential composition
(`Plumbing/Sequential.lean`): the state space adds a fresh dispatch state on top of `State₁ ⊕
State₂`, the dispatch is one step that writes nothing and moves no head, and afterwards the machine
mirrors the chosen sub-machine through a left/right embedding just as `seq` mirrors its second
machine.

Because at a starting `wordsCfg` the head of every work tape sits at the start of its word, tape
`i`'s symbol there is exactly `(ws i).head?`, so the dispatch reads precisely the predicate the
specification branches on.

## Main results

* `Turing.MultiTapeTM.exists_transformsTapes_branch`: from two transformations sharing a
  postcondition, a single machine that runs one or the other according to the symbol under tape
  `i`, with the time bound `max t₁ t₂ + 1` and the space bound `max s₁ s₂ + k`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type*} {input : List Bool}

namespace Branch

/-- The tape holding `xs` reads `xs.head?` at its start cell. -/
private lemma tapeOfList_zero (xs : List Bool) : tapeOfList xs 0 = xs.head? := by
  have h : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [h, tapeOfList_ofNat]
  cases xs <;> rfl

/-- The branching machine. State `none` is a fresh dispatch state: it reads the symbol under tape
`i`'s head and, in one step that writes nothing and moves no head, jumps to `tm₁`'s initial state
(if the symbol is `some x`) or `tm₂`'s (otherwise). Thereafter it mirrors the chosen machine, its
states carried by `Sum.inl`/`Sum.inr`. -/
private def branch (i : Fin k) (x : Bool) (tm₁ : MultiTapeTM k Bool S₁)
    (tm₂ : MultiTapeTM k Bool S₂) : MultiTapeTM k Bool (Option (S₁ ⊕ S₂)) where
  q₀ := none
  tr q inp work :=
    match q with
    | none =>
      { inputTape := 0
        workTapes := fun _ => (none, 0)
        output := none
        state := if work i = some x then some (some (Sum.inl tm₁.q₀))
          else some (some (Sum.inr tm₂.q₀)) }
    | some (Sum.inl q₁) =>
      let a := tm₁.tr q₁ inp work
      { a with state := a.state.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂))) }
    | some (Sum.inr q₂) =>
      let a := tm₂.tr q₂ inp work
      { a with state := a.state.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂))) }

variable {i : Fin k} {x : Bool} {tm₁ : MultiTapeTM k Bool S₁} {tm₂ : MultiTapeTM k Bool S₂}

/-- A configuration of `tm₁`, embedded into the branching machine: a halted state stays halted, a
live state is carried by `Sum.inl`. -/
private def leftCfg (cfg : Cfg k Bool S₁ input) : Cfg k Bool (Option (S₁ ⊕ S₂)) input :=
  ⟨cfg.state.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂))), cfg.inputPos, cfg.workTapes,
    cfg.workTapePos, cfg.output⟩

/-- A configuration of `tm₂`, embedded into the branching machine. -/
private def rightCfg (cfg : Cfg k Bool S₂ input) : Cfg k Bool (Option (S₁ ⊕ S₂)) input :=
  ⟨cfg.state.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂))), cfg.inputPos, cfg.workTapes,
    cfg.workTapePos, cfg.output⟩

@[simp]
private lemma workTapePos_leftCfg (cfg : Cfg k Bool S₁ input) :
    (leftCfg (S₂ := S₂) cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
private lemma workTapePos_rightCfg (cfg : Cfg k Bool S₂ input) :
    (rightCfg (S₁ := S₁) cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
private lemma leftCfg_wordsCfg (q : Option S₁) (ws : Fin k → List Bool) (out : List Bool) :
    leftCfg (S₂ := S₂) (wordsCfg input q ws out) =
      wordsCfg input (q.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂)))) ws out := rfl

@[simp]
private lemma rightCfg_wordsCfg (q : Option S₂) (ws : Fin k → List Bool) (out : List Bool) :
    rightCfg (S₁ := S₁) (wordsCfg input q ws out) =
      wordsCfg input (q.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂)))) ws out := rfl

/-- On `tm₁`'s configurations, the branching machine mirrors `tm₁` step for step. -/
private lemma step_leftCfg (cfg : Cfg k Bool S₁ input) :
    (branch i x tm₁ tm₂).step (leftCfg cfg) = leftCfg (tm₁.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt (by simp [leftCfg, hq]), step_of_halt hq]
  | some q =>
    have h1 : (leftCfg (S₂ := S₂) cfg).state = some (some (Sum.inl q)) := by simp [leftCfg, hq]
    simp only [step, h1, hq]
    rfl

/-- On `tm₂`'s configurations, the branching machine mirrors `tm₂` step for step. -/
private lemma step_rightCfg (cfg : Cfg k Bool S₂ input) :
    (branch i x tm₁ tm₂).step (rightCfg cfg) = rightCfg (tm₂.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt (by simp [rightCfg, hq]), step_of_halt hq]
  | some q =>
    have h1 : (rightCfg (S₁ := S₁) cfg).state = some (some (Sum.inr q)) := by simp [rightCfg, hq]
    simp only [step, h1, hq]
    rfl

private lemma runFrom_leftCfg (cfg : Cfg k Bool S₁ input) (n : ℕ) :
    (branch i x tm₁ tm₂).runFrom (leftCfg cfg) n = leftCfg (tm₁.runFrom cfg n) :=
  runFrom_comm_of_step leftCfg (fun c => step_leftCfg c) cfg n

private lemma runFrom_rightCfg (cfg : Cfg k Bool S₂ input) (n : ℕ) :
    (branch i x tm₁ tm₂).runFrom (rightCfg cfg) n = rightCfg (tm₂.runFrom cfg n) :=
  runFrom_comm_of_step rightCfg (fun c => step_rightCfg c) cfg n

/-- The dispatch step when the symbol under tape `i` is `some x`: it lands on `tm₁`'s initial
configuration, embedded on the left. -/
private lemma step_start_left (ws : Fin k → List Bool) (out : List Bool)
    (h : (ws i).head? = some x) :
    (branch i x tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      leftCfg (S₂ := S₂) (wordsCfg input (some tm₁.q₀) ws out) := by
  have hstate : (wordsCfg (State := Option (S₁ ⊕ S₂)) input (some none) ws out).state =
      some none := rfl
  rw [step_apply_of_state hstate]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [branch, Cfg.workTapeSymbols, tapeOfList_zero, h, leftCfg, wordsCfg, Action.apply,
      SignType.cast]

/-- The dispatch step when the symbol under tape `i` is not `some x`: it lands on `tm₂`'s initial
configuration, embedded on the right. -/
private lemma step_start_right (ws : Fin k → List Bool) (out : List Bool)
    (h : ¬ (ws i).head? = some x) :
    (branch i x tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      rightCfg (S₁ := S₁) (wordsCfg input (some tm₂.q₀) ws out) := by
  have hstate : (wordsCfg (State := Option (S₁ ⊕ S₂)) input (some none) ws out).state =
      some none := rfl
  rw [step_apply_of_state hstate]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [branch, Cfg.workTapeSymbols, tapeOfList_zero, h, rightCfg, wordsCfg, Action.apply,
      SignType.cast]

end Branch

open Branch in
/-- **Branching on a tape symbol.** Given two transformations that share a postcondition `Q`, a
single machine reads the symbol under the head of work tape `i`: if it is `some x` it performs the
first transformation, otherwise the second. The dispatch costs one step and, moving no head, at
most `k` cells, so the time bound is `max t₁ t₂ + 1` and the space bound `max s₁ s₂ + k`. -/
public theorem exists_transformsTapes_branch {J : Type*} {k : ℕ} (i : Fin k) (x : Bool)
    {State₁ State₂ : Type} [Finite State₁] [Finite State₂]
    {tm₁ : MultiTapeTM k Bool State₁} {tm₂ : MultiTapeTM k Bool State₂}
    {P₁ P₂ : J → (input : List Bool) → (Fin k → List Bool) → Prop}
    {Q : J → (input : List Bool) → (Fin k → List Bool) → (Fin k → List Bool) → Prop}
    {t₁ s₁ t₂ s₂ : J → ℕ}
    (h₁ : ∀ j, TransformsTapes tm₁ (P₁ j) (Q j) (t₁ j) (s₁ j))
    (h₂ : ∀ j, TransformsTapes tm₂ (P₂ j) (Q j) (t₂ j) (s₂ j)) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ j : J,
      TransformsTapes tm
        (fun input ws => if (ws i).head? = some x then P₁ j input ws else P₂ j input ws)
        (Q j) (max (t₁ j) (t₂ j) + 1) (max (s₁ j) (s₂ j) + k) := by
  refine ⟨Option (State₁ ⊕ State₂), inferInstance, branch i x tm₁ tm₂, fun j input ws out hP => ?_⟩
  -- the machine's initial state is the dispatch state `none`
  rw [show (branch i x tm₁ tm₂).q₀ = none from rfl]
  by_cases h : (ws i).head? = some x
  · -- read `some x`: run `tm₁`
    simp only [h] at hP
    obtain ⟨τ₁, hτ₁, ws', hrun₁, hQ₁, hsp₁⟩ := h₁ j input ws out hP
    have hstep1 : (branch i x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1 =
        leftCfg (S₂ := State₂) (wordsCfg input (some tm₁.q₀) ws out) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, runFrom_succ_eq_step', runFrom_zero,
        step_start_left ws out h]
    refine ⟨τ₁ + 1, by have := Nat.le_max_left (t₁ j) (t₂ j); omega, ws', ?_, hQ₁, ?_⟩
    · rw [runFrom_succ_eq_step, step_start_left ws out h, runFrom_leftCfg, hrun₁]
      simp
    · -- space: the dispatch adds at most `k` cells, `tm₁`'s run at most `s₁ j`
      have hsp1 : (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 ≤ k := by
        refine spaceUsed_le_of_workTapePos_const (wordsCfg input (some none) ws out) 1
          fun m _ => ?_
        rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
        · rw [runFrom_zero]
        · rw [hstep1]; rfl
      have hsp2 : (branch i x tm₁ tm₂).spaceUsed
          ((branch i x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ₁ ≤ s₁ j := by
        rw [hstep1]
        refine le_trans (le_of_eq
          (spaceUsed_eq_of_workTapePos (tm := branch i x tm₁ tm₂) (tm' := tm₁)
            (leftCfg (wordsCfg input (some tm₁.q₀) ws out)) (wordsCfg input (some tm₁.q₀) ws out)
            τ₁ fun m _ => ?_)) hsp₁
        rw [runFrom_leftCfg, workTapePos_leftCfg]
      calc (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (τ₁ + 1)
          = (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (1 + τ₁) := by
            rw [Nat.add_comm]
        _ ≤ (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 +
            (branch i x tm₁ tm₂).spaceUsed
              ((branch i x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ₁ :=
              spaceUsed_add_le (wordsCfg input (some none) ws out) 1 τ₁
        _ ≤ k + s₁ j := Nat.add_le_add hsp1 hsp2
        _ ≤ max (s₁ j) (s₂ j) + k := by have := Nat.le_max_left (s₁ j) (s₂ j); omega
  · -- read something else: run `tm₂`
    simp only [h] at hP
    obtain ⟨τ₂, hτ₂, ws', hrun₂, hQ₂, hsp₂⟩ := h₂ j input ws out hP
    have hstep1 : (branch i x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1 =
        rightCfg (S₁ := State₁) (wordsCfg input (some tm₂.q₀) ws out) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, runFrom_succ_eq_step', runFrom_zero,
        step_start_right ws out h]
    refine ⟨τ₂ + 1, by have := Nat.le_max_right (t₁ j) (t₂ j); omega, ws', ?_, hQ₂, ?_⟩
    · rw [runFrom_succ_eq_step, step_start_right ws out h, runFrom_rightCfg, hrun₂]
      simp
    · have hsp1 : (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 ≤ k := by
        refine spaceUsed_le_of_workTapePos_const (wordsCfg input (some none) ws out) 1
          fun m _ => ?_
        rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
        · rw [runFrom_zero]
        · rw [hstep1]; rfl
      have hsp2 : (branch i x tm₁ tm₂).spaceUsed
          ((branch i x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ₂ ≤ s₂ j := by
        rw [hstep1]
        refine le_trans (le_of_eq
          (spaceUsed_eq_of_workTapePos (tm := branch i x tm₁ tm₂) (tm' := tm₂)
            (rightCfg (wordsCfg input (some tm₂.q₀) ws out)) (wordsCfg input (some tm₂.q₀) ws out)
            τ₂ fun m _ => ?_)) hsp₂
        rw [runFrom_rightCfg, workTapePos_rightCfg]
      calc (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (τ₂ + 1)
          = (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (1 + τ₂) := by
            rw [Nat.add_comm]
        _ ≤ (branch i x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 +
            (branch i x tm₁ tm₂).spaceUsed
              ((branch i x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ₂ :=
              spaceUsed_add_le (wordsCfg input (some none) ws out) 1 τ₂
        _ ≤ k + s₂ j := Nat.add_le_add hsp1 hsp2
        _ ≤ max (s₁ j) (s₂ j) + k := by have := Nat.le_max_right (s₁ j) (s₂ j); omega

end Turing.MultiTapeTM
