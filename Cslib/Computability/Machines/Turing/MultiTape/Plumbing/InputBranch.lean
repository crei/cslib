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
# Branching on the input's first symbol

`inputBranch x tm₁ tm₂` first reads the symbol under the input head and then, depending on whether
that symbol equals `some x`, behaves like `tm₁` or like `tm₂`, each started in its initial state on
the tapes as they were. It is the input-tape analogue of `Plumbing/Branch.lean`: the dispatch reads
the *input* symbol rather than a work-tape symbol, so the two arms then read the whole input in
place — the dispatch step writes nothing and moves no head — and may emit their result straight to
the real output tape.

At a starting `wordsCfg` the input head sits at the first input symbol, so the dispatch reads
exactly `input.head?`, the predicate the specification branches on.

## Main results

* `Turing.MultiTapeTM.exists_inputBranch_run`: a single machine that reads the input's first symbol
  and runs one of two given machines to completion — output included — plus one dispatch step.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type*} {input : List Bool}

/-- The symbol under the input head of a `wordsCfg` is the input's first symbol: the head is at
position `1`, over `input[0]` when the input is nonempty and at the right boundary otherwise. -/
public lemma inputSymbol_wordsCfg {State : Type*} (input : List Bool) (q : Option State)
    (ws : Fin k → List Bool) (out : List Bool) :
    (wordsCfg input q ws out).inputSymbol = input.head? := by
  cases input with
  | nil => simp only [wordsCfg, Cfg.inputSymbol]; rfl
  | cons b t =>
    rw [inputSymbolInner 0 (by simp [wordsCfg]) (by simp)]
    simp

namespace InputBranch

/-- The input-branching machine. State `none` is a fresh dispatch state: it reads the symbol under
the input head and, in one step that writes nothing and moves no head, jumps to `tm₁`'s initial
state (if the symbol is `some x`) or `tm₂`'s (otherwise). Thereafter it mirrors the chosen machine,
its states carried by `Sum.inl`/`Sum.inr`. -/
private def inputBranch (x : Bool) (tm₁ : MultiTapeTM k Bool S₁)
    (tm₂ : MultiTapeTM k Bool S₂) : MultiTapeTM k Bool (Option (S₁ ⊕ S₂)) where
  q₀ := none
  tr q inp work :=
    match q with
    | none =>
      { inputTape := 0
        workTapes := fun _ => (none, 0)
        output := none
        state := if inp = some x then some (some (Sum.inl tm₁.q₀))
          else some (some (Sum.inr tm₂.q₀)) }
    | some (Sum.inl q₁) =>
      let a := tm₁.tr q₁ inp work
      { a with state := a.state.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂))) }
    | some (Sum.inr q₂) =>
      let a := tm₂.tr q₂ inp work
      { a with state := a.state.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂))) }

variable {x : Bool} {tm₁ : MultiTapeTM k Bool S₁} {tm₂ : MultiTapeTM k Bool S₂}

/-- A configuration of `tm₁`, embedded into the branching machine. -/
private def leftCfg (cfg : Cfg k Bool S₁ input) : Cfg k Bool (Option (S₁ ⊕ S₂)) input :=
  cfg.mapState (Option.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂))))

/-- A configuration of `tm₂`, embedded into the branching machine. -/
private def rightCfg (cfg : Cfg k Bool S₂ input) : Cfg k Bool (Option (S₁ ⊕ S₂)) input :=
  cfg.mapState (Option.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂))))

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
    (inputBranch x tm₁ tm₂).step (leftCfg cfg) = leftCfg (tm₁.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt (by simp [leftCfg, hq]), step_of_halt hq]
  | some q =>
    have h1 : (leftCfg (S₂ := S₂) cfg).state = some (some (Sum.inl q)) := by simp [leftCfg, hq]
    simp only [step, h1, hq]
    rfl

/-- On `tm₂`'s configurations, the branching machine mirrors `tm₂` step for step. -/
private lemma step_rightCfg (cfg : Cfg k Bool S₂ input) :
    (inputBranch x tm₁ tm₂).step (rightCfg cfg) = rightCfg (tm₂.step cfg) := by
  cases hq : cfg.state with
  | none =>
    rw [step_of_halt (by simp [rightCfg, hq]), step_of_halt hq]
  | some q =>
    have h1 : (rightCfg (S₁ := S₁) cfg).state = some (some (Sum.inr q)) := by simp [rightCfg, hq]
    simp only [step, h1, hq]
    rfl

private lemma runFrom_leftCfg (cfg : Cfg k Bool S₁ input) (n : ℕ) :
    (inputBranch x tm₁ tm₂).runFrom (leftCfg cfg) n = leftCfg (tm₁.runFrom cfg n) :=
  runFrom_comm_of_step leftCfg (fun c => step_leftCfg c) cfg n

private lemma runFrom_rightCfg (cfg : Cfg k Bool S₂ input) (n : ℕ) :
    (inputBranch x tm₁ tm₂).runFrom (rightCfg cfg) n = rightCfg (tm₂.runFrom cfg n) :=
  runFrom_comm_of_step rightCfg (fun c => step_rightCfg c) cfg n

/-- The dispatch step when the input's first symbol is `some x`: it lands on `tm₁`'s initial
configuration, embedded on the left. -/
private lemma step_start_left (ws : Fin k → List Bool) (out : List Bool)
    (h : input.head? = some x) :
    (inputBranch x tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      leftCfg (S₂ := S₂) (wordsCfg input (some tm₁.q₀) ws out) := by
  have hstate : (wordsCfg (State := Option (S₁ ⊕ S₂)) input (some none) ws out).state =
      some none := rfl
  rw [step_apply_of_state hstate, inputSymbol_wordsCfg]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [inputBranch, h, leftCfg, Cfg.mapState, wordsCfg, Action.apply, SignType.cast]

/-- The dispatch step when the input's first symbol is not `some x`: it lands on `tm₂`'s initial
configuration, embedded on the right. -/
private lemma step_start_right (ws : Fin k → List Bool) (out : List Bool)
    (h : ¬ input.head? = some x) :
    (inputBranch x tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      rightCfg (S₁ := S₁) (wordsCfg input (some tm₂.q₀) ws out) := by
  have hstate : (wordsCfg (State := Option (S₁ ⊕ S₂)) input (some none) ws out).state =
      some none := rfl
  rw [step_apply_of_state hstate, inputSymbol_wordsCfg]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [inputBranch, h, rightCfg, Cfg.mapState, wordsCfg, Action.apply, SignType.cast]

/-- The full run when the input's first symbol is `some x`: after the dispatch step the machine
mirrors `tm₁` step for step. -/
private lemma runFrom_start_left (ws : Fin k → List Bool) (out : List Bool) (τ : ℕ)
    (h : input.head? = some x) :
    (inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) (τ + 1) =
      leftCfg (S₂ := S₂) (tm₁.runFrom (wordsCfg input (some tm₁.q₀) ws out) τ) := by
  rw [runFrom_succ_eq_step, step_start_left ws out h, runFrom_leftCfg]

/-- The full run when the input's first symbol is not `some x`. -/
private lemma runFrom_start_right (ws : Fin k → List Bool) (out : List Bool) (τ : ℕ)
    (h : ¬ input.head? = some x) :
    (inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) (τ + 1) =
      rightCfg (S₁ := S₁) (tm₂.runFrom (wordsCfg input (some tm₂.q₀) ws out) τ) := by
  rw [runFrom_succ_eq_step, step_start_right ws out h, runFrom_rightCfg]

/-- Space bound of the left branch: the dispatch step costs at most `k` cells and the mirrored run
of `tm₁` uses exactly `tm₁`'s space. -/
private lemma spaceUsed_start_left (ws : Fin k → List Bool) (out : List Bool) (τ : ℕ)
    (h : input.head? = some x) :
    (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (τ + 1) ≤
      tm₁.spaceUsed (wordsCfg input (some tm₁.q₀) ws out) τ + k := by
  have hstep1 : (inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1 =
      leftCfg (S₂ := S₂) (wordsCfg input (some tm₁.q₀) ws out) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, runFrom_succ_eq_step', runFrom_zero,
      step_start_left ws out h]
  have hsp1 : (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 ≤ k := by
    refine spaceUsed_le_of_workTapePos_const (wordsCfg input (some none) ws out) 1 fun m _ => ?_
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rw [runFrom_zero]
    · rw [hstep1]; rfl
  have hsp2 : (inputBranch x tm₁ tm₂).spaceUsed
      ((inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ ≤
      tm₁.spaceUsed (wordsCfg input (some tm₁.q₀) ws out) τ := by
    rw [hstep1]
    refine le_of_eq (spaceUsed_eq_of_workTapePos (tm := inputBranch x tm₁ tm₂) (tm' := tm₁)
      (leftCfg (wordsCfg input (some tm₁.q₀) ws out)) (wordsCfg input (some tm₁.q₀) ws out)
      τ fun m _ => ?_)
    rw [runFrom_leftCfg, workTapePos_leftCfg]
  calc (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (τ + 1)
      = (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (1 + τ) := by
        rw [Nat.add_comm]
    _ ≤ (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 +
        (inputBranch x tm₁ tm₂).spaceUsed
          ((inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ :=
          spaceUsed_add_le (wordsCfg input (some none) ws out) 1 τ
    _ ≤ k + tm₁.spaceUsed (wordsCfg input (some tm₁.q₀) ws out) τ := Nat.add_le_add hsp1 hsp2
    _ = tm₁.spaceUsed (wordsCfg input (some tm₁.q₀) ws out) τ + k := Nat.add_comm _ _

/-- Space bound of the right branch. -/
private lemma spaceUsed_start_right (ws : Fin k → List Bool) (out : List Bool) (τ : ℕ)
    (h : ¬ input.head? = some x) :
    (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (τ + 1) ≤
      tm₂.spaceUsed (wordsCfg input (some tm₂.q₀) ws out) τ + k := by
  have hstep1 : (inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1 =
      rightCfg (S₁ := S₁) (wordsCfg input (some tm₂.q₀) ws out) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, runFrom_succ_eq_step', runFrom_zero,
      step_start_right ws out h]
  have hsp1 : (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 ≤ k := by
    refine spaceUsed_le_of_workTapePos_const (wordsCfg input (some none) ws out) 1 fun m _ => ?_
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rw [runFrom_zero]
    · rw [hstep1]; rfl
  have hsp2 : (inputBranch x tm₁ tm₂).spaceUsed
      ((inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ ≤
      tm₂.spaceUsed (wordsCfg input (some tm₂.q₀) ws out) τ := by
    rw [hstep1]
    refine le_of_eq (spaceUsed_eq_of_workTapePos (tm := inputBranch x tm₁ tm₂) (tm' := tm₂)
      (rightCfg (wordsCfg input (some tm₂.q₀) ws out)) (wordsCfg input (some tm₂.q₀) ws out)
      τ fun m _ => ?_)
    rw [runFrom_rightCfg, workTapePos_rightCfg]
  calc (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (τ + 1)
      = (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) (1 + τ) := by
        rw [Nat.add_comm]
    _ ≤ (inputBranch x tm₁ tm₂).spaceUsed (wordsCfg input (some none) ws out) 1 +
        (inputBranch x tm₁ tm₂).spaceUsed
          ((inputBranch x tm₁ tm₂).runFrom (wordsCfg input (some none) ws out) 1) τ :=
          spaceUsed_add_le (wordsCfg input (some none) ws out) 1 τ
    _ ≤ k + tm₂.spaceUsed (wordsCfg input (some tm₂.q₀) ws out) τ := Nat.add_le_add hsp1 hsp2
    _ = tm₂.spaceUsed (wordsCfg input (some tm₂.q₀) ws out) τ + k := Nat.add_comm _ _

end InputBranch

open InputBranch in
/-- **Streaming dispatch on the input.** A single machine that reads the input's first symbol and
then runs one of two given machines to completion — output included. The arms read the whole input
in place (the dispatch moves no head) and may emit: the combined machine's output, halting and
space are exactly the chosen arm's, plus one dispatch step (costing at most `k`).

Started at a word configuration in the dispatch state, in `τ + 1` steps the machine reads the
input's first symbol and, if it is `some x`, runs `tm₁` for `τ` steps, otherwise `tm₂`. This is
what lets a case analysis send a branch's result straight to the real output tape instead of
parking it. -/
public theorem exists_inputBranch_run {k : ℕ} (x : Bool) {S₁ S₂ : Type}
    [Finite S₁] [Finite S₂]
    (tm₁ : MultiTapeTM k Bool S₁) (tm₂ : MultiTapeTM k Bool S₂) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ (input : List Bool) (ws : Fin k → List Bool) (out : List Bool) (τ : ℕ),
        (input.head? = some x →
          (tm.runFrom (wordsCfg input (some tm.q₀) ws out) (τ + 1)).output =
              (tm₁.runFrom (wordsCfg input (some tm₁.q₀) ws out) τ).output ∧
          ((tm.runFrom (wordsCfg input (some tm.q₀) ws out) (τ + 1)).state = none ↔
              (tm₁.runFrom (wordsCfg input (some tm₁.q₀) ws out) τ).state = none) ∧
          tm.spaceUsed (wordsCfg input (some tm.q₀) ws out) (τ + 1) ≤
              tm₁.spaceUsed (wordsCfg input (some tm₁.q₀) ws out) τ + k) ∧
        (input.head? ≠ some x →
          (tm.runFrom (wordsCfg input (some tm.q₀) ws out) (τ + 1)).output =
              (tm₂.runFrom (wordsCfg input (some tm₂.q₀) ws out) τ).output ∧
          ((tm.runFrom (wordsCfg input (some tm.q₀) ws out) (τ + 1)).state = none ↔
              (tm₂.runFrom (wordsCfg input (some tm₂.q₀) ws out) τ).state = none) ∧
          tm.spaceUsed (wordsCfg input (some tm.q₀) ws out) (τ + 1) ≤
              tm₂.spaceUsed (wordsCfg input (some tm₂.q₀) ws out) τ + k) := by
  refine ⟨Option (S₁ ⊕ S₂), inferInstance, inputBranch x tm₁ tm₂,
    fun input ws out τ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [show (inputBranch x tm₁ tm₂).q₀ = none from rfl, runFrom_start_left ws out τ h]
    exact ⟨rfl, by simp [leftCfg, Option.map_eq_none_iff], spaceUsed_start_left ws out τ h⟩
  · rw [show (inputBranch x tm₁ tm₂).q₀ = none from rfl, runFrom_start_right ws out τ h]
    exact ⟨rfl, by simp [rightCfg, Option.map_eq_none_iff], spaceUsed_start_right ws out τ h⟩

end Turing.MultiTapeTM
