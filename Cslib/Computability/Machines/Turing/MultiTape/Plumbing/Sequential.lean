/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Sequential composition of machines on shared tapes

`seq tm₀ tm₁` behaves like `tm₀` until `tm₀` would halt, at which point it continues as `tm₁`,
started in its initial state on the tapes as `tm₀` left them. The design is due to Samuel
Schlesinger (leanprover/cslib#872): the state space is `State₀ ⊕ State₁`, and the *halting
transition* of the first phase is mapped to the initial state of the second, so the handoff costs
no extra step.

At the specification level this is `transformsTapes_seq`: transformations compose, with the time
and space bounds adding. The postcondition of `TransformsTapes` is what makes the proof direct —
the first machine halts in a full `wordsCfg`, which is exactly a starting configuration for the
second.

## Main results

* `Turing.MultiTapeTM.seq`: the composed machine.
* `Turing.MultiTapeTM.transformsTapes_seq`: transformations compose, bounds adding.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
@[expose] public def seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) where
  q₀ := .inl tm₀.q₀
  tr q inp work :=
    match q with
    | .inl q₀ =>
      let a := tm₀.tr q₀ inp work
      { a with state := some (a.state.elim (.inr tm₁.q₀) .inl) }
    | .inr q₁ =>
      let a := tm₁.tr q₁ inp work
      { a with state := a.state.map .inr }

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

namespace Sequential

/-- A configuration of the first phase: a configuration of `tm₀`, with a halted state mapped to
the initial state of the second phase. Under this map, the whole first phase of `seq` mirrors the
run of `tm₀`, *including* its halting step. -/
@[expose] public def leftCfg (tm₁ : MultiTapeTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  ⟨some (cfg.state.elim (.inr tm₁.q₀) .inl), cfg.inputPos, cfg.workTapes, cfg.workTapePos,
    cfg.output⟩

/-- A configuration of the second phase. Under this map, the second phase of `seq` mirrors the
run of `tm₁`. -/
@[expose] public def rightCfg (cfg : Cfg k Symbol State₁ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  ⟨cfg.state.map .inr, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

public lemma step_leftCfg (cfg : Cfg k Symbol State₀ input) (h : cfg.state ≠ none) :
    (tm₀.seq tm₁).step (leftCfg tm₁ cfg) = leftCfg tm₁ (tm₀.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have h1 : (leftCfg tm₁ cfg).state = some (Sum.inl q : State₀ ⊕ State₁) := by
    simp [leftCfg, hq]
  simp only [step, h1, hq]
  rfl

public lemma step_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (tm₀.seq tm₁).step (rightCfg cfg) = rightCfg (tm₁.step cfg) := by
  cases hq : cfg.state with
  | none =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = none := by simp [rightCfg, hq]
    simp only [step, h1, hq]
  | some q =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = some (Sum.inr q : State₀ ⊕ State₁) := by
      simp [rightCfg, hq]
    simp only [step, h1, hq]
    rfl

/-- The second phase of `seq` mirrors the run of `tm₁`. -/
public lemma runFrom_rightCfg (cfg : Cfg k Symbol State₁ input) (n : ℕ) :
    (tm₀.seq tm₁).runFrom (rightCfg cfg) n = rightCfg (tm₁.runFrom cfg n) :=
  runFrom_comm_of_step rightCfg (fun c => step_rightCfg c) cfg n

/-- While `tm₀` is running, `seq` mirrors it. -/
public lemma runFrom_leftCfg (cfg : Cfg k Symbol State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm₀.runFrom cfg m).state ≠ none) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) n = leftCfg tm₁ (tm₀.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step', ih fun m hm => h m (by omega),
      step_leftCfg _ (h n (by omega))]

@[simp]
public lemma leftCfg_wordsCfg (q : State₀) (ws : Fin k → List Symbol) (out : List Symbol) :
    leftCfg tm₁ (wordsCfg input (some q) ws out) =
      wordsCfg input (some (Sum.inl q : State₀ ⊕ State₁)) ws out := rfl

@[simp]
public lemma rightCfg_wordsCfg (q : Option State₁) (ws : Fin k → List Symbol) (out : List Symbol) :
    rightCfg (State₀ := State₀) (wordsCfg input q ws out) =
      wordsCfg input (q.map Sum.inr) ws out := rfl

@[simp]
public lemma workTapePos_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
public lemma workTapePos_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).workTapePos = cfg.workTapePos := rfl

end Sequential

open Sequential in
/-- **Sequential composition of transformations.** If the postcondition of the first
transformation implies the precondition of the second, the composed machine performs the two
transformations one after the other, with the time and space bounds adding. -/
public theorem transformsTapes_seq
    {P₀ P₁ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P₀ Q₀ t₀ s₀) (h₁ : TransformsTapes tm₁ P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws', P₀ input ws → Q₀ input ws ws' → P₁ input ws') :
    TransformsTapes (tm₀.seq tm₁) P₀
      (fun input ws ws'' => ∃ ws', Q₀ input ws ws' ∧ Q₁ input ws' ws'')
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨τ₀, hτ₀, ws', hrun₀, hQ₀, hspace₀⟩ := h₀ input ws out hP₀
  obtain ⟨τ₁, hτ₁, ws'', hrun₁, hQ₁, hspace₁⟩ := h₁ input ws' out (hmid input ws ws' hP₀ hQ₀)
  -- the first halting time of the first machine
  obtain ⟨u, hu, huhalt, huactive⟩ := exists_minimal_halting_time tm₀
    (wordsCfg input (some tm₀.q₀) ws out) τ₀ (by simp [hrun₀])
  have hu_run : tm₀.runFrom (wordsCfg input (some tm₀.q₀) ws out) u =
      wordsCfg input none ws' out := by
    rw [← runFrom_eq_of_halt tm₀ _ hu huhalt, hrun₀]
  -- the first phase mirrors the first machine, ending in the handoff configuration
  have hleft : ∀ m ≤ u, (tm₀.seq tm₁).runFrom (wordsCfg input (some (tm₀.seq tm₁).q₀) ws out) m
      = leftCfg tm₁ (tm₀.runFrom (wordsCfg input (some tm₀.q₀) ws out) m) := by
    intro m hm
    have : wordsCfg (State := State₀ ⊕ State₁) input (some (tm₀.seq tm₁).q₀) ws out =
        leftCfg tm₁ (wordsCfg input (some tm₀.q₀) ws out) := rfl
    rw [this, runFrom_leftCfg _ m fun r hr =>
      huactive r (by omega)]
  -- the handoff configuration is the second machine's start, seen through the right embedding
  have hhandoff : leftCfg tm₁ (tm₀.runFrom (wordsCfg input (some tm₀.q₀) ws out) u) =
      rightCfg (wordsCfg input (some tm₁.q₀) ws' out) := by
    rw [hu_run]
    rfl
  refine ⟨u + τ₁, by omega, ws'', ?_, ⟨ws', hQ₀, hQ₁⟩, ?_⟩
  · rw [runFrom_add, hleft u le_rfl, hhandoff, runFrom_rightCfg, hrun₁]
    rfl
  · refine le_trans (spaceUsed_add_le _ _ _) (Nat.add_le_add ?_ ?_)
    · -- the first phase visits what the first machine visits
      refine le_trans (le_of_eq (spaceUsed_eq_of_workTapePos _ _ u fun m hm => ?_))
        (le_trans (spaceUsed_mono tm₀ _ hu) hspace₀)
      rw [hleft m hm, workTapePos_leftCfg]
    · -- the second phase visits what the second machine visits
      rw [hleft u le_rfl, hhandoff]
      refine le_trans (le_of_eq (spaceUsed_eq_of_workTapePos _ _ τ₁ fun m hm => ?_)) hspace₁
      rw [runFrom_rightCfg, workTapePos_rightCfg]

section RawSeq

variable {K : ℕ} {Sym S₁ S₂ : Type*} {inp : List Sym}

open Sequential in
public lemma seq_spec {tm₁ : MultiTapeTM K Sym S₁} {tm₂ : MultiTapeTM K Sym S₂}
    {c : Cfg K Sym (S₁ ⊕ S₂) inp} {c₁ : Cfg K Sym S₁ inp} {c₂ : Cfg K Sym S₂ inp}
    {u₁ u₂ s₁' s₂' : ℕ}
    (hc : c.state = some (tm₁.seq tm₂).q₀)
    (h₁ : tm₁.runFrom (c.withState (some tm₁.q₀)) u₁ = c₁)
    (h₁halt : c₁.state = none)
    (h₁act : ∀ m < u₁, (tm₁.runFrom (c.withState (some tm₁.q₀)) m).state ≠ none)
    (h₁sp : tm₁.spaceUsed (c.withState (some tm₁.q₀)) u₁ ≤ s₁')
    (h₂ : tm₂.runFrom (c₁.withState (some tm₂.q₀)) u₂ = c₂)
    (h₂halt : c₂.state = none)
    (h₂act : ∀ m < u₂, (tm₂.runFrom (c₁.withState (some tm₂.q₀)) m).state ≠ none)
    (h₂sp : tm₂.spaceUsed (c₁.withState (some tm₂.q₀)) u₂ ≤ s₂') :
    (tm₁.seq tm₂).runFrom c (u₁ + u₂) = c₂.withState (none : Option (S₁ ⊕ S₂)) ∧
    (∀ m < u₁ + u₂, ((tm₁.seq tm₂).runFrom c m).state ≠ none) ∧
    (tm₁.seq tm₂).spaceUsed c (u₁ + u₂) ≤ s₁' + s₂' := by
  set cs := c.withState (some tm₁.q₀) with hcs
  have hcleft : c = leftCfg tm₂ cs := by
    refine Cfg.ext ?_ rfl rfl rfl rfl
    rw [hc]
    rfl
  have hhalt₁ : (tm₁.runFrom cs u₁).state = none := by rw [h₁]; exact h₁halt
  have hleft : ∀ m ≤ u₁, (tm₁.seq tm₂).runFrom c m = leftCfg tm₂ (tm₁.runFrom cs m) := by
    intro m hm
    rw [hcleft, runFrom_leftCfg _ m fun r hr => h₁act r (by omega)]
  have hmid : (tm₁.seq tm₂).runFrom c u₁ = rightCfg (c₁.withState (some tm₂.q₀)) := by
    rw [hleft u₁ le_rfl, h₁]
    refine Cfg.ext ?_ rfl rfl rfl rfl
    simp [leftCfg, rightCfg, Cfg.withState, h₁halt]
  have hright : ∀ m, (tm₁.seq tm₂).runFrom c (u₁ + m) =
      rightCfg (tm₂.runFrom (c₁.withState (some tm₂.q₀)) m) := by
    intro m
    rw [runFrom_add, hmid, runFrom_rightCfg]
  refine ⟨?_, ?_, ?_⟩
  · rw [hright u₂, h₂]
    refine Cfg.ext ?_ rfl rfl rfl rfl
    simp [rightCfg, Cfg.withState, h₂halt]
  · intro m hm
    rcases Nat.le_total m u₁ with h | h
    · rw [hleft m h]
      simp [leftCfg]
    · obtain ⟨m', rfl⟩ : ∃ m', m = u₁ + m' := ⟨m - u₁, by omega⟩
      rw [hright m']
      have h := h₂act m' (by omega)
      simpa only [rightCfg, ne_eq, Option.map_eq_none_iff] using h
  · refine le_trans (spaceUsed_add_le _ _ _) (Nat.add_le_add ?_ ?_)
    · refine le_trans (le_of_eq (spaceUsed_eq_of_workTapePos _ _ u₁ fun m hm => ?_)) h₁sp
      rw [hleft m hm]
      rfl
    · rw [hmid]
      refine le_trans (le_of_eq (spaceUsed_eq_of_workTapePos _ _ u₂ fun m hm => ?_)) h₂sp
      rw [runFrom_rightCfg]
      rfl

end RawSeq

end Turing.MultiTapeTM
