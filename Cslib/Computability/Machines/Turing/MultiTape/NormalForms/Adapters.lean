/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Tidy
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindTape

/-!
# From a computable function to a tape transformer

A computable function enters the word-transformer interface
(`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes`) by three steps: make it
*tidy* (`Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Tidy`), so it halts with its
result on the append-only output tape and everything else blank; *redirect that output to a work
tape* (`outputToTape`), which leaves the result on a fresh last tape with the head at the write
frontier; and *rewind that head* (`rewindTape`) so the tape holds a word in the normal form the
interface expects.

`exists_transformsTapes_ofComputableInput` is the resulting adapter for a function read from the
real input tape. The output tape is the last of `k₀ + 1` work tapes, where `k₀` is the tidy
machine's tape count.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- **A computable function, read from the input tape, as a tape transformer.** Started with the
input on the real input tape and every work tape blank, the machine halts having written the
encoded result to the last work tape, in linear time and in space linear in the result length. -/
public theorem exists_transformsTapes_ofComputableInput
    {enc : α ↪ List Bool} {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace g enc encOut t s) :
    ∃ (c K : ℕ) (o : Fin K) (State : Type) (_ : Finite State) (tm : MultiTapeTM K Bool State),
      ∀ a, TransformsTapes tm
        (fun input ws => input = enc a ∧ ∀ l, ws l = [])
        (fun _ ws ws' => ws' = Function.update ws o (encOut (g a)))
        (c * (t a + 1)) (c * (s a + (encOut (g a)).length + 1) + K) := by
  classical
  obtain ⟨c₀, k₀, State₀, hfin, tm₀, htidy⟩ := exists_tidy h
  obtain ⟨SR, hSR, tmR, hR⟩ := exists_rewindTape (Symbol := Bool) (Fin.last k₀)
  have := hfin
  have := hSR
  -- the composed machine: run the tidy machine with its output on a fresh tape, then rewind it
  refine ⟨c₀ + k₀ + 4, k₀ + 1, Fin.last k₀, State₀ ⊕ SR, inferInstance,
    tm₀.outputToTape.seq tmR, fun a => ?_⟩
  intro input ws out hP
  obtain ⟨hinput, hblank⟩ := hP
  subst hinput
  have hws : ws = fun _ => [] := funext hblank
  subst hws
  obtain ⟨τ, hτ, htidyrun, htidysp⟩ := htidy a
  -- The encoded result is produced by the *original* machine in at most `t a` steps, so it is no
  -- longer than `t a` — a fact the tidy interface alone (which only bounds by `τ`) does not give.
  have hw_len : (encOut (g a)).length ≤ t a := by
    obtain ⟨kk, SS, hfinSS, tmm, hcomp⟩ := h
    obtain ⟨t', ht', s', hs', hhaltm, houtm, hspm⟩ := hcomp a
    have hlen : ∀ d, (tmm.runFrom (tmm.initCfg (enc a)) d).output.length ≤ d := by
      intro d
      induction d with
      | zero => rw [runFrom_zero, initCfg_eq_wordsCfg]; simp
      | succ d ih =>
        rw [runFrom_succ_eq_step', step_output, List.length_append]
        have h1 : (tmm.outputSymbol (tmm.runFrom (tmm.initCfg (enc a)) d)).toList.length ≤ 1 := by
          cases tmm.outputSymbol (tmm.runFrom (tmm.initCfg (enc a)) d) <;> simp
        omega
    have hle := hlen t'
    rw [houtm] at hle
    omega
  -- Abbreviations: the encoded result `w`, the tidy halting configuration `X`, and the start.
  set w := encOut (g a) with hw_def
  set X := wordsCfg (enc a) none (fun _ => []) w with hX_def
  set cStart := wordsCfg (enc a) (some (tm₀.outputToTape.seq tmR).q₀) (fun _ => []) out
    with hcStart_def
  -- ===================================================================================
  -- Phase 1: run the tidy machine with its output redirected onto the fresh last work tape.
  -- ===================================================================================
  -- The phase-1 start configuration, expressed through the output-redirection maps.
  have hstart1 : cStart.withState (some tm₀.outputToTape.q₀)
      = (outCfg (tm₀.initCfg (enc a))).withOutput out := by
    rw [hcStart_def, ← initCfg_outputToTape, initCfg_eq_wordsCfg]; rfl
  -- Running the redirected machine mirrors the tidy run, ending on `(outCfg X).withOutput out`.
  have hc1_run : tm₀.outputToTape.runFrom (cStart.withState (some tm₀.outputToTape.q₀)) τ
      = (outCfg X).withOutput out := by
    rw [hstart1, runFrom_outputToTape_withOutput, runFrom_outCfg, htidyrun]
  set c₁ := (outCfg X).withOutput out with hc1_def
  have hc1_state : c₁.state = none := by rw [hc1_def, hX_def]; rfl
  -- Replace `τ` by the first halting time `τ'`, which gives phase-1 activity for free.
  obtain ⟨τ', hτ'le, hτ'halt, hτ'act⟩ :=
    exists_minimal_halting_time tm₀.outputToTape (cStart.withState (some tm₀.outputToTape.q₀)) τ
      (by rw [hc1_run]; exact hc1_state)
  have hc1_run' : tm₀.outputToTape.runFrom (cStart.withState (some tm₀.outputToTape.q₀)) τ' = c₁ :=
    (runFrom_eq_of_halt tm₀.outputToTape _ hτ'le hτ'halt).symm.trans hc1_run
  -- The phase-1 space bound: the tidy space, plus one frontier walk over the written output.
  have h₁sp : tm₀.outputToTape.spaceUsed (cStart.withState (some tm₀.outputToTape.q₀)) τ'
      ≤ c₀ * (s a + 1) + k₀ + (w.length + 1) := by
    rw [hstart1, spaceUsed_outputToTape_withOutput]
    refine le_trans (spaceUsed_outputToTape tm₀ (tm₀.initCfg (enc a)) τ') ?_
    have hsp' : tm₀.spaceUsed (tm₀.initCfg (enc a)) τ' ≤ c₀ * (s a + 1) + k₀ :=
      le_trans (spaceUsed_mono tm₀ (tm₀.initCfg (enc a)) hτ'le) htidysp
    have houtlen : (tm₀.runFrom (tm₀.initCfg (enc a)) τ').output.length ≤ w.length := by
      have hτeq : τ' + (τ - τ') = τ := by omega
      have hmono := length_output_mono tm₀ (tm₀.runFrom (tm₀.initCfg (enc a)) τ') (τ - τ')
      rw [← runFrom_add, hτeq, htidyrun, hX_def] at hmono
      simpa using hmono
    omega
  -- ===================================================================================
  -- Phase 2: rewind the last tape's head from the frontier back to the start of the word.
  -- ===================================================================================
  have hcs1_state : (c₁.withState (some tmR.q₀)).state = some tmR.q₀ := rfl
  have hcs1_tape : (c₁.withState (some tmR.q₀)).workTapes (Fin.last k₀) = tapeOfList w := by
    change (outCfg X).workTapes (Fin.last k₀) = tapeOfList w
    simp only [outCfg_workTapes_last, hX_def, wordsCfg_output]
  have hcs1_pos : (c₁.withState (some tmR.q₀)).workTapePos (Fin.last k₀) = (w.length : ℤ) := by
    change (outCfg X).workTapePos (Fin.last k₀) = (w.length : ℤ)
    simp only [outCfg_workTapePos_last, hX_def, wordsCfg_output]
  obtain ⟨u₂, hu₂, h₂act, h₂halteq, hframe⟩ :=
    hR (enc a) (c₁.withState (some tmR.q₀)) w hcs1_state hcs1_tape hcs1_pos
  -- The phase-2 space bound: the moving head stays in `[-1, w.length]`, every other head is fixed.
  have h₂sp : tmR.spaceUsed (c₁.withState (some tmR.q₀)) u₂ ≤ (w.length + 2) + (k₀ + 1) := by
    refine le_trans (spaceUsed_le_of_one_moving (c₁.withState (some tmR.q₀)) u₂ (Fin.last k₀)
      (-1) (w.length : ℤ) ?_ ?_) ?_
    · exact fun m hm => ⟨(hframe m hm).2.2.2.2.1, (hframe m hm).2.2.2.2.2⟩
    · exact fun m hm j hj => ((hframe m hm).2.2.1 j hj).2
    · have htoNat : ((w.length : ℤ) + 1 - (-1)).toNat = w.length + 2 := by omega
      omega
  -- ===================================================================================
  -- Assemble the two phases and read off the halting configuration and the two bounds.
  -- ===================================================================================
  obtain ⟨hseq_run, hseq_act, hseq_sp⟩ :=
    seq_spec (tm₁ := tm₀.outputToTape) (tm₂ := tmR) (c := cStart)
      (by rw [hcStart_def]; rfl) hc1_run' hc1_state hτ'act h₁sp h₂halteq rfl h₂act h₂sp
  refine ⟨τ' + u₂, ?_, Function.update (fun _ => []) (Fin.last k₀) w, ?_, rfl, ?_⟩
  · -- Time: `τ' + u₂ ≤ τ + (w.length + 3)`, with `τ ≤ c₀·(t a+1)` and `w.length ≤ t a`.
    have hτlin : τ ≤ c₀ * (t a + 1) := hτ
    have hprod : (c₀ + k₀ + 4) * (t a + 1) = c₀ * (t a + 1) + (k₀ + 4) * (t a + 1) := by
      rw [show c₀ + k₀ + 4 = c₀ + (k₀ + 4) from by omega, Nat.add_mul]
    have h4 : 4 * (t a + 1) ≤ (k₀ + 4) * (t a + 1) := Nat.mul_le_mul (by omega) (le_refl _)
    omega
  · -- The composed run halts in the normal-form configuration `wordsCfg`.
    rw [hseq_run]
    refine Cfg.ext rfl ?_ ?_ ?_ ?_
    · simp [Cfg.withState_inputPos, hc1_def, Cfg.withOutput_inputPos, hX_def, outCfg]
    · funext l
      induction l using Fin.lastCases with
      | last => funext z; simp [hc1_def, hX_def]
      | cast j => funext z; simp [hc1_def, hX_def]
    · funext l
      induction l using Fin.lastCases with
      | last => simp [hc1_def, hX_def]
      | cast j => simp [hc1_def, hX_def]
    · simp [Cfg.withState_output, hc1_def, Cfg.withOutput_output]
  · -- Space: `s₁' + s₂'` fits the budget `(c₀+k₀+4)·(s a + w.length + 1) + (k₀+1)`.
    refine le_trans hseq_sp ?_
    have e1 : c₀ * (s a + 1) ≤ c₀ * (s a + w.length + 1) := Nat.mul_le_mul (le_refl _) (by omega)
    have e2 : (k₀ + 4) * (w.length + 1) ≤ (k₀ + 4) * (s a + w.length + 1) :=
      Nat.mul_le_mul (le_refl _) (by omega)
    have e3 : (c₀ + k₀ + 4) * (s a + w.length + 1)
        = c₀ * (s a + w.length + 1) + (k₀ + 4) * (s a + w.length + 1) := by
      rw [show c₀ + k₀ + 4 = c₀ + (k₀ + 4) from by omega, Nat.add_mul]
    have e4 : (k₀ + 4) * (w.length + 1) = (k₀ + 4) * w.length + (k₀ + 4) := by
      rw [Nat.mul_add, Nat.mul_one]
    have e5 : 4 * w.length ≤ (k₀ + 4) * w.length := Nat.mul_le_mul (by omega) (le_refl _)
    omega

end Turing.MultiTapeTM
