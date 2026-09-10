/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Tidy
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.EmitTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

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
public theorem exists_transformsTapes_ofComputableInput_fixed
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

/-- **A computable function, read from a work tape, as a tape transformer.** The virtual input
tape is the work tape `Fin.last (k₀ + 1)` (one past the tidy machine's tapes and its output tape);
the result is written to the tidy machine's output tape `⟨k₀, _⟩`. Started with the input on the
virtual tape and every other work tape blank, the machine halts having written the encoded result
to the output tape, in linear time and space linear in the input and result lengths.

Built from `exists_transformsTapes_ofComputableInput`'s machine `M₀` (which reads the *real* input
and leaves the result on a work tape): `inputFromTape M₀` redirects `M₀`'s input reading to the
virtual tape, bracketed by two one-cell writes that place and remove the boundary flag `M₀`'s
input redirection needs. -/
public theorem exists_transformsTapes_ofComputable_fixed
    {enc : α ↪ List Bool} {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace g enc encOut t s) :
    ∃ (c K : ℕ) (i o : Fin K) (State : Type) (_ : Finite State) (tm : MultiTapeTM K Bool State),
      i ≠ o ∧ ∀ a, TransformsTapes tm
        (fun _ ws => ws i = enc a ∧ ∀ l, l ≠ i → ws l = [])
        (fun _ ws ws' => ws' = Function.update ws o (encOut (g a)))
        (c * (t a + 1)) (c * (s a + (enc a).length + (encOut (g a)).length + 1) + K) := by
  classical
  -- The base machine `M₀` reads the *real* input tape and leaves `encOut (g a)` on work tape `o₀`.
  obtain ⟨c_f, K₀, o₀, State₀, hfin₀, M₀, hM₀⟩ := exists_transformsTapes_ofComputableInput_fixed h
  -- Two one-cell writers on the flag tape `⟨K₀ + 1, _⟩`: one places the boundary mark, one clears
  -- it. They bracket the redirected run of `M₀` and supply what its input redirection needs.
  obtain ⟨SM, hSMfin, setMark, hMark⟩ :=
    exists_setCell (Symbol := Bool) (⟨K₀ + 1, by omega⟩ : Fin (K₀ + 2)) (some true)
  obtain ⟨SC, hSCfin, setClear, hClear⟩ :=
    exists_setCell (Symbol := Bool) (⟨K₀ + 1, by omega⟩ : Fin (K₀ + 2)) none
  have := hfin₀
  have := hSMfin
  have := hSCfin
  refine ⟨c_f + 2 * K₀ + 12, K₀ + 2, ⟨K₀, by omega⟩, o₀.castAdd 2, SM ⊕ State₀ ⊕ SC, inferInstance,
    setMark.seq ((inputFromTape M₀).seq setClear), ?_, fun a => ?_⟩
  · -- The virtual input tape `⟨K₀, _⟩` and the output tape `o₀.castAdd 2` are distinct.
    exact Fin.ne_of_val_ne (by have := o₀.isLt; simp; omega)
  intro input ws out hP
  obtain ⟨hi, hblank⟩ := hP
  -- Split any tape index into an inner tape, the virtual input tape, or the flag tape.
  have tcase : ∀ l : Fin (K₀ + 2),
      (∃ j : Fin K₀, l = j.castAdd 2) ∨ l = ⟨K₀, by omega⟩ ∨ l = ⟨K₀ + 1, by omega⟩ := by
    intro l
    rcases Nat.lt_trichotomy l.val K₀ with hlt | heq | hgt
    · exact Or.inl ⟨⟨l.val, hlt⟩, Fin.ext (by simp)⟩
    · exact Or.inr (Or.inl (Fin.ext (by simpa using heq)))
    · have hb := l.isLt
      exact Or.inr (Or.inr (Fin.ext (by simp; omega)))
  -- Run the base machine on the real input `enc a`, reading off the encoded result and its bounds.
  obtain ⟨τ, hτ, ws₀', hM₀run, hws₀', hM₀sp⟩ := hM₀ a (enc a) (fun _ => []) out ⟨rfl, fun _ => rfl⟩
  set w := encOut (g a) with hw_def
  set start := wordsCfg input (some (setMark.seq ((inputFromTape M₀).seq setClear)).q₀) ws out
    with hstart
  -- ===================================================================================
  -- Phase 1: place the boundary mark on the flag tape's cell `-1`.
  -- ===================================================================================
  obtain ⟨u₁, hu₁, h1act, h1eq, h1frame⟩ :=
    hMark input (start.withState (some setMark.q₀)) rfl (by simp [hstart])
  set C1 := setMark.runFrom (start.withState (some setMark.q₀)) u₁ with hC1
  -- The halting configuration of phase 1, restarted for `M₀`, is exactly `M₀`'s start as the
  -- input-redirected machine sees it: the input `enc a` on the virtual tape, the flag marked.
  have hAstart : C1.withState (some M₀.q₀)
      = inCfg true (wordsCfg (enc a) (some M₀.q₀) (fun _ => []) out) input := by
    rw [h1eq, hstart]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l
      rcases tcase l with ⟨j, rfl⟩ | rfl | rfl
      · have hjf : (j.castAdd 2 : Fin (K₀ + 2)) ≠ ⟨K₀ + 1, by omega⟩ :=
          Fin.ne_of_val_ne (by have := j.isLt; simp; omega)
        have hji : (j.castAdd 2 : Fin (K₀ + 2)) ≠ ⟨K₀, by omega⟩ :=
          Fin.ne_of_val_ne (by have := j.isLt; simp; omega)
        funext z
        simp [Cfg.withState_workTapes, inCfg_workTapes_castAdd, wordsCfg_workTapes,
          Function.update_of_ne hjf, hblank _ hji]
      · funext z
        simp [Cfg.withState_workTapes, inCfg_workTapes_vip, wordsCfg_workTapes, hi]
      · have hfi : (⟨K₀ + 1, by omega⟩ : Fin (K₀ + 2)) ≠ ⟨K₀, by omega⟩ :=
          Fin.ne_of_val_ne (by simp)
        funext z
        rcases eq_or_ne z (-1 : ℤ) with hz | hz
        · subst hz
          simp [Cfg.withState_workTapes, inCfg_workTapes_flag, Function.update_self]
        · simp [Cfg.withState_workTapes, inCfg_workTapes_flag, wordsCfg_workTapes,
            Function.update_self, Function.update_of_ne hz, hblank _ hfi, tapeOfList_nil]
    · funext l
      rcases tcase l with ⟨j, rfl⟩ | rfl | rfl
      · simp [Cfg.withState_workTapePos, inCfg_workTapePos_castAdd, wordsCfg_workTapePos]
      · simp [Cfg.withState_workTapePos, inCfg_workTapePos_vip, wordsCfg_workTapePos,
          wordsCfg_inputPos]
      · simp [Cfg.withState_workTapePos, inCfg_workTapePos_flag, wordsCfg_workTapePos,
          wordsCfg_inputPos]
  -- Phase-1 space: one head walks `[-1, 0]`, every other head is fixed.
  have h1sp : setMark.spaceUsed (start.withState (some setMark.q₀)) u₁ ≤ K₀ + 4 := by
    refine le_trans (spaceUsed_le_of_one_moving _ u₁ (⟨K₀ + 1, by omega⟩) (-1) 0
      (fun m hm => ⟨(h1frame m hm).2.2.2.1, (h1frame m hm).2.2.2.2⟩)
      (fun m hm j hj => ((h1frame m hm).2.2.1 j hj).2)) ?_
    have : ((0 : ℤ) + 1 - (-1)).toNat = 2 := by omega
    omega
  -- ===================================================================================
  -- Phase 2: run `M₀`, redirected to read `enc a` from the virtual tape.
  -- ===================================================================================
  -- The redirected run mirrors `M₀`'s run, which `hM₀` says lands in `wordsCfg (enc a) none ws₀'`.
  have hA_run_tau : (inputFromTape M₀).runFrom (C1.withState (some M₀.q₀)) τ
      = inCfg true (wordsCfg (enc a) (none : Option State₀) ws₀' out) input := by
    rw [hAstart, runFrom_inCfg, hM₀run]
  -- Replace `τ` by the first halting time `τ'`, which gives the phase-2 activity for free.
  obtain ⟨τ', hτ'le, hτ'halt, hτ'act⟩ :=
    exists_minimal_halting_time (inputFromTape M₀) (C1.withState (some M₀.q₀)) τ
      (by rw [hA_run_tau]; rfl)
  have h_A : (inputFromTape M₀).runFrom (C1.withState (some M₀.q₀)) τ'
      = inCfg true (wordsCfg (enc a) (none : Option State₀) ws₀' out) input :=
    (runFrom_eq_of_halt (inputFromTape M₀) _ hτ'le hτ'halt).symm.trans hA_run_tau
  -- Phase-2 space: the base machine's space, plus one frontier walk over the virtual input.
  have hA_sp : (inputFromTape M₀).spaceUsed (C1.withState (some M₀.q₀)) τ'
      ≤ c_f * (s a + w.length + 1) + K₀ + 2 * ((enc a).length + 2) := by
    rw [hAstart]
    refine le_trans (spaceUsed_inputFromTape M₀ true
      (wordsCfg (enc a) (some M₀.q₀) (fun _ => []) out) input τ') ?_
    have hmono : M₀.spaceUsed (wordsCfg (enc a) (some M₀.q₀) (fun _ => []) out) τ'
        ≤ M₀.spaceUsed (wordsCfg (enc a) (some M₀.q₀) (fun _ => []) out) τ :=
      spaceUsed_mono M₀ _ hτ'le
    omega
  -- ===================================================================================
  -- Phase 3: clear the boundary mark from the flag tape's cell `-1`.
  -- ===================================================================================
  obtain ⟨uB, huB, hBact, hBeq, hBframe⟩ :=
    hClear input
      ((inCfg true (wordsCfg (enc a) (none : Option State₀) ws₀' out) input).withState
        (some setClear.q₀))
      rfl (by simp [Cfg.withState_workTapePos, inCfg_workTapePos_flag, wordsCfg_inputPos])
  have hB_sp : setClear.spaceUsed
      ((inCfg true (wordsCfg (enc a) (none : Option State₀) ws₀' out) input).withState
        (some setClear.q₀)) uB
      ≤ K₀ + 4 := by
    refine le_trans (spaceUsed_le_of_one_moving _ uB (⟨K₀ + 1, by omega⟩) (-1) 0
      (fun m hm => ⟨(hBframe m hm).2.2.2.1, (hBframe m hm).2.2.2.2⟩)
      (fun m hm j hj => ((hBframe m hm).2.2.1 j hj).2)) ?_
    have : ((0 : ℤ) + 1 - (-1)).toNat = 2 := by omega
    omega
  -- ===================================================================================
  -- Assemble the three phases (a nested sequential composition) and read off the results.
  -- ===================================================================================
  obtain ⟨inner_run, inner_act, inner_sp⟩ :=
    seq_spec (tm₁ := inputFromTape M₀) (tm₂ := setClear)
      (c := C1.withState (some ((inputFromTape M₀).seq setClear).q₀))
      rfl h_A rfl hτ'act hA_sp hBeq rfl hBact hB_sp
  obtain ⟨outer_run, outer_act, outer_sp⟩ :=
    seq_spec (tm₁ := setMark) (tm₂ := (inputFromTape M₀).seq setClear) (c := start)
      (by rw [hstart]; rfl) hC1.symm (by rw [h1eq]) h1act h1sp inner_run rfl inner_act inner_sp
  refine ⟨u₁ + (τ' + uB), ?_, Function.update ws (o₀.castAdd 2) w, ?_, rfl, ?_⟩
  · -- Time: `u₁ + τ' + uB ≤ 4 + c_f·(t a + 1) + 4`, absorbed by the generous constant.
    have e : (c_f + 2 * K₀ + 12) * (t a + 1)
        = c_f * (t a + 1) + (2 * K₀ + 12) * (t a + 1) := by
      rw [show c_f + 2 * K₀ + 12 = c_f + (2 * K₀ + 12) from by omega, Nat.add_mul]
    have h8 : 8 * 1 ≤ (2 * K₀ + 12) * (t a + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  · -- The composed run halts in the normal-form configuration, with `w` on the output tape.
    rw [outer_run]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l
      rcases tcase l with ⟨j, rfl⟩ | rfl | rfl
      · have hjf : (j.castAdd 2 : Fin (K₀ + 2)) ≠ ⟨K₀ + 1, by omega⟩ :=
          Fin.ne_of_val_ne (by have := j.isLt; simp; omega)
        have hji : (j.castAdd 2 : Fin (K₀ + 2)) ≠ ⟨K₀, by omega⟩ :=
          Fin.ne_of_val_ne (by have := j.isLt; simp; omega)
        funext z
        simp only [Cfg.withState_workTapes, Function.update_of_ne hjf, inCfg_workTapes_castAdd,
          wordsCfg_workTapes, hws₀']
        by_cases hjo : j = o₀
        · subst hjo
          simp only [Function.update_self]
        · have hjo2 : (j.castAdd 2 : Fin (K₀ + 2)) ≠ o₀.castAdd 2 :=
            fun hh => hjo (Fin.ext (by simpa using congrArg Fin.val hh))
          simp only [Function.update_of_ne hjo, Function.update_of_ne hjo2, hblank _ hji]
      · have hio : (⟨K₀, by omega⟩ : Fin (K₀ + 2)) ≠ o₀.castAdd 2 :=
          Fin.ne_of_val_ne (by have := o₀.isLt; simp; omega)
        have hif : (⟨K₀, by omega⟩ : Fin (K₀ + 2)) ≠ ⟨K₀ + 1, by omega⟩ :=
          Fin.ne_of_val_ne (by simp)
        funext z
        simp only [Cfg.withState_workTapes, Function.update_of_ne hif, inCfg_workTapes_vip,
          wordsCfg_workTapes, Function.update_of_ne hio, hi]
      · have hfo : (⟨K₀ + 1, by omega⟩ : Fin (K₀ + 2)) ≠ o₀.castAdd 2 :=
          Fin.ne_of_val_ne (by have := o₀.isLt; simp; omega)
        have hfi : (⟨K₀ + 1, by omega⟩ : Fin (K₀ + 2)) ≠ ⟨K₀, by omega⟩ :=
          Fin.ne_of_val_ne (by simp)
        funext z
        rcases eq_or_ne z (-1 : ℤ) with hz | hz
        · subst hz
          simp [Cfg.withState_workTapes, wordsCfg_workTapes,
            Function.update_self, Function.update_of_ne hfo, hblank _ hfi, tapeOfList_nil]
        · simp [Cfg.withState_workTapes, inCfg_workTapes_flag, wordsCfg_workTapes,
            Function.update_self, Function.update_of_ne hz, Function.update_of_ne hfo,
            hblank _ hfi, tapeOfList_nil]
    · funext l
      rcases tcase l with ⟨j, rfl⟩ | rfl | rfl
      · simp [Cfg.withState_workTapePos, inCfg_workTapePos_castAdd, wordsCfg_workTapePos]
      · simp [Cfg.withState_workTapePos, inCfg_workTapePos_vip, wordsCfg_workTapePos,
          wordsCfg_inputPos]
      · simp [Cfg.withState_workTapePos, inCfg_workTapePos_flag, wordsCfg_workTapePos,
          wordsCfg_inputPos]
  · -- Space: the two flag writes plus the redirected run fit the generous budget.
    refine le_trans outer_sp ?_
    have eL : (c_f + 2 * K₀ + 12) * (s a + (enc a).length + w.length + 1)
        = c_f * (s a + (enc a).length + w.length + 1)
          + (2 * K₀ + 12) * (s a + (enc a).length + w.length + 1) := by
      rw [show c_f + 2 * K₀ + 12 = c_f + (2 * K₀ + 12) from by omega, Nat.add_mul]
    have ecf : c_f * (s a + w.length + 1)
        ≤ c_f * (s a + (enc a).length + w.length + 1) := Nat.mul_le_mul (le_refl _) (by omega)
    have ebig : (2 * K₀ + 12) * ((enc a).length + 1)
        ≤ (2 * K₀ + 12) * (s a + (enc a).length + w.length + 1) :=
      Nat.mul_le_mul (le_refl _) (by omega)
    have eexp : (2 * K₀ + 12) * ((enc a).length + 1)
        = (2 * K₀ + 12) * (enc a).length + (2 * K₀ + 12) := by
      rw [Nat.mul_add, Nat.mul_one]
    have elen : 2 * (enc a).length ≤ (2 * K₀ + 12) * (enc a).length :=
      Nat.mul_le_mul (by omega) (le_refl _)
    omega

/-- **From a tape transformer back to a computable function.** A machine that, reading the input
from the real input tape with every work tape blank, halts with the encoded result on work tape
`o`, computes that function once the result is copied from tape `o` to the real output tape. -/
public theorem computableInTimeAndSpace_of_transformsTapes {K : ℕ} {State : Type} [Finite State]
    (o : Fin K) {tm : MultiTapeTM K Bool State}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {gg : α → β} {t s : α → ℕ}
    (hT : ∀ a, TransformsTapes tm (fun input ws => input = encIn a ∧ ∀ l, ws l = [])
      (fun _ _ ws' => ws' o = encOut (gg a)) (t a) (s a)) :
    ∃ c, ComputableInTimeAndSpace gg encIn encOut
      (fun a => c * (t a + (encOut (gg a)).length + 1))
      (fun a => c * (s a + (encOut (gg a)).length + 1)) := by
  obtain ⟨SE, hSE, tmE, hE⟩ := exists_emitTape (Symbol := Bool) o
  have := hSE
  refine ⟨K + 2, K, State ⊕ SE, inferInstance, tm.seq tmE, fun a => ?_⟩
  -- run the transformer, then emit tape `o`
  set start := (tm.seq tmE).initCfg (encIn a) with hstart
  have hstart_words : start = wordsCfg (encIn a) (some (tm.seq tmE).q₀) (fun _ => []) [] := by
    rw [hstart, initCfg_eq_wordsCfg]
  -- phase 1: the transformer halts with the result on tape `o`
  obtain ⟨τ, hτ, ws', hrun1, hws', hsp1⟩ :=
    hT a (encIn a) (fun _ => []) [] ⟨rfl, fun _ => rfl⟩
  have hc1eq : tm.runFrom (start.withState (some tm.q₀)) τ =
      wordsCfg (encIn a) none ws' [] := by
    rw [hstart_words]; exact hrun1
  -- first halting time of phase 1, for activity
  obtain ⟨τ', hτ'le, hτ'halt, hτ'act⟩ :=
    exists_minimal_halting_time tm (start.withState (some tm.q₀)) τ (by rw [hc1eq]; rfl)
  have hc1eq' : tm.runFrom (start.withState (some tm.q₀)) τ' = wordsCfg (encIn a) none ws' [] :=
    (runFrom_eq_of_halt tm _ hτ'le hτ'halt).symm.trans hc1eq
  set c₁ := wordsCfg (encIn a) (none : Option State) ws' [] with hc1def
  -- tape `o` holds the encoded result, head at 0
  have ho_tape : c₁.workTapes o = tapeOfList (encOut (gg a)) := by
    rw [hc1def]
    change tapeOfList (ws' o) = tapeOfList (encOut (gg a))
    rw [hws']
  have ho_pos : c₁.workTapePos o = 0 := by rw [hc1def, wordsCfg_workTapePos]
  -- phase 2: emit tape `o` to the output
  obtain ⟨u₂, hu₂, h₂act, h₂run, h₂frame⟩ :=
    hE (encIn a) (c₁.withState (some tmE.q₀)) (encOut (gg a)) rfl ho_tape ho_pos
  -- the two phase-space bounds
  have hstartws : start.withState (some tm.q₀) =
      wordsCfg (encIn a) (some tm.q₀) (fun _ => []) [] := by
    rw [hstart_words]; rfl
  have hsp1' : tm.spaceUsed (start.withState (some tm.q₀)) τ' ≤ s a := by
    rw [hstartws]
    exact le_trans (spaceUsed_mono tm _ hτ'le) hsp1
  have hsp2' : tmE.spaceUsed (c₁.withState (some tmE.q₀)) u₂ ≤
      (encOut (gg a)).length + 1 + K := by
    refine le_trans (spaceUsed_le_of_one_moving (c₁.withState (some tmE.q₀)) u₂ o
      0 ((encOut (gg a)).length : ℤ) (fun m hm => ⟨(h₂frame m hm).2.2.2.1,
        (h₂frame m hm).2.2.2.2⟩) (fun m hm j hj => (h₂frame m hm).2.2.1 j hj)) ?_
    have : ((encOut (gg a)).length + 1 - (0 : ℤ)).toNat = (encOut (gg a)).length + 1 := by omega
    omega
  -- assemble
  obtain ⟨hseq_run, hseq_act, hseq_sp⟩ :=
    seq_spec (tm₁ := tm) (tm₂ := tmE) (c := start) (by rw [hstart_words]; rfl)
      hc1eq' (by rw [hc1def]; rfl) hτ'act hsp1' h₂run rfl h₂act hsp2'
  refine ⟨τ' + u₂, ?_, (tm.seq tmE).spaceUsed start (τ' + u₂), ?_, ?_, ?_, rfl⟩
  · -- time bound: τ'+u₂ ≤ t a+|encOut|+2 ≤ (K+2)·(t a+|encOut|+1)
    change τ' + u₂ ≤ (K + 2) * (t a + (encOut (gg a)).length + 1)
    have hu : u₂ ≤ (encOut (gg a)).length + 2 := hu₂
    have hτt : τ' ≤ t a := le_trans hτ'le hτ
    have hprod2 : 2 * (t a + (encOut (gg a)).length + 1)
        ≤ (K + 2) * (t a + (encOut (gg a)).length + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · -- space bound: s a + (|encOut|+1+K) ≤ (K+2)·(s a + |encOut| + 1)
    change (tm.seq tmE).spaceUsed start (τ' + u₂) ≤ (K + 2) * (s a + (encOut (gg a)).length + 1)
    refine le_trans hseq_sp ?_
    set S := s a + (encOut (gg a)).length + 1 with hSdef
    have hKS : K ≤ K * S := Nat.le_mul_of_pos_right K (by omega)
    have hexp : (K + 2) * S = K * S + S + S := by rw [Nat.add_mul]; omega
    have hrw : s a + ((encOut (gg a)).length + 1 + K) = S + K := by omega
    omega
  · -- the run halts
    rw [hseq_run]; rfl
  · -- output is the encoded result
    rw [hseq_run]
    simp only [Cfg.withState_output]
    change (c₁.withState (some tmE.q₀)).output ++ encOut (gg a) = encOut (gg a)
    rw [Cfg.withState_output, hc1def, wordsCfg_output, List.nil_append]

/-- A `wordsCfg` over `k'` tapes, viewed as the `k`-tape `wordsCfg` on the tapes selected by `e`,
embedded with the remaining tapes carrying the leftover words. -/
private lemma wordsCfg_eq_embed {k k' : ℕ} {State : Type} (e : Fin k ↪ Fin k')
    (input : List Bool) (q : Option State) (ws : Fin k' → List Bool) (out : List Bool) :
    wordsCfg input q ws out =
      embed e (wordsCfg input q (fun j => ws (e j)) out)
        (fun l => tapeOfList (ws l)) (fun _ => 0) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext l z
    change tapeOfList (ws l) z = _
    rcases hpi : partialInv e l with _ | j
    · simp [embed, hpi]
    · simp only [embed, hpi, wordsCfg_workTapes, partialInv_eq_some e hpi]
  · funext l
    change (0 : ℤ) = _
    rcases hpi : partialInv e l with _ | j <;> simp [embed, hpi]

/-- **Reindexing preserves being a tape transformer.** If `M` transforms tapes along `P`/`Q`, then
`extendTapes M e` transforms them on the tapes selected by `e`, leaving the tapes outside the range
of `e` untouched, in the same time and space plus one cell per added tape. -/
public theorem transformsTapes_extendTapes {k k' : ℕ} {State : Type}
    (e : Fin k ↪ Fin k') {M : MultiTapeTM k Bool State}
    {P : (input : List Bool) → (Fin k → List Bool) → Prop}
    {Q : (input : List Bool) → (Fin k → List Bool) → (Fin k → List Bool) → Prop}
    {t s : ℕ} (h : TransformsTapes M P Q t s) :
    TransformsTapes (extendTapes M e)
      (fun input ws => P input (fun j => ws (e j)) ∧ ∀ l, (∀ j, e j ≠ l) → ws l = [])
      (fun input ws ws' => Q input (fun j => ws (e j)) (fun j => ws' (e j)) ∧
        ∀ l, (∀ j, e j ≠ l) → ws' l = ws l)
      t (s + (k' - k)) := by
  intro input ws out ⟨hP, hextra⟩
  -- the start config, viewed through the embedding
  have hstart : wordsCfg input (some (extendTapes M e).q₀) ws out =
      embed e (wordsCfg input (some M.q₀) (fun j => ws (e j)) out)
        (fun l => tapeOfList (ws l)) (fun _ => 0) :=
    wordsCfg_eq_embed e input (some M.q₀) ws out
  -- run the inner machine
  obtain ⟨τ, hτ, ws', hrun, hQ, hsp⟩ :=
    h input (fun j => ws (e j)) out hP
  refine ⟨τ, hτ, fun l => match partialInv e l with | some j => ws' j | none => ws l, ?_, ?_, ?_⟩
  · -- the run: the embedded halting config is a `wordsCfg`
    rw [hstart, runFrom_embed, hrun]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l z
      change (embed e (wordsCfg input (none : Option State) ws' out)
        (fun l => tapeOfList (ws l)) (fun _ => 0)).workTapes l z =
        (wordsCfg input (none : Option State)
          (fun l => match partialInv e l with | some j => ws' j | none => ws l) out).workTapes l z
      rcases hpi : partialInv e l with _ | j
      · simp [embed, hpi]
      · simp [embed, hpi, wordsCfg_workTapes]
    · funext l
      change (embed e (wordsCfg input (none : Option State) ws' out)
        (fun l => tapeOfList (ws l)) (fun _ => 0)).workTapePos l = (0 : ℤ)
      rcases hpi : partialInv e l with _ | j <;> simp [embed, hpi]
  · -- the postcondition
    refine ⟨?_, ?_⟩
    · have : (fun j => (fun l => match partialInv e l with | some j => ws' j | none => ws l) (e j))
          = ws' := by
        funext j; simp only [partialInv_embed]
      rw [this]; exact hQ
    · intro l hl
      simp only [partialInv_eq_none e (fun ⟨j, hj⟩ => hl j hj)]
  · -- the space
    rw [hstart]
    exact le_trans (spaceUsed_embed_le M e _ _ _ τ) (Nat.add_le_add_right hsp _)

/-- **Reindexing preserves being a tape transformer (relaxed precondition).** Same as
`transformsTapes_extendTapes`, but the precondition no longer requires the tapes outside `range e`
to be blank: those tapes are simply carried through unchanged, as the postcondition records. -/
public theorem transformsTapes_extendTapes' {k k' : ℕ} {State : Type}
    (e : Fin k ↪ Fin k') {M : MultiTapeTM k Bool State}
    {P : (input : List Bool) → (Fin k → List Bool) → Prop}
    {Q : (input : List Bool) → (Fin k → List Bool) → (Fin k → List Bool) → Prop}
    {t s : ℕ} (h : TransformsTapes M P Q t s) :
    TransformsTapes (extendTapes M e)
      (fun input ws => P input (fun j => ws (e j)))
      (fun input ws ws' => Q input (fun j => ws (e j)) (fun j => ws' (e j)) ∧
        ∀ l, (∀ j, e j ≠ l) → ws' l = ws l)
      t (s + (k' - k)) := by
  intro input ws out hP
  -- the start config, viewed through the embedding
  have hstart : wordsCfg input (some (extendTapes M e).q₀) ws out =
      embed e (wordsCfg input (some M.q₀) (fun j => ws (e j)) out)
        (fun l => tapeOfList (ws l)) (fun _ => 0) :=
    wordsCfg_eq_embed e input (some M.q₀) ws out
  -- run the inner machine
  obtain ⟨τ, hτ, ws', hrun, hQ, hsp⟩ :=
    h input (fun j => ws (e j)) out hP
  refine ⟨τ, hτ, fun l => match partialInv e l with | some j => ws' j | none => ws l, ?_, ?_, ?_⟩
  · -- the run: the embedded halting config is a `wordsCfg`
    rw [hstart, runFrom_embed, hrun]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l z
      change (embed e (wordsCfg input (none : Option State) ws' out)
        (fun l => tapeOfList (ws l)) (fun _ => 0)).workTapes l z =
        (wordsCfg input (none : Option State)
          (fun l => match partialInv e l with | some j => ws' j | none => ws l) out).workTapes l z
      rcases hpi : partialInv e l with _ | j
      · simp [embed, hpi]
      · simp [embed, hpi, wordsCfg_workTapes]
    · funext l
      change (embed e (wordsCfg input (none : Option State) ws' out)
        (fun l => tapeOfList (ws l)) (fun _ => 0)).workTapePos l = (0 : ℤ)
      rcases hpi : partialInv e l with _ | j <;> simp [embed, hpi]
  · -- the postcondition
    refine ⟨?_, ?_⟩
    · have : (fun j => (fun l => match partialInv e l with | some j => ws' j | none => ws l) (e j))
          = ws' := by
        funext j; simp only [partialInv_embed]
      rw [this]; exact hQ
    · intro l hl
      simp only [partialInv_eq_none e (fun ⟨j, hj⟩ => hl j hj)]
  · -- the space
    rw [hstart]
    exact le_trans (spaceUsed_embed_le M e _ _ _ τ) (Nat.add_le_add_right hsp _)

/-- **Placement embedding (two pins).** Given distinct canonical indices `i₀ ≠ o₀` in `Fin K` and
distinct target indices `i ≠ o` in `Fin k` avoiding a set `keep`, with enough room
(`K + keep.card ≤ k`), there is an embedding `Fin K ↪ Fin k` sending `i₀ ↦ i`, `o₀ ↦ o`, and every
other index to a tape outside `insert i (insert o keep)`. -/
private lemma exists_embed_placing {K k : ℕ} (i₀ o₀ : Fin K) (hio₀ : i₀ ≠ o₀)
    (i o : Fin k) (keep : Finset (Fin k)) (hio : i ≠ o) (_hik : i ∉ keep) (_hok : o ∉ keep)
    (hroom : K + keep.card ≤ k) :
    ∃ e : Fin K ↪ Fin k, e i₀ = i ∧ e o₀ = o ∧
      ∀ j, j ≠ i₀ → j ≠ o₀ → e j ∉ insert i (insert o keep) := by
  classical
  set forb : Finset (Fin k) := insert i (insert o keep) with hforb
  set avail : Finset (Fin k) := Finset.univ \ forb with havail
  have hforb_card : forb.card ≤ keep.card + 2 := by
    have h1 : (insert o keep).card ≤ keep.card + 1 := Finset.card_insert_le _ _
    have h2 : forb.card ≤ (insert o keep).card + 1 := by
      rw [hforb]; exact Finset.card_insert_le _ _
    omega
  have havail_card : avail.card = k - forb.card := by
    rw [havail, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hlhs : (Finset.univ \ {i₀, o₀} : Finset (Fin K)).card = K - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair_eq_two_iff.mpr hio₀]
  have hcard_le : Fintype.card {x : Fin K // x ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K))}
      ≤ Fintype.card {x : Fin k // x ∈ avail} := by
    simp only [Fintype.card_coe]
    rw [hlhs, havail_card]; omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard_le
  have hmem : ∀ j : Fin K, j ≠ i₀ → j ≠ o₀ →
      j ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K)) := by
    intro j hj1 hj2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hj1, hj2⟩
  have hg_forb : ∀ y : {x : Fin K // x ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K))},
      (g y).val ∉ forb := by
    intro y
    have hy : (g y).val ∈ Finset.univ \ forb := (g y).2
    exact (Finset.mem_sdiff.mp hy).2
  have hi_forb : i ∈ forb := by rw [hforb]; exact Finset.mem_insert_self _ _
  have ho_forb : o ∈ forb := by
    rw [hforb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hg_ne_i : ∀ y, (g y).val ≠ i := fun y hcon => hg_forb y (by rw [hcon]; exact hi_forb)
  have hg_ne_o : ∀ y, (g y).val ≠ o := fun y hcon => hg_forb y (by rw [hcon]; exact ho_forb)
  set f : Fin K → Fin k := fun j =>
    if hj : j ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K)) then (g ⟨j, hj⟩).val
    else if j = i₀ then i else o with hf_def
  have hmem_i₀ : i₀ ∉ (Finset.univ \ {i₀, o₀} : Finset (Fin K)) := by simp
  have hmem_o₀ : o₀ ∉ (Finset.univ \ {i₀, o₀} : Finset (Fin K)) := by simp
  have hfi₀ : f i₀ = i := by
    rw [hf_def]; dsimp only; rw [dite_eq_right hmem_i₀]; exact ite_eq_left rfl
  have hfo₀ : f o₀ = o := by
    rw [hf_def]; dsimp only; rw [dite_eq_right hmem_o₀]; exact ite_eq_right (Ne.symm hio₀)
  have hfother : ∀ j (hj : j ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K))),
      f j = (g ⟨j, hj⟩).val := by
    intro j hj; rw [hf_def]; dsimp only; rw [dite_eq_left hj]
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_cases ha : a ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K))
    · by_cases hb : b ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K))
      · rw [hfother a ha, hfother b hb] at hab
        exact congrArg Subtype.val (g.injective (Subtype.ext hab))
      · exfalso
        rw [hfother a ha] at hab
        have hb' : b = i₀ ∨ b = o₀ := by
          by_contra hbc; rw [not_or] at hbc; exact hb (hmem b hbc.1 hbc.2)
        rcases hb' with rfl | rfl
        · rw [hfi₀] at hab; exact hg_ne_i _ hab
        · rw [hfo₀] at hab; exact hg_ne_o _ hab
    · by_cases hb : b ∈ (Finset.univ \ {i₀, o₀} : Finset (Fin K))
      · exfalso
        rw [hfother b hb] at hab
        have ha' : a = i₀ ∨ a = o₀ := by
          by_contra hac; rw [not_or] at hac; exact ha (hmem a hac.1 hac.2)
        rcases ha' with rfl | rfl
        · rw [hfi₀] at hab; exact hg_ne_i _ hab.symm
        · rw [hfo₀] at hab; exact hg_ne_o _ hab.symm
      · have ha' : a = i₀ ∨ a = o₀ := by
          by_contra hac; rw [not_or] at hac; exact ha (hmem a hac.1 hac.2)
        have hb' : b = i₀ ∨ b = o₀ := by
          by_contra hbc; rw [not_or] at hbc; exact hb (hmem b hbc.1 hbc.2)
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · rfl
        · exfalso; rw [hfi₀, hfo₀] at hab; exact hio hab
        · exfalso; rw [hfi₀, hfo₀] at hab; exact hio hab.symm
        · rfl
  refine ⟨⟨f, hf_inj⟩, hfi₀, hfo₀, ?_⟩
  intro j hj1 hj2
  change f j ∉ forb
  rw [hfother j (hmem j hj1 hj2)]
  exact hg_forb ⟨j, hmem j hj1 hj2⟩

/-- **Placement embedding (one pin).** Like `exists_embed_placing`, but pinning a single index
`o₀ ↦ o`, sending every other index outside `insert o keep`. -/
private lemma exists_embed_placing_one {K k : ℕ} (o₀ : Fin K)
    (o : Fin k) (keep : Finset (Fin k)) (_hok : o ∉ keep) (hroom : K + keep.card ≤ k) :
    ∃ e : Fin K ↪ Fin k, e o₀ = o ∧ ∀ j, j ≠ o₀ → e j ∉ insert o keep := by
  classical
  set forb : Finset (Fin k) := insert o keep with hforb
  set avail : Finset (Fin k) := Finset.univ \ forb with havail
  have hforb_card : forb.card ≤ keep.card + 1 := by rw [hforb]; exact Finset.card_insert_le _ _
  have havail_card : avail.card = k - forb.card := by
    rw [havail, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hlhs : (Finset.univ \ {o₀} : Finset (Fin K)).card = K - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton]
  have hcard_le : Fintype.card {x : Fin K // x ∈ (Finset.univ \ {o₀} : Finset (Fin K))}
      ≤ Fintype.card {x : Fin k // x ∈ avail} := by
    simp only [Fintype.card_coe]
    rw [hlhs, havail_card]; omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard_le
  have hmem : ∀ j : Fin K, j ≠ o₀ → j ∈ (Finset.univ \ {o₀} : Finset (Fin K)) := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hj
  have hg_forb : ∀ y : {x : Fin K // x ∈ (Finset.univ \ {o₀} : Finset (Fin K))},
      (g y).val ∉ forb := by
    intro y
    have hy : (g y).val ∈ Finset.univ \ forb := (g y).2
    exact (Finset.mem_sdiff.mp hy).2
  have ho_forb : o ∈ forb := by rw [hforb]; exact Finset.mem_insert_self _ _
  have hg_ne_o : ∀ y, (g y).val ≠ o := fun y hcon => hg_forb y (by rw [hcon]; exact ho_forb)
  set f : Fin K → Fin k := fun j =>
    if hj : j ∈ (Finset.univ \ {o₀} : Finset (Fin K)) then (g ⟨j, hj⟩).val else o with hf_def
  have hmem_o₀ : o₀ ∉ (Finset.univ \ {o₀} : Finset (Fin K)) := by simp
  have hfo₀ : f o₀ = o := by rw [hf_def]; dsimp only; rw [dite_eq_right hmem_o₀]
  have hfother : ∀ j (hj : j ∈ (Finset.univ \ {o₀} : Finset (Fin K))),
      f j = (g ⟨j, hj⟩).val := by
    intro j hj; rw [hf_def]; dsimp only; rw [dite_eq_left hj]
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_cases ha : a ∈ (Finset.univ \ {o₀} : Finset (Fin K))
    · by_cases hb : b ∈ (Finset.univ \ {o₀} : Finset (Fin K))
      · rw [hfother a ha, hfother b hb] at hab
        exact congrArg Subtype.val (g.injective (Subtype.ext hab))
      · exfalso
        rw [hfother a ha] at hab
        have hb' : b = o₀ := by by_contra hbc; exact hb (hmem b hbc)
        rw [hb', hfo₀] at hab; exact hg_ne_o _ hab
    · by_cases hb : b ∈ (Finset.univ \ {o₀} : Finset (Fin K))
      · exfalso
        rw [hfother b hb] at hab
        have ha' : a = o₀ := by by_contra hac; exact ha (hmem a hac)
        rw [ha', hfo₀] at hab; exact hg_ne_o _ hab.symm
      · have ha' : a = o₀ := by by_contra hac; exact ha (hmem a hac)
        have hb' : b = o₀ := by by_contra hbc; exact hb (hmem b hbc)
        rw [ha', hb']
  refine ⟨⟨f, hf_inj⟩, hfo₀, ?_⟩
  intro j hj
  change f j ∉ forb
  rw [hfother j (hmem j hj)]
  exact hg_forb ⟨j, hmem j hj⟩

/-- **A computable function, read from a work tape, as a tape transformer (general layout).** Placed
on any tape count `k` with a chosen input tape `i`, output tape `o` and a set `keep` of tapes to
leave untouched, provided there is room for the machine's own tapes. -/
public theorem exists_transformsTapes_ofComputable {α β : Type*} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace g enc encOut t s) :
    ∃ m c : ℕ, ∀ (k : ℕ) (i o : Fin k) (keep : Finset (Fin k)),
      i ≠ o → i ∉ keep → o ∉ keep → m + 2 + keep.card ≤ k →
      ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ a : α,
        TransformsTapes tm
          (fun _ ws => ws i = enc a ∧ ∀ l, l ≠ i → l ∉ keep → ws l = [])
          (fun _ ws ws' => ws' = Function.update ws o (encOut (g a)))
          (c * (t a + 1))
          (c * (s a + (enc a).length + (encOut (g a)).length + 1) + k) := by
  classical
  obtain ⟨c, K, i₀, o₀, State₀, hfin₀, tm₀, hio₀, hcanon⟩ :=
    exists_transformsTapes_ofComputable_fixed h
  have hK2 : 2 ≤ K := by
    by_contra hlt
    exact hio₀ (Fin.ext (by have := i₀.isLt; have := o₀.isLt; omega))
  refine ⟨K - 2, c, fun k i o keep hio hik hok hroom => ?_⟩
  have hKk : K ≤ k := by omega
  have hroom' : K + keep.card ≤ k := by omega
  obtain ⟨e, hei, heo, hother⟩ :=
    exists_embed_placing i₀ o₀ hio₀ i o keep hio hik hok hroom'
  refine ⟨State₀, hfin₀, extendTapes tm₀ e, fun a => ?_⟩
  refine (transformsTapes_extendTapes' e (hcanon a)).imp ?_ ?_ le_rfl ?_
  · -- precondition: the general layout satisfies the embedded canonical precondition
    rintro input ws ⟨hwi, hwblank⟩
    refine ⟨?_, ?_⟩
    · change ws (e i₀) = enc a
      rw [hei]; exact hwi
    · intro l' hl'
      change ws (e l') = []
      by_cases hlo : l' = o₀
      · subst hlo; rw [heo]; exact hwblank o (Ne.symm hio) hok
      · have hmem := hother l' hl' hlo
        rw [Finset.mem_insert, not_or] at hmem
        obtain ⟨hne_i, hmem2⟩ := hmem
        rw [Finset.mem_insert, not_or] at hmem2
        exact hwblank (e l') hne_i hmem2.2
  · -- postcondition: read the update back through the embedding
    rintro input ws ws' _ ⟨hQ1, hQ2⟩
    funext l
    by_cases hlo : l = o
    · subst hlo
      have hh := congrFun hQ1 o₀
      simp only [heo, Function.update_self] at hh
      rw [Function.update_self]; exact hh
    · rw [Function.update_of_ne hlo]
      by_cases hex : ∃ j, e j = l
      · obtain ⟨j, rfl⟩ := hex
        have hjo : j ≠ o₀ := by intro hj; apply hlo; rw [hj, heo]
        have hh := congrFun hQ1 j
        rw [Function.update_of_ne hjo] at hh
        exact hh
      · exact hQ2 l (fun j hj => hex ⟨j, hj⟩)
  · -- space
    omega

/-- **A computable function, read from the input tape, as a tape transformer (general layout).**
Placed on any tape count `k` with a chosen output tape `o` and a set `keep` of tapes to leave
untouched, provided there is room for the machine's own tapes. -/
public theorem exists_transformsTapes_ofComputableInput {α β : Type*} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {g : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace g enc encOut t s) :
    ∃ m c : ℕ, ∀ (k : ℕ) (o : Fin k) (keep : Finset (Fin k)),
      o ∉ keep → m + 1 + keep.card ≤ k →
      ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ a : α,
        TransformsTapes tm
          (fun input ws => input = enc a ∧ ∀ l, l ∉ keep → ws l = [])
          (fun _ ws ws' => ws' = Function.update ws o (encOut (g a)))
          (c * (t a + 1))
          (c * (s a + (encOut (g a)).length + 1) + k) := by
  classical
  obtain ⟨c, K, o₀, State₀, hfin₀, tm₀, hcanon⟩ :=
    exists_transformsTapes_ofComputableInput_fixed h
  have hK1 : 1 ≤ K := by have := o₀.isLt; omega
  refine ⟨K - 1, c, fun k o keep hok hroom => ?_⟩
  have hKk : K ≤ k := by omega
  have hroom' : K + keep.card ≤ k := by omega
  obtain ⟨e, heo, hother⟩ := exists_embed_placing_one o₀ o keep hok hroom'
  refine ⟨State₀, hfin₀, extendTapes tm₀ e, fun a => ?_⟩
  refine (transformsTapes_extendTapes' e (hcanon a)).imp ?_ ?_ le_rfl ?_
  · -- precondition
    rintro input ws ⟨hinput, hwblank⟩
    refine ⟨hinput, ?_⟩
    intro l'
    change ws (e l') = []
    by_cases hlo : l' = o₀
    · subst hlo; rw [heo]; exact hwblank o hok
    · have hmem := hother l' hlo
      rw [Finset.mem_insert, not_or] at hmem
      exact hwblank (e l') hmem.2
  · -- postcondition
    rintro input ws ws' _ ⟨hQ1, hQ2⟩
    funext l
    by_cases hlo : l = o
    · subst hlo
      have hh := congrFun hQ1 o₀
      simp only [heo, Function.update_self] at hh
      rw [Function.update_self]; exact hh
    · rw [Function.update_of_ne hlo]
      by_cases hex : ∃ j, e j = l
      · obtain ⟨j, rfl⟩ := hex
        have hjo : j ≠ o₀ := by intro hj; apply hlo; rw [hj, heo]
        have hh := congrFun hQ1 j
        rw [Function.update_of_ne hjo] at hh
        exact hh
      · exact hQ2 l (fun j hj => hex ⟨j, hj⟩)
  · -- space
    omega

end Turing.MultiTapeTM
