/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Adapters
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Complexity of a concatenation of two functions

If `f` and `g` are computable, then so is any function whose encoded result is the encoded result
of `f` followed by the encoded result of `g`. The machine runs a *tidy* machine for `f`, which
halts with `encB (f x)` on the append-only output tape and every work tape blank and the input head
rewound, and then a tidy machine for `g` on disjoint work tapes, which appends `encC (g x)` to the
same output tape. The intermediate results are never stored on a work tape: both machines write
straight to the output, which is append-only, so the outputs end up concatenated.

Because the tidy machine rewinds the input head and re-blanks its work tapes, the configuration
between the two phases is again a clean word configuration, and the second machine reads the same
input as the first with no explicit rewinding step in between.

This is the introduction rule of a finite product, dual to the case analysis of
`Cslib.Computability.Machines.Turing.MultiTape.Combinators.Ite`. Note that only the *syntactic*
factorisation of the encoding is required: producing a pair asks nothing of the encoding beyond
`henc`; reading a component back out is a genuine computability requirement, handled elsewhere.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_concat`: the complexity of a concatenation.
* `Turing.MultiTapeTM.computableInTimeAndSpace_pair`: the special case of a pair.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ δ : Type*} {k : ℕ} {State : Type*} {input : List Bool}

/-- Running from a configuration with a nonempty output tape is the same as running from the empty
one and prepending: the transition never reads the output, so its only effect on the run is a
constant prefix on the final output tape. -/
private lemma step_withOutput_prepend (tm : MultiTapeTM k Bool State) (Y : List Bool)
    (c : Cfg k Bool State input) :
    tm.step (c.withOutput (Y ++ c.output)) =
      (tm.step c).withOutput (Y ++ (tm.step c).output) := by
  cases hq : c.state with
  | none =>
    have h1 : (c.withOutput (Y ++ c.output)).state = none := hq
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (c.withOutput (Y ++ c.output)).state = some q := hq
    have hin : (c.withOutput (Y ++ c.output)).inputSymbol = c.inputSymbol := rfl
    have hws : (c.withOutput (Y ++ c.output)).workTapeSymbols = c.workTapeSymbols := rfl
    rw [step_apply_of_state h1, step_apply_of_state hq, hin, hws]
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [Action.apply_output, Cfg.withOutput_output, List.append_assoc]

/-- The run from a configuration with output `Y ++ c.output` is the run from `c` with `Y` prepended
to the final output. -/
private lemma runFrom_withOutput_prepend (tm : MultiTapeTM k Bool State) (Y : List Bool)
    (c : Cfg k Bool State input) (n : ℕ) :
    tm.runFrom (c.withOutput (Y ++ c.output)) n =
      (tm.runFrom c n).withOutput (Y ++ (tm.runFrom c n).output) :=
  runFrom_comm_of_step (fun c => c.withOutput (Y ++ c.output))
    (fun c => step_withOutput_prepend tm Y c) c n

/-- Replacing the output of a word configuration is again a word configuration. -/
private lemma withOutput_wordsCfg (q : Option State) (ws : Fin k → List Bool) (o z : List Bool) :
    (wordsCfg input q ws o).withOutput z = wordsCfg input q ws z := rfl

/-- An all-blank word configuration on `k` tapes, embedded through `er` with blank extra tapes, is
that same all-blank word configuration. Both hold the empty word on every tape with every head at
the start. -/
private lemma embed_blank_collapse {kr : ℕ} {Sr : Type} (er : Fin kr ↪ Fin k)
    (input : List Bool) (q : Option Sr) (out : List Bool) :
    embed er (wordsCfg input q (fun _ => []) out) (fun _ _ => none) (fun _ => 0) =
      wordsCfg input q (fun _ => []) out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext l z
    simp only [embed, wordsCfg_workTapes]
    cases partialInv er l <;> simp [tapeOfList_nil]
  · funext l; simp only [embed, wordsCfg_workTapePos]; cases partialInv er l <;> rfl

/-- **Bridge: an all-blank run of a reindexed machine mirrors the underlying machine.** If the
underlying machine `tmr`, started on blank tapes with output `outS`, halts on blank tapes with
output `outF`, then so does `extendTapes tmr er` on the larger blank layout. Both endpoints are
all-blank word configurations, so the tape embedding collapses on each side. -/
private lemma extendTapes_run_blank {kr : ℕ} {Sr : Type} (tmr : MultiTapeTM kr Bool Sr)
    (er : Fin kr ↪ Fin k) (input outS outF : List Bool) (n : ℕ)
    (hrun : tmr.runFrom (wordsCfg input (some tmr.q₀) (fun _ => []) outS) n =
      wordsCfg input none (fun _ => []) outF) :
    (extendTapes tmr er).runFrom
        (wordsCfg input (some (extendTapes tmr er).q₀) (fun _ => []) outS) n =
      wordsCfg input none (fun _ => []) outF := by
  have hstart : wordsCfg input (some (extendTapes tmr er).q₀) (fun _ => []) outS =
      embed er (wordsCfg input (some tmr.q₀) (fun _ => []) outS) (fun _ _ => none) (fun _ => 0) :=
    (embed_blank_collapse er input (some tmr.q₀) outS).symm
  rw [hstart, runFrom_embed, hrun, embed_blank_collapse]

/-- **Bridge for space.** The space used by a reindexed all-blank run is that of the underlying
run plus at most one cell for each of the extra tapes. -/
private lemma spaceUsed_extendTapes_blank {kr : ℕ} {Sr : Type} (tmr : MultiTapeTM kr Bool Sr)
    (er : Fin kr ↪ Fin k) (input outS : List Bool) (n : ℕ) :
    (extendTapes tmr er).spaceUsed
        (wordsCfg input (some (extendTapes tmr er).q₀) (fun _ => []) outS) n ≤
      tmr.spaceUsed (wordsCfg input (some tmr.q₀) (fun _ => []) outS) n + (k - kr) := by
  rw [show wordsCfg input (some (extendTapes tmr er).q₀) (fun _ => []) outS =
      embed er (wordsCfg input (some tmr.q₀) (fun _ => []) outS) (fun _ _ => none) (fun _ => 0) from
    (embed_blank_collapse er input (some tmr.q₀) outS).symm]
  exact spaceUsed_embed_le tmr er _ _ _ n

/-- **Complexity of a concatenation.** If `f` and `g` are computable and the encoded result of `h`
is the encoded result of `f` followed by the encoded result of `g`, then `h` is computable: run a
tidy machine for `f`, whose result is emitted to the output tape, then a tidy machine for `g` on
disjoint work tapes, which appends its result to the same output tape.

The bound is stated in the relaxed multiplicative shape `c * (… + 1)`: nothing downstream needs it
tight, and the space bound carries no output-length term because neither result is ever parked on a
work tape. -/
public theorem computableInTimeAndSpace_concat
    {f : α → β} {g : α → γ} {h : α → δ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {encD : δ ↪ List Bool}
    {tf sf tg sg : α → ℕ}
    (henc : ∀ x, encD (h x) = encB (f x) ++ encC (g x))
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace h encIn encD
      (fun x => c * (tf x + tg x + 1))
      (fun x => c * (sf x + sg x + 1)) := by
  classical
  obtain ⟨cf, kf, Sf, hSf, tmf, Hf⟩ := exists_tidy hf
  obtain ⟨cg, kg, Sg, hSg, tmg, Hg⟩ := exists_tidy hg
  have := hSf; have := hSg
  set K := kf + kg with hK
  let e_f : Fin kf ↪ Fin K :=
    ⟨fun j => ⟨j.val, by have := j.isLt; omega⟩,
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simpa using this)⟩
  let e_g : Fin kg ↪ Fin K :=
    ⟨fun j => ⟨kf + j.val, by have := j.isLt; omega⟩,
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simpa using this)⟩
  -- the composed machine and the additive-bound version of the claim
  have main : ComputableInTimeAndSpace h encIn encD
      (fun x => cf * (tf x + 1) + cg * (tg x + 1))
      (fun x => (cf * (sf x + 1) + kf + K) + (cg * (sg x + 1) + kg + K)) := by
    refine ⟨K, Sf ⊕ Sg, inferInstance, (extendTapes tmf e_f).seq (extendTapes tmg e_g), fun x => ?_⟩
    obtain ⟨τf, hτf, hrunf, hspf⟩ := Hf x
    obtain ⟨τg, hτg, hrung, hspg⟩ := Hg x
    -- beta-reduce the tidy bounds so the arithmetic solvers see them
    replace hτf : τf ≤ cf * (tf x + 1) := hτf
    replace hspf : tmf.spaceUsed (tmf.initCfg (encIn x)) τf ≤ cf * (sf x + 1) + kf := hspf
    replace hτg : τg ≤ cg * (tg x + 1) := hτg
    replace hspg : tmg.spaceUsed (tmg.initCfg (encIn x)) τg ≤ cg * (sg x + 1) + kg := hspg
    set start := ((extendTapes tmf e_f).seq (extendTapes tmg e_g)).initCfg (encIn x) with hstart
    have hstart_words : start = wordsCfg (encIn x)
        (some ((extendTapes tmf e_f).seq (extendTapes tmg e_g)).q₀) (fun _ => []) [] := by
      rw [hstart, initCfg_eq_wordsCfg]
    -- the raw `tmg` run started with `encB (f x)` already on the output tape, via prepending
    have hrung' : tmg.runFrom (wordsCfg (encIn x) (some tmg.q₀) (fun _ => []) (encB (f x))) τg =
        wordsCfg (encIn x) none (fun _ => []) (encD (h x)) := by
      have hstart_eq :
          wordsCfg (encIn x) (some tmg.q₀) (fun _ => []) (encB (f x)) =
            (tmg.initCfg (encIn x)).withOutput
              (encB (f x) ++ (tmg.initCfg (encIn x)).output) := by
        rw [initCfg_eq_wordsCfg, wordsCfg_output, List.append_nil, withOutput_wordsCfg]
      rw [hstart_eq, runFrom_withOutput_prepend, hrung,
        wordsCfg_output, withOutput_wordsCfg, henc]
    -- phase 1 and phase 2 as reindexed all-blank runs
    have hMf : (extendTapes tmf e_f).runFrom
        (wordsCfg (encIn x) (some (extendTapes tmf e_f).q₀) (fun _ => []) []) τf =
        wordsCfg (encIn x) none (fun _ => []) (encB (f x)) :=
      extendTapes_run_blank tmf e_f (encIn x) [] (encB (f x)) τf
        (by rw [← initCfg_eq_wordsCfg]; exact hrunf)
    have hMg : (extendTapes tmg e_g).runFrom
        (wordsCfg (encIn x) (some (extendTapes tmg e_g).q₀) (fun _ => []) (encB (f x))) τg =
        wordsCfg (encIn x) none (fun _ => []) (encD (h x)) :=
      extendTapes_run_blank tmg e_g (encIn x) (encB (f x)) (encD (h x)) τg hrung'
    -- first halting times, for the activity hypotheses
    obtain ⟨u₁, hu₁le, hu₁halt, hu₁act⟩ :=
      exists_minimal_halting_time (extendTapes tmf e_f)
        (wordsCfg (encIn x) (some (extendTapes tmf e_f).q₀) (fun _ => []) []) τf (by rw [hMf]; rfl)
    have hMf' : (extendTapes tmf e_f).runFrom
        (wordsCfg (encIn x) (some (extendTapes tmf e_f).q₀) (fun _ => []) []) u₁ =
        wordsCfg (encIn x) none (fun _ => []) (encB (f x)) :=
      (runFrom_eq_of_halt _ _ hu₁le hu₁halt).symm.trans hMf
    obtain ⟨u₂, hu₂le, hu₂halt, hu₂act⟩ :=
      exists_minimal_halting_time (extendTapes tmg e_g)
        (wordsCfg (encIn x) (some (extendTapes tmg e_g).q₀) (fun _ => []) (encB (f x))) τg
        (by rw [hMg]; rfl)
    have hMg' : (extendTapes tmg e_g).runFrom
        (wordsCfg (encIn x) (some (extendTapes tmg e_g).q₀) (fun _ => []) (encB (f x))) u₂ =
        wordsCfg (encIn x) none (fun _ => []) (encD (h x)) :=
      (runFrom_eq_of_halt _ _ hu₂le hu₂halt).symm.trans hMg
    -- space bounds for the two phases, via the space bridge
    have hspf' : (extendTapes tmf e_f).spaceUsed
        (wordsCfg (encIn x) (some (extendTapes tmf e_f).q₀) (fun _ => []) []) u₁ ≤
        cf * (sf x + 1) + kf + K := by
      refine le_trans (spaceUsed_extendTapes_blank tmf e_f (encIn x) [] u₁) ?_
      rw [← initCfg_eq_wordsCfg]
      have hb : tmf.spaceUsed (tmf.initCfg (encIn x)) u₁ ≤ cf * (sf x + 1) + kf :=
        le_trans (spaceUsed_mono tmf _ hu₁le) hspf
      omega
    have hspg' : (extendTapes tmg e_g).spaceUsed
        (wordsCfg (encIn x) (some (extendTapes tmg e_g).q₀) (fun _ => []) (encB (f x))) u₂ ≤
        cg * (sg x + 1) + kg + K := by
      refine le_trans (spaceUsed_extendTapes_blank tmg e_g (encIn x) (encB (f x)) u₂) ?_
      -- the raw run's space is output-independent, so the tidy bound (at `initCfg`) controls it
      have hsp_out :
          tmg.spaceUsed (wordsCfg (encIn x) (some tmg.q₀) (fun _ => []) (encB (f x))) u₂ =
            tmg.spaceUsed (tmg.initCfg (encIn x)) u₂ := by
        have hstart_eq :
            wordsCfg (encIn x) (some tmg.q₀) (fun _ => []) (encB (f x)) =
              (tmg.initCfg (encIn x)).withOutput
                (encB (f x) ++ (tmg.initCfg (encIn x)).output) := by
          rw [initCfg_eq_wordsCfg, wordsCfg_output, List.append_nil, withOutput_wordsCfg]
        rw [hstart_eq]
        refine spaceUsed_eq_of_workTapePos _ _ u₂ fun m _ => ?_
        rw [runFrom_withOutput_prepend]; rfl
      rw [hsp_out]
      have hb : tmg.spaceUsed (tmg.initCfg (encIn x)) u₂ ≤ cg * (sg x + 1) + kg :=
        le_trans (spaceUsed_mono tmg _ hu₂le) hspg
      omega
    -- assemble the two phases; the phase start configurations are word configurations
    have hcwf : start.withState (some (extendTapes tmf e_f).q₀) =
        wordsCfg (encIn x) (some (extendTapes tmf e_f).q₀) (fun _ => []) [] := by
      rw [hstart_words]; rfl
    have hcwg :
        (wordsCfg (k := K) (State := Sf) (encIn x) none (fun _ => []) (encB (f x))).withState
          (some (extendTapes tmg e_g).q₀) =
        wordsCfg (encIn x) (some (extendTapes tmg e_g).q₀) (fun _ => []) (encB (f x)) := rfl
    rw [← hcwf] at hMf' hu₁act hspf'
    rw [← hcwg] at hMg' hu₂act hspg'
    obtain ⟨hseq_run, _hseq_act, hseq_sp⟩ :=
      seq_spec (tm₁ := extendTapes tmf e_f) (tm₂ := extendTapes tmg e_g) (c := start)
        (c₁ := wordsCfg (encIn x) none (fun _ => []) (encB (f x)))
        (c₂ := wordsCfg (encIn x) none (fun _ => []) (encD (h x)))
        (by rw [hstart_words]; rfl)
        hMf' rfl hu₁act hspf'
        hMg' rfl hu₂act hspg'
    refine ⟨u₁ + u₂, (by omega : u₁ + u₂ ≤ cf * (tf x + 1) + cg * (tg x + 1)),
      ((extendTapes tmf e_f).seq (extendTapes tmg e_g)).spaceUsed start (u₁ + u₂), hseq_sp,
      ?_, ?_, rfl⟩
    · rw [hseq_run]; rfl
    · rw [hseq_run]; rfl
  -- renormalise the additive bounds into the stated multiplicative shape
  refine ⟨cf + cg + 3 * K + 1, main.mono (fun x => ?_) (fun x => ?_)⟩
  · -- time: `cf·(tf+1) + cg·(tg+1) ≤ (cf+cg)·(tf+tg+1) ≤ D·(tf+tg+1)`
    set D := cf + cg + 3 * K + 1 with hD
    have ha : cf * (tf x + 1) ≤ cf * (tf x + tg x + 1) := Nat.mul_le_mul le_rfl (by omega)
    have hb : cg * (tg x + 1) ≤ cg * (tf x + tg x + 1) := Nat.mul_le_mul le_rfl (by omega)
    have hsum : cf * (tf x + tg x + 1) + cg * (tf x + tg x + 1) =
        (cf + cg) * (tf x + tg x + 1) := (Nat.add_mul _ _ _).symm
    have hDle : (cf + cg) * (tf x + tg x + 1) ≤ D * (tf x + tg x + 1) :=
      Nat.mul_le_mul (by omega) le_rfl
    omega
  · -- space: `cf·(sf+1) + cg·(sg+1) + 3K ≤ (cf+cg+3K)·(sf+sg+1) ≤ D·(sf+sg+1)`
    set D := cf + cg + 3 * K + 1 with hD
    have ha : cf * (sf x + 1) ≤ cf * (sf x + sg x + 1) := Nat.mul_le_mul le_rfl (by omega)
    have hb : cg * (sg x + 1) ≤ cg * (sf x + sg x + 1) := Nat.mul_le_mul le_rfl (by omega)
    have hsum : cf * (sf x + sg x + 1) + cg * (sf x + sg x + 1) =
        (cf + cg) * (sf x + sg x + 1) := (Nat.add_mul _ _ _).symm
    have hkk : 3 * K ≤ (3 * K) * (sf x + sg x + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hsum2 : (cf + cg) * (sf x + sg x + 1) + (3 * K) * (sf x + sg x + 1) =
        (cf + cg + 3 * K) * (sf x + sg x + 1) := (Nat.add_mul _ _ _).symm
    have hDle : (cf + cg + 3 * K) * (sf x + sg x + 1) ≤ D * (sf x + sg x + 1) :=
      Nat.mul_le_mul (by omega) le_rfl
    omega

/-- **Complexity of computing a pair.** The special case of `computableInTimeAndSpace_concat` in
which the two results are packed into a pair, encoded by concatenating the two encodings. -/
public theorem computableInTimeAndSpace_pair
    {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {encPair : β × γ ↪ List Bool} {tf sf tg sg : α → ℕ}
    (henc : ∀ p : β × γ, encPair p = encB p.1 ++ encC p.2)
    (hf : ComputableInTimeAndSpace f encIn encB tf sf)
    (hg : ComputableInTimeAndSpace g encIn encC tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn encPair
      (fun x => c * (tf x + tg x + 1))
      (fun x => c * (sf x + sg x + 1)) :=
  computableInTimeAndSpace_concat (fun x => henc (f x, g x)) hf hg

end Turing.MultiTapeTM
