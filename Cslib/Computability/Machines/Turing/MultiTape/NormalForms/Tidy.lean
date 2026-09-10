/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Instrument
public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Sweep
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# The tidy normal form

A machine given by `ComputesFunInTimeAndSpace` promises nothing about the configuration it halts
in: its work tapes hold garbage — possibly with blanks embedded, so that no scan can find its
extent — and its heads are wherever the run left them. A *tidy* machine halts in the fully
normalised configuration: work tapes blank, all heads back at the start, the input head rewound —
which is exactly a `Turing.MultiTapeTM.wordsCfg`. Tidiness is what the word-transformer interface
(`Turing.MultiTapeTM.TransformsTapes`) needs of a machine before it can be run on redirected
tapes: a tidy machine ends where the next one can begin.

The normal-form theorem — every computable function has a tidy machine, at a constant-factor cost
in time and space — is the deep result of this directory. Its construction instruments the given
machine with one *footprint* tape per work tape, marking every visited cell in lockstep (the
footprint is contiguous because a head path is connected, restoring the scannability that garbage
lacks) with a distinguished anchor mark at cell `0`, and afterwards sweeps each pair clean,
outside-in towards the anchor.

## Main definitions

* `Turing.MultiTapeTM.TidyComputes`: the machine computes the function and halts tidily.

## Main results

* `Turing.MultiTapeTM.exists_tidy`: every computable function has a tidy machine, at a
  constant-factor cost in time and space.
-/

namespace Turing.MultiTapeTM

variable {α β : Type*} {k : ℕ} {Symbol State : Type*}

/-- The machine computes `f` between the given encodings within the given bounds, and halts in the
fully normalised configuration: work tapes blank with heads at the start, input head rewound, the
encoded result as the output. -/
@[expose] public def TidyComputes (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ τ ≤ t a,
    tm.runFrom (tm.initCfg (encIn a)) τ =
      wordsCfg (encIn a) none (fun _ => []) (encOut (f a)) ∧
    tm.spaceUsed (tm.initCfg (encIn a)) τ ≤ s a

/-- A tidy machine computes its function in the ordinary sense: tidiness only adds constraints on
the halting configuration. -/
public theorem TidyComputes.computesFunInTimeAndSpace
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ} (h : TidyComputes tm encIn encOut f t s) :
    ComputesFunInTimeAndSpace tm encIn encOut f t s := by
  intro a
  obtain ⟨τ, hτ, hrun, hspace⟩ := h a
  exact ⟨τ, hτ, _, hspace, by rw [hrun]; rfl, by rw [hrun]; rfl, rfl⟩

section Assembly

open Sequential

variable {K : ℕ} {S₁ S₂ : Type} {input : List Bool}

/-- The machine that halts on its first step, changing nothing. -/
private def haltTM (K : ℕ) : MultiTapeTM K Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

private lemma haltTM_run (c : Cfg K Bool Unit input) (hc : c.state = some ()) :
    (haltTM K).runFrom c 1 = c.withState (none : Option Unit) ∧
    (haltTM K).spaceUsed c 1 ≤ K := by
  have hstep : (haltTM K).step c = c.withState (none : Option Unit) := by
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [step, hc, Action.apply, haltTM, Cfg.withState]
  have hrun : (haltTM K).runFrom c 1 = c.withState (none : Option Unit) := by
    rw [runFrom_succ_eq_step', runFrom_zero, hstep]
  refine ⟨hrun, spaceUsed_le_of_workTapePos_const _ _ fun m hm => ?_⟩
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · rfl
  · rw [hrun]
    rfl

section SweepChain

variable {k₀ : ℕ}

private lemma pair_ne {j j' : Fin k₀} (h : j' ≠ j) :
    j'.castAdd k₀ ≠ j.castAdd k₀ ∧ j'.castAdd k₀ ≠ j.addNat k₀ ∧
    j'.addNat k₀ ≠ j.castAdd k₀ ∧ j'.addNat k₀ ≠ j.addNat k₀ := by
  have hval : j'.val ≠ j.val := fun he => h (Fin.ext he)
  have hj := j.isLt
  have hj' := j'.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Fin.ne_of_val_ne ?_ <;>
    simp only [Fin.val_castAdd, Fin.val_addNat] <;> omega

set_option linter.style.haveILetI false in
/-- Sweeping a list of distinct footprinted pairs, one after the other. -/
private lemma exists_sweepChain (k₀ : ℕ) (js : List (Fin k₀)) (hnd : js.Nodup) :
    ∃ (S : Type) (_ : Finite S) (tm : MultiTapeTM (k₀ + k₀) Bool S),
      ∀ (input : List Bool) (c : Cfg (k₀ + k₀) Bool S input) (L R P : Fin k₀ → ℤ),
        c.state = some tm.q₀ →
        (∀ j ∈ js, L j ≤ 0 ∧ 0 ≤ R j ∧ L j ≤ P j ∧ P j ≤ R j ∧
          c.workTapePos (j.castAdd k₀) = P j ∧ c.workTapePos (j.addNat k₀) = P j ∧
          (∀ z, c.workTapes (j.addNat k₀) z = if z = 0 then some true
            else if L j ≤ z ∧ z ≤ R j then some false else none) ∧
          (∀ z, z < L j ∨ R j < z → c.workTapes (j.castAdd k₀) z = none)) →
        ∃ u ≤ (js.map fun j => 4 * (R j - L j).toNat + 8).sum + 1,
          (∀ m < u, (tm.runFrom c m).state ≠ none) ∧
          tm.runFrom c u = ⟨none, c.inputPos,
            js.foldl (fun w j => Function.update (Function.update w (j.castAdd k₀)
              fun _ => none) (j.addNat k₀) fun _ => none) c.workTapes,
            js.foldl (fun wp j => Function.update (Function.update wp (j.castAdd k₀) 0)
              (j.addNat k₀) 0) c.workTapePos,
            c.output⟩ ∧
          tm.spaceUsed c u ≤
            (js.map fun j => 2 * (R j - L j).toNat + 4 + (k₀ + k₀)).sum + (k₀ + k₀) := by
  induction js with
  | nil =>
    refine ⟨Unit, inferInstance, haltTM (k₀ + k₀), fun input c L R P hq _ => ?_⟩
    obtain ⟨hrun, hsp⟩ := haltTM_run c hq
    refine ⟨1, by simp, fun m hm => ?_, ?_, by simpa using hsp⟩
    · obtain rfl : m = 0 := by omega
      rw [runFrom_zero, hq]
      simp
    · rw [hrun]
      rfl
  | cons j rest ih =>
    obtain ⟨hjr, hndr⟩ := List.nodup_cons.mp hnd
    obtain ⟨Sr, hSr, tmr, hr⟩ := ih hndr
    have hne : j.castAdd k₀ ≠ j.addNat k₀ := by
      refine Fin.ne_of_val_ne ?_
      simp only [Fin.val_castAdd, Fin.val_addNat]
      omega
    obtain ⟨Ss, hSs, tms, hs⟩ := exists_sweepPair (j.castAdd k₀) (j.addNat k₀) hne
    haveI := hSr
    haveI := hSs
    refine ⟨Ss ⊕ Sr, inferInstance, tms.seq tmr, fun input c L R P hq hpairs => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpairs j (List.mem_cons_self)
    -- run the sweep for the first pair
    obtain ⟨u₁, hu₁, hact₁, hrun₁, hsp₁⟩ := hs input (c.withState (some tms.q₀))
      (L j) (R j) (P j) rfl h1 h2 h3 h4 h5 h6 h7 h8
    -- the rest of the pairs are untouched by the first sweep
    have hrest : ∀ j' ∈ rest, L j' ≤ 0 ∧ 0 ≤ R j' ∧ L j' ≤ P j' ∧ P j' ≤ R j' ∧
        (⟨some tmr.q₀, c.inputPos,
          Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
            (j.addNat k₀) fun _ => none,
          Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0,
          c.output⟩ : Cfg (k₀ + k₀) Bool Sr input).workTapePos (j'.castAdd k₀) = P j' ∧
        (⟨some tmr.q₀, c.inputPos,
          Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
            (j.addNat k₀) fun _ => none,
          Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0,
          c.output⟩ : Cfg (k₀ + k₀) Bool Sr input).workTapePos (j'.addNat k₀) = P j' ∧
        (∀ z, (⟨some tmr.q₀, c.inputPos,
          Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
            (j.addNat k₀) fun _ => none,
          Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0,
          c.output⟩ : Cfg (k₀ + k₀) Bool Sr input).workTapes (j'.addNat k₀) z =
          if z = 0 then some true
          else if L j' ≤ z ∧ z ≤ R j' then some false else none) ∧
        (∀ z, z < L j' ∨ R j' < z →
          (⟨some tmr.q₀, c.inputPos,
            Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
              (j.addNat k₀) fun _ => none,
            Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0,
            c.output⟩ : Cfg (k₀ + k₀) Bool Sr input).workTapes (j'.castAdd k₀) z = none) := by
      intro j' hj'
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hpairs j' (List.mem_cons_of_mem _ hj')
      obtain ⟨n1, n2, n3, n4⟩ := pair_ne (j := j) (j' := j') (by rintro rfl; exact hjr hj')
      refine ⟨g1, g2, g3, g4, ?_, ?_, fun z => ?_, fun z hz => ?_⟩
      · rw [show (⟨some tmr.q₀, c.inputPos, _, _, c.output⟩ : Cfg (k₀ + k₀) Bool Sr
            input).workTapePos (j'.castAdd k₀) =
          (Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0)
            (j'.castAdd k₀) from rfl,
          Function.update_of_ne n2, Function.update_of_ne n1]
        exact g5
      · rw [show (⟨some tmr.q₀, c.inputPos, _, _, c.output⟩ : Cfg (k₀ + k₀) Bool Sr
            input).workTapePos (j'.addNat k₀) =
          (Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0)
            (j'.addNat k₀) from rfl,
          Function.update_of_ne n4, Function.update_of_ne n3]
        exact g6
      · rw [show (⟨some tmr.q₀, c.inputPos, _, _, c.output⟩ : Cfg (k₀ + k₀) Bool Sr
            input).workTapes (j'.addNat k₀) =
          (Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
            (j.addNat k₀) fun _ => none) (j'.addNat k₀) from rfl,
          Function.update_of_ne n4, Function.update_of_ne n3]
        exact g7 z
      · rw [show (⟨some tmr.q₀, c.inputPos, _, _, c.output⟩ : Cfg (k₀ + k₀) Bool Sr
            input).workTapes (j'.castAdd k₀) =
          (Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
            (j.addNat k₀) fun _ => none) (j'.castAdd k₀) from rfl,
          Function.update_of_ne n2, Function.update_of_ne n1]
        exact g8 z hz
    obtain ⟨u₂, hu₂, hact₂, hrun₂, hsp₂⟩ :=
      hr input ⟨some tmr.q₀, c.inputPos,
        Function.update (Function.update c.workTapes (j.castAdd k₀) fun _ => none)
          (j.addNat k₀) fun _ => none,
        Function.update (Function.update c.workTapePos (j.castAdd k₀) 0) (j.addNat k₀) 0,
        c.output⟩ L R P rfl hrest
    -- glue the two runs
    obtain ⟨hrunC, hactC, hspC⟩ := seq_spec (c := c) hq hrun₁ rfl hact₁ hsp₁
      hrun₂ rfl hact₂ hsp₂
    refine ⟨u₁ + u₂, ?_, hactC, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · rw [hrunC]
      rfl
    · refine le_trans hspC ?_
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Evaluating a fold of pairwise updates: a tape in one of the listed pairs got the new value,
any other keeps its old one. -/
private lemma foldl_update_pair_eval {γ : Type*} {k₀ : ℕ} (js : List (Fin k₀)) (b : γ)
    (w : Fin (k₀ + k₀) → γ) (l : Fin (k₀ + k₀)) :
    js.foldl (fun w' j => Function.update (Function.update w' (j.castAdd k₀) b)
      (j.addNat k₀) b) w l =
      if ∃ j ∈ js, l = j.castAdd k₀ ∨ l = j.addNat k₀ then b else w l := by
  induction js generalizing w with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih]
    by_cases hmem : ∃ j' ∈ rest, l = j'.castAdd k₀ ∨ l = j'.addNat k₀
    · rw [ite_eq_left hmem, ite_eq_left ?_]
      obtain ⟨j', hj', hl⟩ := hmem
      exact ⟨j', List.mem_cons_of_mem _ hj', hl⟩
    · rw [ite_eq_right hmem]
      by_cases h1 : l = j.addNat k₀
      · subst h1
        rw [Function.update_self, ite_eq_left ⟨j, List.mem_cons_self, Or.inr rfl⟩]
      · rw [Function.update_of_ne h1]
        by_cases h2 : l = j.castAdd k₀
        · subst h2
          rw [Function.update_self, ite_eq_left ⟨j, List.mem_cons_self, Or.inl rfl⟩]
        · rw [Function.update_of_ne h2, ite_eq_right ?_]
          rintro ⟨j', hj', hl⟩
          rcases List.mem_cons.mp hj' with rfl | hj'
          · exact hl.elim h2 h1
          · exact hmem ⟨j', hj', hl⟩

/-- Every tape belongs to one of the pairs. -/
private lemma exists_pair_mem {k₀ : ℕ} (l : Fin (k₀ + k₀)) :
    ∃ j ∈ List.finRange k₀, l = j.castAdd k₀ ∨ l = j.addNat k₀ := by
  induction l using Fin.addCases with
  | left j => exact ⟨j, List.mem_finRange j, Or.inl rfl⟩
  | right j => exact ⟨j, List.mem_finRange j, Or.inr (by rw [Fin.natAdd_eq_addNat])⟩

end SweepChain

set_option linter.style.haveILetI false in
/-- **The tidy normal form theorem.** Every computable function has a tidy machine, at a
constant-factor cost in time and space: anchor the footprints, run the instrumented machine,
mark the final head positions, rewind the input head, and sweep every pair clean. -/
public theorem exists_tidy {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ (c k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      TidyComputes tm encIn encOut f
        (fun a => c * (t a + 1)) (fun a => c * (s a + 1) + k) := by
  classical
  obtain ⟨k₀, State₀, hfin₀, tm₀, hfun⟩ := h
  obtain ⟨SA, hSA, tmA, hA⟩ := exists_markAnchors k₀ Bool true
  obtain ⟨SC, hSC, tmC, hC⟩ := exists_markCurrent k₀ Bool false
  obtain ⟨SD, hSD, tmD, hD⟩ := exists_rewindInput (k₀ + k₀) Bool
  obtain ⟨SE, hSE, tmE, hE⟩ := exists_sweepChain k₀ (List.finRange k₀) (List.nodup_finRange k₀)
  haveI := hfin₀; haveI := hSA; haveI := hSC; haveI := hSD; haveI := hSE
  refine ⟨20 * (k₀ + 1) * (k₀ + 1), k₀ + k₀,
    SA ⊕ (State₀ ⊕ (SC ⊕ (SD ⊕ SE))), inferInstance,
    tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE))), fun a => ?_⟩
  -- the run of the original machine, at its first halting time
  obtain ⟨t', ht', s', hs', hhalt', hout', hspace'⟩ := hfun a
  obtain ⟨u₀, hu₀, hhalt₀, hact₀⟩ :=
    exists_minimal_halting_time tm₀ (tm₀.initCfg (encIn a)) t' hhalt'
  have hout₀ : (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).output = encOut (f a) := by
    rw [← runFrom_eq_of_halt tm₀ (tm₀.initCfg (encIn a)) hu₀ hhalt₀]
    exact hout'
  have hsp₀ : tm₀.spaceUsed (tm₀.initCfg (encIn a)) u₀ ≤ s a := by
    have hm : tm₀.spaceUsed (tm₀.initCfg (encIn a)) u₀ ≤
        tm₀.spaceUsed (tm₀.initCfg (encIn a)) t' :=
      spaceUsed_mono tm₀ (tm₀.initCfg (encIn a)) hu₀
    omega
  -- the visited interval and final head position of each tape
  choose L R hL0 h0R hIcc using
    fun j => exists_visitedByTapeHead_eq_Icc (tm := tm₀) (tm₀.initCfg (encIn a)) u₀ j
  set P : Fin k₀ → ℤ := fun j => (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).workTapePos j with hP
  have hPmem : ∀ j, L j ≤ P j ∧ P j ≤ R j := by
    intro j
    have hmem := tm₀.mem_visitedByTapeHead_self (tm₀.initCfg (encIn a)) u₀ j
    rw [hIcc j] at hmem
    exact Finset.mem_Icc.mp hmem
  have hGconf : ∀ j z, z < L j ∨ R j < z →
      (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).workTapes j z = none := by
    intro j z hz
    by_contra hne
    have hmem : z ∈ tm₀.visitedByTapeHead (tm₀.initCfg (encIn a)) u₀ j :=
      tm₀.mem_visitedByTapeHead_of_workTapes_ne j u₀ z hne
    rw [hIcc j] at hmem
    have := Finset.mem_Icc.mp hmem
    omega
  -- phase A: place the anchors
  obtain ⟨eAstate, eAip, eAout, eApos, eAcast, eAanchor⟩ := hA (encIn a)
    (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
      (encIn a)).withState (some tmA.q₀)) rfl
  -- the interval data, in usable form
  have hL0' : ∀ j, L j ≤ 0 := fun j => by simpa [Cfg.init] using hL0 j
  have h0R' : ∀ j, 0 ≤ R j := fun j => by simpa [Cfg.init] using h0R j
  -- phases D and E, from any configuration with the right fields
  have hDE : ∀ (c : Cfg (k₀ + k₀) Bool (SD ⊕ SE) (encIn a)),
      c.state = some (tmD.seq tmE).q₀ →
      c.inputPos.val ≤ u₀ + 1 →
      c.output = encOut (f a) →
      (∀ j, c.workTapes (j.castAdd k₀) = (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).workTapes j) →
      (∀ j z, c.workTapes (j.addNat k₀) z = if z = 0 then some true
        else if L j ≤ z ∧ z ≤ R j then some false else none) →
      (∀ j, c.workTapePos (j.castAdd k₀) = P j) →
      (∀ j, c.workTapePos (j.addNat k₀) = P j) →
      ∃ u ≤ (u₀ + 3) +
          (((List.finRange k₀).map fun j => 4 * (R j - L j).toNat + 8).sum + 1),
        (tmD.seq tmE).runFrom c u = wordsCfg (encIn a) none (fun _ => []) (encOut (f a)) ∧
        (∀ m < u, ((tmD.seq tmE).runFrom c m).state ≠ none) ∧
        (tmD.seq tmE).spaceUsed c u ≤ (k₀ + k₀) +
          ((((List.finRange k₀).map fun j =>
            2 * (R j - L j).toNat + 4 + (k₀ + k₀)).sum) + (k₀ + k₀)) := by
    intro c hstate hip hout hcast hfp hposc hposn
    -- rewind the input head
    obtain ⟨uD, huD, hactD, hrunD, hframeD⟩ := hD (encIn a) (c.withState (some tmD.q₀)) rfl
    -- sweep every pair
    have hpairsE : ∀ j ∈ List.finRange k₀, L j ≤ 0 ∧ 0 ≤ R j ∧ L j ≤ P j ∧ P j ≤ R j ∧
        ((⟨none, 1, (c.withState (some tmD.q₀)).workTapes,
            (c.withState (some tmD.q₀)).workTapePos, (c.withState (some tmD.q₀)).output⟩ :
          Cfg (k₀ + k₀) Bool SD (encIn a)).withState
            (some tmE.q₀)).workTapePos (j.castAdd k₀) = P j ∧
        ((⟨none, 1, (c.withState (some tmD.q₀)).workTapes,
            (c.withState (some tmD.q₀)).workTapePos, (c.withState (some tmD.q₀)).output⟩ :
          Cfg (k₀ + k₀) Bool SD (encIn a)).withState
            (some tmE.q₀)).workTapePos (j.addNat k₀) = P j ∧
        (∀ z, ((⟨none, 1, (c.withState (some tmD.q₀)).workTapes,
            (c.withState (some tmD.q₀)).workTapePos, (c.withState (some tmD.q₀)).output⟩ :
          Cfg (k₀ + k₀) Bool SD (encIn a)).withState
            (some tmE.q₀)).workTapes (j.addNat k₀) z = if z = 0 then some true
          else if L j ≤ z ∧ z ≤ R j then some false else none) ∧
        (∀ z, z < L j ∨ R j < z → ((⟨none, 1, (c.withState (some tmD.q₀)).workTapes,
            (c.withState (some tmD.q₀)).workTapePos, (c.withState (some tmD.q₀)).output⟩ :
          Cfg (k₀ + k₀) Bool SD (encIn a)).withState
            (some tmE.q₀)).workTapes (j.castAdd k₀) z = none) := by
      intro j _
      refine ⟨hL0' j, h0R' j, (hPmem j).1, (hPmem j).2, hposc j, hposn j, fun z => hfp j z,
        fun z hz => ?_⟩
      rw [show ((⟨none, 1, (c.withState (some tmD.q₀)).workTapes,
          (c.withState (some tmD.q₀)).workTapePos, (c.withState (some tmD.q₀)).output⟩ :
        Cfg (k₀ + k₀) Bool SD (encIn a)).withState
          (some tmE.q₀)).workTapes (j.castAdd k₀) = c.workTapes (j.castAdd k₀) from rfl,
        hcast j]
      exact hGconf j z hz
    obtain ⟨uE, huE, hactE, hrunE, hspE⟩ := hE (encIn a)
      ((⟨none, 1, (c.withState (some tmD.q₀)).workTapes,
          (c.withState (some tmD.q₀)).workTapePos, (c.withState (some tmD.q₀)).output⟩ :
        Cfg (k₀ + k₀) Bool SD (encIn a)).withState (some tmE.q₀)) L R P rfl hpairsE
    -- glue the two phases
    obtain ⟨hrunC, hactC, hspC⟩ := seq_spec hstate hrunD rfl hactD
      (spaceUsed_le_of_workTapePos_const _ _ fun m hm => (hframeD m hm).2.1)
      hrunE rfl hactE hspE
    have huD' : uD ≤ c.inputPos.val + 2 := by simpa using huD
    refine ⟨uD + uE, by omega, ?_, hactC, le_trans hspC (by omega)⟩
    rw [hrunC]
    -- the swept configuration is the tidy one
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext l
      exact ((foldl_update_pair_eval (List.finRange k₀) (fun _ => none)
        ((c.withState (some tmD.q₀)).workTapes) l).trans
          (by rw [ite_eq_left (exists_pair_mem l)])).trans tapeOfList_nil.symm
    · funext l
      exact (foldl_update_pair_eval (List.finRange k₀) 0
        ((c.withState (some tmD.q₀)).workTapePos) l).trans
          (by rw [ite_eq_left (exists_pair_mem l)]; rfl)
    · exact hout
  -- the marks laid down before the final step, together with the final position, are the interval
  have hmarksIccT : ∀ (j : Fin k₀) (z : ℤ),
      ((z ∈ (Finset.range u₀).image
          (fun m => (tm₀.runFrom (tm₀.initCfg (encIn a)) m).workTapePos j)) ∨ z = P j) ↔
        (L j ≤ z ∧ z ≤ R j) := by
    intro j z
    rw [show (L j ≤ z ∧ z ≤ R j) ↔ z ∈ Finset.Icc (L j) (R j) from (Finset.mem_Icc).symm,
      ← hIcc j, mem_visitedByTapeHead]
    constructor
    · rintro (hz | rfl)
      · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨m, by have := Finset.mem_range.mp hm; omega, rfl⟩
      · exact ⟨u₀, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_or_ge m u₀ with hlt | hge
      · exact Or.inl (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hlt, rfl⟩)
      · right
        rw [show m = u₀ from by omega]
  -- phases C, D and E: mark the final positions, then rewind and sweep
  have hCDE : ∀ (c : Cfg (k₀ + k₀) Bool (SC ⊕ (SD ⊕ SE)) (encIn a)),
      c.state = some (tmC.seq (tmD.seq tmE)).q₀ →
      c.inputPos.val ≤ u₀ + 1 →
      c.output = encOut (f a) →
      (∀ j, c.workTapes (j.castAdd k₀) = (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).workTapes j) →
      (∀ j z, c.workTapes (j.addNat k₀) z = if z = 0 then some true
        else if z ∈ (Finset.range u₀).image
          (fun m => (tm₀.runFrom (tm₀.initCfg (encIn a)) m).workTapePos j) then some false
        else none) →
      (∀ j, c.workTapePos (j.castAdd k₀) = P j) →
      (∀ j, c.workTapePos (j.addNat k₀) = P j) →
      ∃ u ≤ 1 + ((u₀ + 3) +
          (((List.finRange k₀).map fun j => 4 * (R j - L j).toNat + 8).sum + 1)),
        (tmC.seq (tmD.seq tmE)).runFrom c u =
          wordsCfg (encIn a) none (fun _ => []) (encOut (f a)) ∧
        (∀ m < u, ((tmC.seq (tmD.seq tmE)).runFrom c m).state ≠ none) ∧
        (tmC.seq (tmD.seq tmE)).spaceUsed c u ≤ (k₀ + k₀) + ((k₀ + k₀) +
          ((((List.finRange k₀).map fun j =>
            2 * (R j - L j).toNat + 4 + (k₀ + k₀)).sum) + (k₀ + k₀))) := by
    intro c hstate hip hout hcast hfp hposc hposn
    obtain ⟨eCstate, eCip, eCout, eCpos, eCcast, eCmark⟩ :=
      hC (encIn a) (c.withState (some tmC.q₀)) rfl
    -- after the mark, the footprints are exactly the intervals
    have hfpC : ∀ (j : Fin k₀) (z : ℤ),
        (tmC.runFrom (c.withState (some tmC.q₀)) 1).workTapes (j.addNat k₀) z =
          if z = 0 then some true
          else if L j ≤ z ∧ z ≤ R j then some false else none := by
      intro j z
      have hthis := congrFun (eCmark j) z
      simp only [Cfg.withState_workTapes, Cfg.withState_workTapePos] at hthis
      rw [hposn j, hfp j z, hfp j (P j)] at hthis
      rw [hthis]
      by_cases hz : z = 0
      · subst hz
        simp
      · simp only [ite_eq_right hz]
        by_cases hmem : z ∈ (Finset.range u₀).image
            (fun m => (tm₀.runFrom (tm₀.initCfg (encIn a)) m).workTapePos j)
        · rw [ite_eq_left hmem, ite_eq_left ((hmarksIccT j z).mp (Or.inl hmem))]
        · rw [ite_eq_right hmem]
          by_cases hzP : z = P j
          · subst hzP
            rw [ite_eq_right hz, ite_eq_right hmem, ite_eq_left ⟨rfl, rfl⟩,
              ite_eq_left ((hmarksIccT j (P j)).mp (Or.inr rfl))]
          · have hnot : ¬ (L j ≤ z ∧ z ≤ R j) := by
              intro hin
              rcases (hmarksIccT j z).mpr hin with hm | hm
              · exact hmem hm
              · exact hzP hm
            rw [ite_eq_right hnot, ite_eq_right (fun hcond => hzP hcond.1)]
    -- hand over to the rewind and the sweeps
    obtain ⟨u₂, hu₂, hrun₂, hact₂, hsp₂⟩ := hDE
      ((tmC.runFrom (c.withState (some tmC.q₀)) 1).withState (some (tmD.seq tmE).q₀))
      rfl
      ((by
        rw [eCip]
        simpa using hip) :
        ((tmC.runFrom (c.withState (some tmC.q₀)) 1).inputPos : ℕ) ≤ u₀ + 1)
      ((by
        rw [eCout]
        simpa using hout) :
        (tmC.runFrom (c.withState (some tmC.q₀)) 1).output = encOut (f a))
      (fun j => (eCcast j).trans (hcast j))
      (fun j z => hfpC j z)
      (fun j => ((by
        rw [eCpos]
        simpa using hposc j) :
        (tmC.runFrom (c.withState (some tmC.q₀)) 1).workTapePos (j.castAdd k₀) = P j))
      (fun j => ((by
        rw [eCpos]
        simpa using hposn j) :
        (tmC.runFrom (c.withState (some tmC.q₀)) 1).workTapePos (j.addNat k₀) = P j))
    obtain ⟨hrunG, hactG, hspG⟩ := seq_spec hstate rfl eCstate
      (fun m hm => by
        obtain rfl : m = 0 := by omega
        rw [runFrom_zero]
        simp)
      (spaceUsed_le_of_workTapePos_const _ _ fun m hm => by
        rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
        · rw [runFrom_zero]
        · exact eCpos)
      hrun₂ rfl hact₂ hsp₂
    refine ⟨1 + u₂, by omega, ?_, hactG, le_trans hspG (by omega)⟩
    rw [hrunG]
    rfl
  -- phases B to E: the instrumented run, then the cleanup
  have hBCDE : ∀ (c : Cfg (k₀ + k₀) Bool (State₀ ⊕ (SC ⊕ (SD ⊕ SE))) (encIn a)),
      c.state = some ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE))).q₀ →
      c.inputPos = 1 →
      (∀ j : Fin k₀, c.workTapes (j.castAdd k₀) = fun _ => none) →
      (∀ (j : Fin k₀) (z : ℤ), c.workTapes (j.addNat k₀) z =
        if z = 0 then some true else none) →
      (∀ l, c.workTapePos l = 0) →
      c.output = [] →
      ∃ u ≤ u₀ + (1 + ((u₀ + 3) +
          (((List.finRange k₀).map fun j => 4 * (R j - L j).toNat + 8).sum + 1))),
        ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE))).runFrom c u =
          wordsCfg (encIn a) none (fun _ => []) (encOut (f a)) ∧
        (∀ m < u, (((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE))).runFrom c m).state ≠
          none) ∧
        ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE))).spaceUsed c u ≤
          2 * s a + ((k₀ + k₀) + ((k₀ + k₀) +
            ((((List.finRange k₀).map fun j =>
              2 * (R j - L j).toNat + 4 + (k₀ + k₀)).sum) + (k₀ + k₀)))) := by
    intro c hstate hip hcastB hanchorB hposB houtB
    -- the instrumented start projects to the original start
    have hproj : projCfg (c.withState (some tm₀.q₀)) = tm₀.initCfg (encIn a) := by
      refine Cfg.ext rfl ?_ ?_ ?_ ?_
      · simpa using hip
      · funext j z
        simpa using congrFun (hcastB j) z
      · funext j
        simpa using hposB (j.castAdd k₀)
      · simpa using houtB
    have hmirror : ∀ m, tm₀.runFrom (tm₀.initCfg (encIn a)) m =
        projCfg ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) m) := by
      intro m
      rw [← hproj]
      exact runFrom_projCfg tm₀ false (c.withState (some tm₀.q₀)) m
    have hstateB : ∀ m, ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) m).state =
        (tm₀.runFrom (tm₀.initCfg (encIn a)) m).state := by
      intro m
      rw [hmirror m]
      rfl
    have hactB : ∀ m < u₀,
        ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) m).state ≠ none := by
      intro m hm
      rw [hstateB]
      exact hact₀ m hm
    have hhaltB : ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).state =
        none := by
      rw [hstateB]
      exact hhalt₀
    have halignB : ∀ j : Fin k₀, (c.withState (some tm₀.q₀)).workTapePos (j.addNat k₀) =
        (c.withState (some tm₀.q₀)).workTapePos (j.castAdd k₀) := by
      intro j
      have h1 := hposB (j.addNat k₀)
      have h2 := hposB (j.castAdd k₀)
      simp only [Cfg.withState_workTapePos]
      omega
    -- hand over to the marking, the rewind and the sweeps
    obtain ⟨u₂, hu₂, hrun₂, hact₂, hsp₂⟩ := hCDE
      (((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).withState
        (some (tmC.seq (tmD.seq tmE)).q₀))
      rfl
      ((by
        rw [show ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).inputPos =
          (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).inputPos from by rw [hmirror u₀]; rfl]
        have h := inputPos_runFrom_le tm₀ (tm₀.initCfg (encIn a)) u₀
        have h2 : ((tm₀.initCfg (encIn a)).inputPos : ℕ) = 1 := rfl
        omega) :
        (((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).inputPos : ℕ) ≤
          u₀ + 1)
      ((by
        rw [show ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).output =
          (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).output from by rw [hmirror u₀]; rfl]
        exact hout₀) :
        ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).output = encOut (f a))
      (fun j => ((by rw [hmirror u₀]; rfl) :
        ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).workTapes
          (j.castAdd k₀) = (tm₀.runFrom (tm₀.initCfg (encIn a)) u₀).workTapes j))
      (fun j z => ((by
        rw [congrFun (workTapes_addNat_instrument (c.withState (some tm₀.q₀)) j (halignB j)
          u₀ hactB) z]
        rw [show (c.withState (some tm₀.q₀)).workTapes (j.addNat k₀) z =
          c.workTapes (j.addNat k₀) z from rfl, hanchorB j z]
        have himg : (Finset.range u₀).image
            (fun m => ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀))
              m).workTapePos (j.castAdd k₀)) =
            (Finset.range u₀).image
              (fun m => (tm₀.runFrom (tm₀.initCfg (encIn a)) m).workTapePos j) := by
          refine Finset.image_congr fun m _ => ?_
          rw [hmirror m]
          rfl
        rw [himg]
        by_cases hz : z = 0
        · subst hz
          simp
        · simp only [ite_eq_right hz]) :
        ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).workTapes
          (j.addNat k₀) z = if z = 0 then some true
          else if z ∈ (Finset.range u₀).image
            (fun m => (tm₀.runFrom (tm₀.initCfg (encIn a)) m).workTapePos j) then some false
          else none))
      (fun j => ((by
        simp only [hP]
        rw [hmirror u₀]
        rfl) :
        ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).workTapePos
          (j.castAdd k₀) = P j))
      (fun j => ((by
        rw [workTapePos_addNat_instrument (c.withState (some tm₀.q₀)) j (halignB j) u₀ hactB]
        simp only [hP]
        rw [hmirror u₀]
        rfl) :
        ((tm₀.instrument false).runFrom (c.withState (some tm₀.q₀)) u₀).workTapePos
          (j.addNat k₀) = P j))
    have hspB : (tm₀.instrument false).spaceUsed (c.withState (some tm₀.q₀)) u₀ ≤ 2 * s a := by
      rw [spaceUsed_instrument tm₀ false (c.withState (some tm₀.q₀)) u₀ halignB hactB, hproj]
      omega
    obtain ⟨hrunG, hactG, hspG⟩ := seq_spec hstate rfl hhaltB hactB hspB hrun₂
      rfl hact₂ hsp₂
    refine ⟨u₀ + u₂, by omega, ?_, hactG, le_trans hspG (by omega)⟩
    rw [hrunG]
    rfl
  -- the interval sums, bounded by the original machine's space
  have hcard : ∀ j, (R j - L j).toNat + 1 =
      tm₀.spaceUsedByTape (tm₀.initCfg (encIn a)) u₀ j := by
    intro j
    rw [spaceUsedByTape, hIcc j, Int.card_Icc]
    have h1 := hL0' j
    have h2 := h0R' j
    omega
  have hsumX : (∑ j : Fin k₀, (R j - L j).toNat) + k₀ =
      tm₀.spaceUsed (tm₀.initCfg (encIn a)) u₀ := by
    have h1 : (∑ j : Fin k₀, ((R j - L j).toNat + 1)) =
        tm₀.spaceUsed (tm₀.initCfg (encIn a)) u₀ :=
      Finset.sum_congr rfl fun j _ => hcard j
    rw [Finset.sum_add_distrib] at h1
    simpa using h1
  have hsX_s : (∑ j : Fin k₀, (R j - L j).toNat) ≤ s a := by omega
  have hsX_t : (∑ j : Fin k₀, (R j - L j).toNat) ≤ k₀ * u₀ := by
    have hlin := spaceUsed_linear (tm := tm₀) (tm₀.initCfg (encIn a)) u₀
    omega
  have hs4 : ((List.finRange k₀).map fun j => 4 * (R j - L j).toNat + 8).sum =
      4 * (∑ j : Fin k₀, (R j - L j).toNat) + 8 * k₀ := by
    rw [← Fin.sum_univ_def, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_comm]
  have hs2 : ((List.finRange k₀).map fun j => 2 * (R j - L j).toNat + 4 + (k₀ + k₀)).sum =
      2 * (∑ j : Fin k₀, (R j - L j).toNat) + (4 + (k₀ + k₀)) * k₀ := by
    rw [← Fin.sum_univ_def,
      show (fun j : Fin k₀ => 2 * (R j - L j).toNat + 4 + (k₀ + k₀)) =
        (fun j => 2 * (R j - L j).toNat + (4 + (k₀ + k₀))) from funext fun j => by omega,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_comm]
  -- discharge phase A and glue at the top
  obtain ⟨u₂, hu₂, hrun₂, hact₂, hsp₂⟩ := hBCDE
    ((tmA.runFrom (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
        (encIn a)).withState (some tmA.q₀)) 1).withState
      (some ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE))).q₀))
    rfl
    ((by rw [eAip]; rfl) :
      (tmA.runFrom (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
        (encIn a)).withState (some tmA.q₀)) 1).inputPos = 1)
    (fun j => (eAcast j :
      (tmA.runFrom (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
        (encIn a)).withState (some tmA.q₀)) 1).workTapes (j.castAdd k₀) = fun _ => none))
    (fun j z => ((by
      rw [congrFun (eAanchor j) z,
        show (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
          (encIn a)).withState (some tmA.q₀)).workTapePos (j.addNat k₀) = (0 : ℤ) from rfl]
      by_cases hz : z = 0
      · subst hz
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hz, ite_eq_right hz]
        rfl) :
      (tmA.runFrom (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
        (encIn a)).withState (some tmA.q₀)) 1).workTapes (j.addNat k₀) z =
        if z = 0 then some true else none))
    (fun l => (congrFun eApos l :
      (tmA.runFrom (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
        (encIn a)).withState (some tmA.q₀)) 1).workTapePos l = 0))
    (eAout :
      (tmA.runFrom (((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg
        (encIn a)).withState (some tmA.q₀)) 1).output = [])
  obtain ⟨hrunT, hactT, hspT⟩ := seq_spec
    (c := (tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg (encIn a))
    rfl rfl eAstate
    (fun m hm => by
      obtain rfl : m = 0 := by omega
      rw [runFrom_zero]
      simp)
    (spaceUsed_le_of_workTapePos_const _ _ fun m hm => by
      rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
      · rw [runFrom_zero]
      · exact eApos)
    hrun₂ rfl hact₂ hsp₂
  -- assemble the run and the bounds
  have hkk : k₀ ≤ (k₀ + 1) * (k₀ + 1) := by
    have h := Nat.le_mul_of_pos_left (k₀ + 1) (show 0 < k₀ + 1 by omega)
    omega
  have hM : ∀ v x : ℕ, (x ≤ k₀ * v ∨ x ≤ v ∨ x ≤ k₀ * k₀ ∨ x ≤ k₀ ∨ x ≤ 1) →
      x ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) := by
    intro v x hx
    have h1 : k₀ * v ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) := Nat.mul_le_mul hkk (by omega)
    have h2 : v + 1 ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) :=
      Nat.le_mul_of_pos_left (v + 1) (Nat.mul_pos (by omega) (by omega))
    have h3 : k₀ * k₀ ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) := by
      have ha : k₀ * k₀ ≤ (k₀ + 1) * (k₀ + 1) := Nat.mul_le_mul (by omega) (by omega)
      have hb : (k₀ + 1) * (k₀ + 1) ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h4 : k₀ ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) := by
      have hb : (k₀ + 1) * (k₀ + 1) ≤ (k₀ + 1) * (k₀ + 1) * (v + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega
  refine ⟨1 + u₂, ?_, ?_, ?_⟩
  · -- the time bound
    change 1 + u₂ ≤ 20 * (k₀ + 1) * (k₀ + 1) * (t a + 1)
    rw [hs4] at hu₂
    have hb : 1 + u₂ ≤ 4 * (k₀ * u₀) + (2 * u₀ + (8 * k₀ + 6)) := by omega
    have m1 := hM u₀ (k₀ * u₀) (Or.inl le_rfl)
    have m2 := hM u₀ u₀ (Or.inr (Or.inl le_rfl))
    have m3 := hM u₀ k₀ (Or.inr (Or.inr (Or.inr (Or.inl le_rfl))))
    have m4 := hM u₀ 1 (Or.inr (Or.inr (Or.inr (Or.inr le_rfl))))
    have hbig : 1 + u₂ ≤ 20 * ((k₀ + 1) * (k₀ + 1) * (u₀ + 1)) := by omega
    have hmono : 20 * ((k₀ + 1) * (k₀ + 1) * (u₀ + 1)) ≤
        20 * ((k₀ + 1) * (k₀ + 1) * (t a + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    calc 1 + u₂ ≤ 20 * ((k₀ + 1) * (k₀ + 1) * (u₀ + 1)) := hbig
      _ ≤ 20 * ((k₀ + 1) * (k₀ + 1) * (t a + 1)) := hmono
      _ = 20 * (k₀ + 1) * (k₀ + 1) * (t a + 1) := by rw [← mul_assoc, ← mul_assoc]
  · -- the halting configuration
    rw [hrunT]
    rfl
  · -- the space bound
    change (tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).spaceUsed
      ((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg (encIn a))
      (1 + u₂) ≤ 20 * (k₀ + 1) * (k₀ + 1) * (s a + 1) + (k₀ + k₀)
    have hs2' : ((List.finRange k₀).map fun j =>
        2 * (R j - L j).toNat + 4 + (k₀ + k₀)).sum =
        2 * (∑ j : Fin k₀, (R j - L j).toNat) + (4 * k₀ + (k₀ * k₀ + k₀ * k₀)) := by
      rw [hs2, Nat.add_mul, Nat.add_mul]
    rw [hs2'] at hspT
    have m1 := hM (s a) (s a) (Or.inr (Or.inl le_rfl))
    have m2 := hM (s a) (k₀ * k₀) (Or.inr (Or.inr (Or.inl le_rfl)))
    have m3 := hM (s a) k₀ (Or.inr (Or.inr (Or.inr (Or.inl le_rfl))))
    have hbig : (tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).spaceUsed
        ((tmA.seq ((tm₀.instrument false).seq (tmC.seq (tmD.seq tmE)))).initCfg (encIn a))
        (1 + u₂) ≤ 20 * ((k₀ + 1) * (k₀ + 1) * (s a + 1)) := by omega
    calc _ ≤ 20 * ((k₀ + 1) * (k₀ + 1) * (s a + 1)) := hbig
      _ ≤ 20 * (k₀ + 1) * (k₀ + 1) * (s a + 1) + (k₀ + k₀) := by
        rw [← mul_assoc, ← mul_assoc]
        omega


end Assembly



end Turing.MultiTapeTM
