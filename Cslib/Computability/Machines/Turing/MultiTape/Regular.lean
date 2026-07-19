/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Computability.DFA

/-!
# Regular languages are decidable in linear time and zero space

This file connects the notion of a regular language (as defined in Mathlib via a deterministic
finite automaton with finitely many states, `Language.IsRegular`) with the complexity classes of
multi-tape Turing machines defined in `Cslib.Computability.Machines.Turing.MultiTape.Deterministic`.

The main result states that every regular language over a *finite* alphabet is decidable by a
multi-tape Turing machine *without work tapes* (`k = 0`). Such a machine uses zero space (by
`MultiTapeTM.spaceUsed_zero_tapes_eq_zero`) and only needs to sweep once over the input, so it
decides the language within `n + 2` steps.

This is the "regular ⇒ `DSPACE(1)`" direction of the characterisation mentioned in the design notes
of the multi-tape Turing machine file: with the "cells visited" space measure, `DSPACE(1)` is
exactly the class of regular languages.

A finite input alphabet (`Finite IOSymbol`) is necessary: a `k = 0` machine has a finite work
alphabet and finite state set, so it can only handle inputs over a finite alphabet.
-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

/-!
## Relabeling the state type

Relabeling only the state type of a Turing machine along an equivalence `State ≃ State'` does not
change its behaviour: the tapes, input and output are untouched, so the machine computes exactly the
same input/output pairs in the same time and space. This is straightforward because none of the
dependent structure of a configuration (the input tape and head position) mentions the state type.
-/

section CongrState

variable {k : ℕ} {Symbol State State' : Type*}

/-- Relabel the state of a configuration along `eState : State ↪ State'`. -/
def Cfg.congrState {input : List Symbol} (eState : State ↪ State')
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  { cfg with state := cfg.state.map eState }

/-- Relabel the state type of a Turing machine along an embedding `eState : State ↪ State'`.

Only a left inverse of `eState` is needed: every state reachable during a computation is an
`eState`-image (the start state is `eState tm.q₀` and successors are `eState`-images), so the value
of `Function.invFun eState` outside the range of `eState` is irrelevant. -/
noncomputable def congrState (eState : State ↪ State') (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol State' :=
  haveI : Nonempty State := ⟨tm.q₀⟩
  { q₀ := eState tm.q₀
    tr := fun q input work =>
      let o := tm.tr (Function.invFun eState q) input work
      { inputMove := o.inputMove
        workActions := o.workActions
        outS := o.outS
        q' := o.q'.map eState } }

/-- The step function commutes with state relabeling. -/
@[simp]
lemma step_congrState {input : List Symbol} (eState : State ↪ State')
    (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    (tm.congrState eState).step (cfg.congrState eState)
      = (tm.step cfg).congrState eState := by
  unfold step
  cases hs : cfg.state with
  | none => simp [Cfg.congrState, hs]
  | some q =>
    haveI : Nonempty State := ⟨tm.q₀⟩
    have hinv : Function.invFun eState (eState q) = q :=
      Function.leftInverse_invFun eState.injective q
    simp only [Cfg.congrState, hs, Option.map_some, congrState, hinv]
    rfl

/-- The configuration sequence commutes with state relabeling. -/
lemma configs_congrState {input : List Symbol} (eState : State ↪ State')
    (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.congrState eState).configs (cfg.congrState eState) t
      = (tm.configs cfg t).congrState eState := by
  unfold configs
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_congrState]

lemma initCfg_congrState (eState : State ↪ State') (tm : MultiTapeTM k Symbol State)
    (input : List Symbol) :
    (tm.congrState eState).initCfg input = (tm.initCfg input).congrState eState := by
  simp [initCfg, Cfg.congrState, congrState]

/-- Relabeling the state type of a Turing machine along an embedding preserves its computations:
`tm.congrState eState` computes the same input/output pairs in the same time and space as `tm`. -/
lemma computesInTimeAndSpace_congrState (eState : State ↪ State')
    (tm : MultiTapeTM k Symbol State) (input output : List Symbol) (t s : ℕ)
    (h : tm.ComputesInTimeAndSpace input output t s) :
    (tm.congrState eState).ComputesInTimeAndSpace input output t s := by
  obtain ⟨cfg, hstate, hout, hrel, hspace⟩ := h
  refine ⟨cfg.congrState eState, ?_, ?_, ?_, ?_⟩
  · simp [Cfg.congrState, hstate]
  · simpa [Cfg.congrState] using hout
  · rw [relatesInSteps_iff_configs_eq] at hrel ⊢
    rw [initCfg_congrState, configs_congrState, hrel]
  · rw [initCfg_congrState, ← hspace]
    unfold spaceUsed spaceUsedByTape
    simp only [configs_congrState]
    rfl

end CongrState

/-!
## Relabeling the symbol type

Relabeling the tape alphabet along an equivalence `Symbol ≃ Symbol'` transports a computation to
the relabeled input and output. Unlike state relabeling, this touches the dependent structure of a
configuration: the input head position lives in `Fin (input.length + 2)`, so mapping the input list
requires transporting the position along `List.length_map` via `Fin.cast`.
-/

section CongrSymbol

variable {k : ℕ} {Symbol Symbol' State : Type*}

def Cfg.congrSymbol {input : List Symbol} (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) : Cfg k Symbol' State (input.map eSym) where
  state := cfg.state
  inputPos := Fin.cast (by rw [List.length_map]) cfg.inputPos
  workTapes i z := (cfg.workTapes i z).map eSym
  workTapePos := cfg.workTapePos
  output := cfg.output.map eSym

def congrSymbol (eSym : Symbol ≃ Symbol') (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol' State where
  q₀ := tm.q₀
  tr q input work :=
    let o := tm.tr q (input.map eSym.symm) (fun i => (work i).map eSym.symm)
    { inputMove := o.inputMove
      workActions := fun i => ((o.workActions i).1.map (Option.map eSym), (o.workActions i).2)
      outS := o.outS.map eSym
      q' := o.q' }

variable {input : List Symbol}

@[simp] lemma Cfg.congrSymbol_state (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) :
    (cfg.congrSymbol eSym).state = cfg.state := rfl
@[simp] lemma Cfg.congrSymbol_output (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) :
    (cfg.congrSymbol eSym).output = cfg.output.map eSym := rfl
@[simp] lemma Cfg.congrSymbol_workTapePos (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) :
    (cfg.congrSymbol eSym).workTapePos = cfg.workTapePos := rfl
@[simp] lemma Cfg.congrSymbol_inputPos_val (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) :
    (cfg.congrSymbol eSym).inputPos.val = cfg.inputPos.val := rfl

@[simp] lemma Cfg.congrSymbol_inputSymbol (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) :
    (cfg.congrSymbol eSym).inputSymbol = cfg.inputSymbol.map eSym := by
  have hz : ((cfg.congrSymbol eSym).inputPos = 0) ↔ (cfg.inputPos = 0) := by
    simp only [Fin.ext_iff, Cfg.congrSymbol_inputPos_val, Fin.val_zero]
  have he : ((cfg.congrSymbol eSym).inputPos = (input.map eSym).length + 1)
      ↔ (cfg.inputPos = input.length + 1) := by
    simp only [Cfg.congrSymbol_inputPos_val, List.length_map]
  unfold Cfg.inputSymbol
  simp only [hz, he]
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp [Cfg.congrSymbol, List.getElem_map]

@[simp] lemma Cfg.congrSymbol_workTapeSymbols (eSym : Symbol ≃ Symbol')
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    (cfg.congrSymbol eSym).workTapeSymbols i = (cfg.workTapeSymbols i).map eSym := rfl


lemma moveInputPos_cast {n m : ℕ} (h : n + 2 = m + 2) (pos : Fin (n + 2)) (mv : SignType) :
    moveInputPos (Fin.cast h pos) mv = Fin.cast h (moveInputPos pos mv) := by
  obtain rfl : n = m := by omega
  simp

lemma step_congrSymbol (eSym : Symbol ≃ Symbol') (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (tm.congrSymbol eSym).step (cfg.congrSymbol eSym)
      = (tm.step cfg).congrSymbol eSym := by
  have key : ∀ x : Option Symbol, Option.map (⇑eSym.symm) (Option.map (⇑eSym) x) = x := by
    intro x; cases x <;> simp
  cases hs : cfg.state with
  | none =>
    have h1 : (tm.congrSymbol eSym).step (cfg.congrSymbol eSym) = cfg.congrSymbol eSym := by
      rw [step]; simp [hs]
    have h2 : tm.step cfg = cfg := by rw [step]; simp [hs]
    rw [h1, h2]
  | some q =>
    conv_lhs => rw [step]
    conv_rhs => rw [step]
    simp only [Cfg.congrSymbol_state, hs, Cfg.congrSymbol_inputSymbol,
      Cfg.congrSymbol_workTapeSymbols, congrSymbol, key]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · exact moveInputPos_cast (by simp) _ _
    · funext i z
      simp only [Cfg.congrSymbol]
      rcases hw : (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i |>.1 with _ | s
      · simp
      · simp [Function.apply_update (fun _ (y : Option Symbol) => Option.map eSym y)]
    · rfl
    · rcases ho : (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).outS with _ | s
      · simp [Cfg.congrSymbol]
      · simp [Cfg.congrSymbol]


lemma configs_congrSymbol (eSym : Symbol ≃ Symbol') (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.congrSymbol eSym).configs (cfg.congrSymbol eSym) t
      = (tm.configs cfg t).congrSymbol eSym := by
  unfold configs
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_congrSymbol]

lemma initCfg_congrSymbol (eSym : Symbol ≃ Symbol') (tm : MultiTapeTM k Symbol State)
    (input : List Symbol) :
    (tm.congrSymbol eSym).initCfg (input.map eSym) = (tm.initCfg input).congrSymbol eSym := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [initCfg, Cfg.congrSymbol, congrSymbol, Fin.ext_iff]

lemma spaceUsed_congrSymbol (eSym : Symbol ≃ Symbol') (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.congrSymbol eSym).spaceUsed (cfg.congrSymbol eSym) t = tm.spaceUsed cfg t := by
  unfold spaceUsed spaceUsedByTape
  simp only [configs_congrSymbol, Cfg.congrSymbol_workTapePos]

lemma computesInTimeAndSpace_congrSymbol (eSym : Symbol ≃ Symbol')
    (tm : MultiTapeTM k Symbol State) (input output : List Symbol) (t s : ℕ)
    (h : tm.ComputesInTimeAndSpace input output t s) :
    (tm.congrSymbol eSym).ComputesInTimeAndSpace (input.map eSym) (output.map eSym) t s := by
  obtain ⟨cfg, hstate, hout, hrel, hspace⟩ := h
  refine ⟨cfg.congrSymbol eSym, by simpa using hstate, by simp [hout], ?_, ?_⟩
  · rw [relatesInSteps_iff_configs_eq] at hrel ⊢
    rw [initCfg_congrSymbol, configs_congrSymbol, hrel]
  · rw [initCfg_congrSymbol, spaceUsed_congrSymbol, hspace]

end CongrSymbol

/-!
## Simulating a deterministic finite automaton

We build a `k = 0` (work-tape-free) multi-tape Turing machine `ofDFA M` that simulates a
deterministic finite automaton `M`, directly over the state type `σ` and alphabet `IOSymbol` of
`M`. The relabeling lemmas above are used later to encode `σ` and `IOSymbol` into `Fin`.
-/

open scoped Classical in
/--
The `k = 0` multi-tape Turing machine simulating a deterministic finite automaton `M`, using `M`'s
state type as its state type and `M`'s alphabet as its tape alphabet.

The machine has no work tapes. The input head starts on the first input cell and only ever moves
right, consuming one input symbol per step and advancing `M`'s state accordingly. When it reaches
the blank cell past the end of the input, it halts, outputting the default symbol iff `M`'s current
state is accepting.
-/
noncomputable def ofDFA {IOSymbol : Type} [Inhabited IOSymbol] {σ : Type} (M : DFA IOSymbol σ) :
    MultiTapeTM 0 IOSymbol σ where
  q₀ := M.start
  tr q input _ :=
    match input with
    | some a =>
        { inputMove := SignType.pos, workActions := Fin.elim0, outS := none,
          q' := some (M.step q a) }
    | none =>
        { inputMove := 0, workActions := Fin.elim0,
          outS := if q ∈ M.accept then some default else none,
          q' := none }

/-- Moving the input head right by one increments its position, if it stays within bounds. -/
lemma moveInputPos_pos {n : ℕ} (pos : Fin (n + 2)) (h : pos.val + 1 < n + 2) :
    (moveInputPos pos SignType.pos).val = pos.val + 1 := by
  unfold moveInputPos
  simp only [SignType.cast, Fin.toNat_eq_val, Fin.is_lt, ↓reduceDIte, Fin.eta]
  rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; omega)]

/-- Invariant of the simulation: after `t ≤ |input|` steps, `ofDFA M` is in the state `M` would be
in after reading the first `t` input symbols, has produced no output, and its head is at position
`1 + t`. -/
lemma ofDFA_sim {IOSymbol : Type} [Inhabited IOSymbol] {σ : Type} (M : DFA IOSymbol σ)
    (input : List IOSymbol) :
    ∀ t, t ≤ input.length →
      ((ofDFA M).configs ((ofDFA M).initCfg input) t).state = some (M.eval (input.take t)) ∧
      ((ofDFA M).configs ((ofDFA M).initCfg input) t).output = [] ∧
      ((ofDFA M).configs ((ofDFA M).initCfg input) t).inputPos.val = 1 + t := by
  intro t
  induction t with
  | zero => intro _; refine ⟨?_, ?_, ?_⟩ <;> simp [configs, ofDFA]
  | succ t ih =>
    intro ht
    obtain ⟨hst, hout, hpos⟩ := ih (by omega)
    have hlt : t < input.length := by omega
    set c := (ofDFA M).configs ((ofDFA M).initCfg input) t with hc
    have hsym : c.inputSymbol = some input[t] := inputSymbolInner (cfg := c) t hpos hlt
    have hstep : (ofDFA M).configs ((ofDFA M).initCfg input) (t + 1) = (ofDFA M).step c := by
      rw [hc, configs, configs, Function.iterate_succ_apply']
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [step, hst, hsym]; simp only [ofDFA]
      rw [List.take_succ_eq_append_getElem hlt, M.eval_append_singleton]
    · rw [step, hst, hsym]; simp [ofDFA, hout]
    · rw [step, hst, hsym]; simp only [ofDFA]
      rw [moveInputPos_pos c.inputPos (by omega)]; omega

open scoped Classical in
/-- The Turing machine `ofDFA M` computes the indicator of the language of `M`: on input `input` it
halts after `|input| + 1` steps in zero space, outputting `[default]` iff `M` accepts `input`. -/
lemma ofDFA_computes {IOSymbol : Type} [Inhabited IOSymbol] {σ : Type} (M : DFA IOSymbol σ)
    (input : List IOSymbol) :
    (ofDFA M).ComputesInTimeAndSpace input
      (if M.eval input ∈ M.accept then [default] else []) (input.length + 1) 0 := by
  obtain ⟨hst, hout, hpos⟩ := ofDFA_sim M input input.length le_rfl
  set c := (ofDFA M).configs ((ofDFA M).initCfg input) input.length with hc
  have hval : c.inputPos.val = input.length + 1 := by omega
  have hsym : c.inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg (by simp [Fin.ext_iff, hval]), dif_pos (by simp [hval])]
  have hstep : (ofDFA M).configs ((ofDFA M).initCfg input) (input.length + 1)
      = (ofDFA M).step c := by
    rw [hc, configs, configs, Function.iterate_succ_apply']
  refine ⟨(ofDFA M).configs ((ofDFA M).initCfg input) (input.length + 1), ?_, ?_, ?_, ?_⟩
  · rw [hstep, step, hst, hsym]; simp [ofDFA]
  · rw [hstep, step, hst, hsym]; simp only [ofDFA, hout, List.take_length]
    by_cases hacc : M.eval input ∈ M.accept <;> simp [hacc]
  · rw [relatesInSteps_iff_configs_eq]
  · exact spaceUsed_zero_tapes_eq_zero _ _ rfl

/--
Every regular language over a finite alphabet is decidable by a multi-tape Turing machine without
work tapes (`k = 0`), hence in zero space, within `n + 2` steps.
-/
theorem isRegular_decidableInTimeAndSpace
    {IOSymbol : Type} [Inhabited IOSymbol] [Finite IOSymbol]
    {L : Language IOSymbol} (hL : L.IsRegular) :
    DecidableInTimeAndSpace L (fun n => n + 2) (fun _ => 0) := by
  classical
  obtain ⟨σ, _, M, hM⟩ := hL
  have : Fintype IOSymbol := Fintype.ofFinite IOSymbol
  refine ⟨0, Fintype.card IOSymbol, Fintype.card σ, (Fintype.equivFin IOSymbol).toEmbedding,
    ((ofDFA M).congrState (Fintype.equivFin σ).toEmbedding).congrSymbol
      (Fintype.equivFin IOSymbol), ?_⟩
  intro input
  refine ⟨input.length + 1, Nat.le_succ _, 0, le_rfl, ?_⟩
  have heq : (if M.eval input ∈ M.accept then [default] else []) = indicator L input := by
    have hiff : (M.eval input ∈ M.accept) ↔ (input ∈ L) := by rw [← hM, DFA.mem_accepts]
    unfold indicator
    exact if_congr hiff rfl rfl
  have hcomp := ofDFA_computes M input
  rw [heq] at hcomp
  have h1 := computesInTimeAndSpace_congrState (Fintype.equivFin σ).toEmbedding (ofDFA M)
    input (indicator L input) (input.length + 1) 0 hcomp
  have h2 := computesInTimeAndSpace_congrSymbol (Fintype.equivFin IOSymbol)
    ((ofDFA M).congrState (Fintype.equivFin σ).toEmbedding)
    input (indicator L input) (input.length + 1) 0 h1
  simpa using h2

end Turing.MultiTapeTM
