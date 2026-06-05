/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Simulations between different machines


-/

@[expose] public section

open Cslib Relation Turing.BiTape Turing.MultiTapeTM.Cfg

namespace Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

namespace MultiTapeTM

section SingleTapeTMSimulation
/-! Simulation of a single-tape TM by a multi-tape TM. -/

variable (tm : SingleTapeTM Symbol)

-- Stages of simulating a single-tape TM in a multi-tape TM:
-- 1. copy input to work tape
-- 2. move to start of work tape
-- 3. run single-tape-tm on work tape
-- 4. copy output to output tape and halt


inductive SimState where
  | copyInput -- copy from the input tape to the work tape
  | moveToStart -- move to the start of the work tape
  | runSingleTape (q : tm.State) -- simulate single-tape TM on work tape
  | copyOutput -- copy output to output tape
deriving Fintype

def SimTr :
    (SimState tm) → (Option Symbol) → (Fin 1 → Option Symbol) → TransitionOut 1 Symbol (SimState tm)
  | .copyInput => fun input _ => match input with
    | none => ⟨none, fun _ => ⟨none, some .left⟩, none, some .moveToStart⟩
    | some c => ⟨some .right, fun _ => ⟨some (some c), some .right⟩, none, some .copyInput⟩
  | .moveToStart => fun _ syms => match syms 0 with
    | some c => ⟨none, fun _ => ⟨none, some .left⟩, none, some .moveToStart⟩
    | none => ⟨none, fun _ => ⟨none, some .right⟩, none, some (.runSingleTape tm.q₀)⟩
  | .runSingleTape q => sorry
  | .copyOutput => sorry

def MultiFromSingle : MultiTapeTM (k := 1) Symbol where
  State := SimState tm
  q₀ := .copyInput
  tr := SimTr tm

-- TODO re-prove this using RelatesInSteps?

lemma copyInput_innerStep
    (input : List Symbol) (t : ℕ) (h_lt : t ≤ input.length) :
    (MultiFromSingle tm).configs ((MultiFromSingle tm).initCfg input) t =
      some ⟨some .copyInput, input, ⟨1 + t, by omega⟩,
            fun _ => (BiTape.mk₁ (input.take t)).moveInt t, []⟩ := by
  induction t with
  | zero =>
    simp [configs, Function.iterate_zero, initCfg, MultiFromSingle, moveInt]
  | succ t ih =>
    have hinput (work : BiTape Symbol) : (MultiFromSingle tm).inputSymbol
        ⟨some .copyInput, input, ⟨1 + t, by omega⟩, fun _ => work, []⟩ = some input[t] := by
      grind
    have htransitionOut (work : BiTape Symbol) :
        (MultiFromSingle tm).transitionOutput .copyInput (some input[t]) (fun _ => work) =
        ⟨some .right, fun _ => ⟨some input[t], some .right⟩, none, some .copyInput⟩ := by
      unfold MultiFromSingle SimTr
      simp [transitionOutput]
    have htape : (((mk₁ (List.take t input)).moveInt ↑t).write (some input[t])).move Dir.right =
        (mk₁ (List.take (t + 1) input)).moveInt (↑t + 1) := by
      ext1 i
      simp [Function.update]
      grind
    rw [configs_succ, ih (by omega)]
    simp [step, hinput, htransitionOut, moveInputPos, optionDirToInt, htape]
    grind

lemma copyInput_lastStep
    (input : List Symbol) (work : BiTape Symbol) :
    (MultiFromSingle tm).step
      ⟨some .copyInput, input, ⟨1 + input.length, by omega⟩, fun _ => work, []⟩ =
      some ⟨some .moveToStart, input, ⟨1 + input.length, by omega⟩,
          fun _ => work.move_left, []⟩ := by
  have hinput : (MultiFromSingle tm).inputSymbol
      ⟨some .copyInput, input, ⟨1 + input.length, by omega⟩, fun _ => work, []⟩ = none := by
    grind
  have htransitionOut :
      (MultiFromSingle tm).transitionOutput .copyInput none (fun _ => work) =
      ⟨none, fun _ => ⟨none, some .left⟩, none, some .moveToStart⟩ := by
    unfold MultiFromSingle SimTr
    simp [transitionOutput]
  simp [step, hinput, htransitionOut]
  grind

lemma moveToStart_semantics (input work : List Symbol) (ip : Fin (input.length + 2))
    (t : ℕ) (h_lt : t < work.length - 1) :
    RelatesInSteps (MultiFromSingle tm).TransitionRelation
      ⟨some .moveToStart, input, ip, fun _ => (BiTape.mk₁ work).moveInt (t - 1), []⟩
      ⟨some .moveToStart, input, ip, fun _ => (BiTape.mk₁ work).moveInt (-1), []⟩
      t := by
  induction t with
  | zero => simp [RelatesInSteps.zero_iff]
  | succ t ih =>
    specialize ih (by omega)
    rw [RelatesInSteps.succ'_iff]
    refine ⟨⟨some .moveToStart, input, ip, fun _ => (BiTape.mk₁ work).moveInt (t - 1), []⟩, ?_, ih⟩
    have h_inputSymbol : (MultiFromSingle tm).inputSymbol
        ⟨some .moveToStart, input, ip, fun _ => (BiTape.mk₁ work).moveInt (t - 1), []⟩ ≠ none := by
      grind
    have htout (c : Symbol) : (MultiFromSingle tm).transitionOutput
          .moveToStart (some c) (fun _ => (BiTape.mk₁ work).moveInt t) =
        ⟨none, fun _ => ⟨none, some .left⟩, none, some .moveToStart⟩ := by
      unfold MultiFromSingle SimTr
      simp [inputSymbol]
      sorry

    --   grind
    simp [TransitionRelation, step, h_inputSymbol, htout, moveInputPos, optionDirToInt]
    ext i
    simp [optionDirToInt]
    grind



end SingleTapeTMSimulation

end MultiTapeTM

end Turing
