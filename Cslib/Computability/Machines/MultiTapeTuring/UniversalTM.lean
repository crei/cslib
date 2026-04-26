/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Navigation
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Copy
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Eq
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.ListIteration
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed
import Mathlib.Order.Interval.Finset.Defs

namespace Turing

namespace UniversalTM

open Routines

variable [Inhabited Symbol] [Fintype Symbol] [StrEnc Symbol]

/-- The cell of a single Turing tape. -/
public structure TapeCell Symbol where
  /-- The symbol in the cell. -/
  c : Option Symbol
  /-- If the head is at this cell currently. -/
  containsHead : Bool

public instance : StrEnc (TapeCell Symbol) where
  toData cell := StrEnc.toData (cell.c, cell.containsHead)
  fromData d := do
    let (c, containsHead) ← StrEnc.fromData d
    pure { c, containsHead }
  fromData_toData := by
    intro c
    simp
  toData_fromData := by
    intro d cell h
    simp only at h
    match hpair : StrEnc.fromData (α := Option Symbol × Bool) d, h with
    | some (c, ch), h =>
      simp only [Option.pure_def] at h
      cases h
      have := StrEnc.toData_fromData _ _ hpair
      rw [show ({ c := c, containsHead := ch } : TapeCell Symbol).c = c from rfl,
          show ({ c := c, containsHead := ch } : TapeCell Symbol).containsHead = ch from rfl]
      exact this

/-
Outline of UTM:
while the current state is not None:
- for each tape, find the head position on the multi-tape
  and copy the current symbol to an aux tape.
- now the aux tape contains the symbols in the correct order.
- copy the current state to the aux tape.
- the contents of the aux tape is exactly the input to the
  transition function
- "evaluate the transition function" by iterating through its
  table and storing the result on another tape
- execute the actions for each of the tapes:
  - find the head. update the symbol, update the head marking
    according to the move action
    (potentially extend the tape to the left or right)
- update the current state
-/

/- sub-routines we need:
- move to the first element of a list that satisfies a condition:
  tm₁ tm₂ tm₃: For each item in the list: if tm₁ outputs true on an aux tape, run tm₂.
  if it never outputs true, run tm₃
- evaluate a function given by a list of input-output pairs
- update an element in a list, whose encoding size must be the same
- extend a list to the right
-/


/-- Parameters for encoding a tuple of tapes as a single tape with multiple tracks. -/
public structure EncodingParams (k : ℕ) where
  /-- The encoding start for each tape, relative to the tape head. -/
  start : Fin k → ℤ
  /-- The number of cells to encode. -/
  length : ℕ

/-- The encoding of a tuple of tapes as a list of tuples of `TapeCell`s.
Note that the encoding can only be decoded for some values of `params`. -/
public def encodeTapes {k : ℕ} (tapes : Fin k → BiTape Symbol) (params : EncodingParams k) :
    List (Fin k → TapeCell Symbol) :=
  List.ofFn (n := params.length) fun p i =>
    {
      c := (tapes i).atPos ((params.start i) + p)
      containsHead := (params.start i) + p == 0
    }

/-- The minimal head positions over all tapes at step `t` starting from initial zero positions. -/
public def minHeadPos
  {k : ℕ} (tm : MultiTapeTM k Symbol) (initialTapes : Fin k → BiTape Symbol) (t : ℕ) : ℤ :=
  (List.ofFn (tm.headPosition initialTapes t)).min?.getD 0

/-- The maximal head positions over all tapes at step `t` starting from initial zero positions. -/
public def maxHeadPos
  {k : ℕ} (tm : MultiTapeTM k Symbol) (initialTapes : Fin k → BiTape Symbol) (t : ℕ) : ℤ :=
  (List.ofFn (tm.headPosition initialTapes t)).max?.getD 0

-- TODO use this sequence of encoding parameters.

public def encodingParamSequence {k : ℕ} (tm : MultiTapeTM k Symbol)
    (initialTapes : Fin k → BiTape Symbol) (t : ℕ) : EncodingParams k :=
  let headPositions := tm.headPosition initialTapes
  -- The min head position over all tapes at a specific step
  let minHeadPosAtStep := fun t' => (List.ofFn (headPositions t')).min?.getD 0
  let maxHeadPosAtStep := fun t' => (List.ofFn (headPositions t')).max?.getD 0
  -- The min head position over all tapes and all steps until step t
  -- TODO check for off-by-one errors here
  let minHeadPosUntil := (List.ofFn (n := t + 1) (fun t' => minHeadPosAtStep t')).min?.getD 0
  let maxHeadPosUntil := (List.ofFn (n := t + 1) (fun t' => maxHeadPosAtStep t')).max?.getD 0
  let length := 1 + (maxHeadPosUntil - minHeadPosUntil).toNat
  let start := fun i => (headPositions t i) - minHeadPosUntil
  ⟨ start, length ⟩

public def updateEncodingParams {k : ℕ} (tm : MultiTapeTM k Symbol)
  (params : EncodingParams k)
  (cfg : tm.Cfg) : EncodingParams k := sorry
  -- match cfg with
  -- | ⟨none, _⟩ => (fun _ => 0)
  -- | ⟨some q, tapes⟩ =>
  --   match tm.tr q (fun i => (tapes i).head) with
  --   | ⟨stmts, _⟩ => fun i => shifts i + (match (stmts i).movement with
  --     | none => 0
  --     | .some .right => 1
  --     | .some .left => -1)

def getHeadSymbol (k : ℕ) (tapeIdx : ℕ) (tapes out aux : Fin k) : MultiTapeTM k Char :=
  find_list tapes aux
    -- Find the cell where the tapeIdx-th tape has the head
    (atPath [0, tapeIdx, 1] tapes (copyEnc tapes aux))
    -- copy the symbol to out
    (atPath [0, tapeIdx, 0] tapes (copy_to_list tapes out))
    -- otherwise do nothing (because we know there is a head marker)
    (noop)

lemma geatHeadSymbol.semantics {k k' : ℕ} (tapeIdx : ℕ) (tapes out aux : Fin k)
  (h_tapes_aux : tapes ≠ aux)
  {t : Fin k' → BiTape Symbol}
  {views : Fin k → TapeView}
  {params : EncodingParams k'}
  (h_tapes : views tapes = .ofEnc (encodeTapes t params))
   :
  (getHeadSymbol k tapeIdx tapes out aux).eval_struct views = sorry := by
  unfold getHeadSymbol
  have h_check : computes_function_read_replace
      (atPath [0, tapeIdx, 1] tapes (copyEnc tapes aux))
      (fun tc : TapeCell Symbol => tc.containsHead)
      tapes
      aux := by
    sorry
  rw [find_list.computes_fun (h_tapes_aux) h_check views sorry sorry sorry]
  simp
  sorry

-- /-- Copies the symbol the head of tape `i` currently points to, to tape 3. -/
-- def copyReadSymbol (i : Fin k) : MultiTapeTM 10 Char :=
--   find_list 1 4 (atPath [0, i, 1] 1 (copyEnc 1 4))
--     (atPath [0, i, 0] 1 (copy_to_list 1 4))
--     (noop)


public def utm_step : MultiTapeTM 10 Char := sorry

/-- Main theorem -/
public theorem utm_step_semantics
  {k : ℕ} (tm : MultiTapeTM k Symbol)
  [StrEnc tm.State] -- it is a fintype, so easy to satsify
  (cfg : tm.Cfg)
  (views : Fin 10 → TapeView)
  (params : EncodingParams k)
  (h_tapes : views 1 = .ofEnc (encodeTapes cfg.tapes params))
  (h_state : views 2 = .ofEnc cfg.state) :
  utm_step.eval_struct views = .some (match tm.step cfg with
    | none => views
    | some cfg' => Function.update (Function.update views
      1 (.ofEnc (encodeTapes cfg'.tapes (updateEncodingParams tm params cfg))))
      2 (.ofEnc cfg'.state)) := by sorry

end UniversalTM

end Turing
