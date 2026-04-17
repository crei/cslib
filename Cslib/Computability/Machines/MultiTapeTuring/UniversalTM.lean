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

/-- The cell of a single Turing tape. -/
public structure TapeCell where
  /-- TODO document -/
  c : Option Data
  /-- TODO document -/
  containsHead : Bool

public instance : StrEnc TapeCell where
  toData cell := StrEnc.toData (cell.c, cell.containsHead)
  fromData d := do
    let (c, containsHead) ← StrEnc.fromData d
    pure { c, containsHead }
  fromData_toData := by
    intro c
    simp

-- public instance (α : Type) [StrEnc α] (k : ℕ) : StrEnc (Vector α k) where
--   toData v := StrEnc.toData v.toList
--   fromData d := do
--       let ls : List α ← StrEnc.fromData d
--       if h : ls.length = k then
--         pure ⟨ls.toArray, h⟩
--       else
--         none
--   fromData_toData := by
--     intro v
--     simp [Vector.toList]


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

variable [Inhabited Symbol] [Fintype Symbol] [StrEnc Symbol]

public structure EncodingParams (k : ℕ) where
  start : Fin k → ℤ
  length : ℕ

/-- The encoding of the given tapes as a list of `MultiCell`s.
The parameter `shifts` specifies where relative to the current head position we start encoding.
Note that the encoding can only be decoded for some values of `shifts` and `length`. -/
public def encodeTapes {k : ℕ} (tapes : Fin k → BiTape Symbol) (params : EncodingParams k) :
    List (Fin k → TapeCell) :=
  let rec encodeTapes' (start : Fin k → ℤ) (length : ℕ) :=
    match length with
    | .zero => []
    | l + 1 =>
      (fun i => {
          c := ((tapes i).atPos (start i)).map StrEnc.toData,
          containsHead := start i == 0 }) ::
        encodeTapes' (fun i => start i + 1) l
  encodeTapes' params.start params.length

/-- The minimal head positions over all tapes at step `t` starting from initial zero positions. -/
public def minHeadPos
  {k : ℕ} (tm : MultiTapeTM k Symbol) (initialTapes : Fin k → BiTape Symbol) (t : ℕ) : ℤ :=
  if h : k = 0 then
    0
  else
    (List.ofFn (tm.headPosition initialTapes t)).min (by simp [h])

/-- The maximal head positions over all tapes at step `t` starting from initial zero positions. -/
public def maxHeadPos
  -- TODO this looks needlessly complicated.
  {k : ℕ} (tm : MultiTapeTM k Symbol) (initialTapes : Fin k → BiTape Symbol) (t : ℕ) : ℤ :=
  if h : k = 0 then
    0
  else
    (List.ofFn (tm.headPosition initialTapes t)).max (by simp [h])

-- TODO use this sequence of encoding parameters.

public def encodingParamSequence  {k : ℕ} (tm : MultiTapeTM k Symbol)
    (initialTapes : Fin k → BiTape Symbol) (t : ℕ) : EncodingParams k :=
  let length : ℕ := (maxHeadPos tm initialTapes t) - (minHeadPos tm initialTapes)
  let shift : ℕ  := fun i => sorry
  ⟨ shift, length ⟩

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

def getHeadSymbol (k : ℕ) (tapeIdx : ℕ) (mt out aux : Fin k) : MultiTapeTM k Char :=
  -- Find the cell where the tapeIdx-th tape has the head
  find_list mt aux (atPath [0, tapeIdx, 1] mt (copyEnc mt aux))
    -- copy the symbol to out
    (atPath [0, tapeIdx, 0] mt (copy_to_list mt out))
    -- otherwise do nothing (because we know there is a head marker)
    (noop)

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
