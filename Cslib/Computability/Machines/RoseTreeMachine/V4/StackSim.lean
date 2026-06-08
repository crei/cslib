/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.Prog

/-! # RoseTreeMachine V4 — an iterative, defunctionalized simulator (no proofs)

This file gives a Lean evaluator for `Prog` whose **inner step is a single non-recursive
transition** over explicit stacks. It is a defunctionalized abstract machine in the style of a
CEK machine: continuations are reified as a first-order list of `Instruction`s (the *control
stack*), intermediate results live on a *value stack*, and environments are carried inside the
`eval` instructions.

The point of the exercise is that the source language's only control-flow constructs — recursion
through `app`/`elim` and iteration through `while_` — are all expressed by *pushing further
instructions onto the control stack*. The single `step` function never calls itself. The only
loop is the outer driver `iterate`, which simply applies `step` until the control stack is
empty; that loop is the analogue of an in-place `while_`.

Because the source language is Turing-complete, the driver need not terminate, so it is given a
`noncomputable` definition via classical choice (it selects the least number of steps after
which the machine has halted, if such a number exists).

No correctness statements are proved here; this is the explicit Lean model that a later
translation into an in-place `Prog` (a single `while_` over this `step`) can target.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

namespace StackSim

/-- Extract first-order data from a runtime value. Closures are not first-order; since a
well-formed program never inspects a closure as data, they are mapped to the empty list. -/
def valueToData : Value → Data
  | .data d => d
  | .closure _ _ => Data.l []

/-! ### The instruction set (defunctionalized continuations)

Each constructor is one kind of pending work. Evaluating a compound term never recurses: it
simply pushes the sub-evaluations followed by the instruction that combines their results. -/

/-- A single unit of pending work on the control stack. -/
inductive Instruction where
  /-- Evaluate `program` under `env`, pushing the resulting value. -/
  | eval (env : List Value) (program : Prog)
  /-- Combine the top two values (`tail` then `head`) into a `cons`. -/
  | buildCons
  /-- The scrutinee of an `elim` is on top of the value stack; choose the empty or the
      cons branch, evaluating the corresponding sub-program under `env`. -/
  | chooseElimBranch (env : List Value) (emptyBranch : Prog) (consBranch : Prog)
  /-- Push a known value onto the value stack. Used to place the (already-evaluated)
      arguments of an `elim` cons branch so that a uniform `apply` can consume them. -/
  | pushValue (value : Value)
  /-- Apply a function to an argument: the argument is on top of the value stack and the
      function value directly below it. This single instruction serves `app`, the two
      applications of an `elim` cons branch, and each iteration of a `while_`. -/
  | apply
  /-- Begin a `while_` loop: the body closure is on top of the value stack and the initial
      accumulator below it. -/
  | startWhile
  /-- One halting check of a `while_` loop carrying its body closure; the current accumulator
      is on top of the value stack. -/
  | whileStep (bodyClosure : Value)

/-- The machine state: a control stack of pending instructions and a value stack of results. -/
structure MachineState where
  /-- Instructions still to be executed, innermost first. -/
  control : List Instruction
  /-- Intermediate values produced so far, most recent first. -/
  values : List Value

/-! ### The non-recursive transition function

`step` pattern-matches on the top instruction and either pushes sub-instructions or consumes
values and pushes a result. It never calls itself. Malformed configurations (an out-of-range
variable, applying a non-closure, an empty stack where a value is expected) fall back to safe
defaults rather than getting stuck, which keeps the function total. -/

/-- One transition of the abstract machine. This function is deliberately non-recursive: every
form of control flow in the source language is realised by pushing further instructions. -/
def step (state : MachineState) : MachineState :=
  match state.control with
  | [] => state
  | instruction :: remainingControl =>
    match instruction with
    | .eval env program =>
      match program with
      | .var index =>
        let lookupIndex : ℕ := index
        { control := remainingControl,
          values := (env[lookupIndex]?.getD Value.empty) :: state.values }
      | .empty =>
        { control := remainingControl, values := Value.empty :: state.values }
      | .cons head tail =>
        { control := .eval env head :: .eval env tail :: .buildCons :: remainingControl,
          values := state.values }
      | .elim scrutinee emptyBranch consBranch =>
        { control := .eval env scrutinee ::
            .chooseElimBranch env emptyBranch consBranch :: remainingControl,
          values := state.values }
      | .while_ initial body =>
        { control := .eval env initial :: .eval env body :: .startWhile :: remainingControl,
          values := state.values }
      | .fn body =>
        { control := remainingControl, values := Value.closure body env :: state.values }
      | .app function argument =>
        { control := .eval env function :: .eval env argument :: .apply :: remainingControl,
          values := state.values }
    | .buildCons =>
      match state.values with
      | tailValue :: headValue :: remainingValues =>
        { control := remainingControl,
          values := Value.data (Data.l (valueToData headValue :: (valueToData tailValue).asList)) ::
            remainingValues }
      | _ => { control := remainingControl, values := state.values }
    | .chooseElimBranch env emptyBranch consBranch =>
      match state.values with
      | scrutineeValue :: remainingValues =>
        match (valueToData scrutineeValue).asList with
        | [] =>
          { control := .eval env emptyBranch :: remainingControl, values := remainingValues }
        | head :: tail =>
          { control := .eval env consBranch :: .pushValue (Value.data head) :: .apply ::
              .pushValue (Value.data (Data.l tail)) :: .apply :: remainingControl,
            values := remainingValues }
      | _ => { control := remainingControl, values := state.values }
    | .pushValue value =>
      { control := remainingControl, values := value :: state.values }
    | .apply =>
      match state.values with
      | argumentValue :: functionValue :: remainingValues =>
        match functionValue with
        | .closure body capturedEnv =>
          { control := .eval (capturedEnv ++ [argumentValue]) body :: remainingControl,
            values := remainingValues }
        | .data _ => { control := remainingControl, values := remainingValues }
      | _ => { control := remainingControl, values := state.values }
    | .startWhile =>
      match state.values with
      | bodyClosure :: accumulator :: remainingValues =>
        { control := .whileStep bodyClosure :: remainingControl,
          values := accumulator :: remainingValues }
      | _ => { control := remainingControl, values := state.values }
    | .whileStep bodyClosure =>
      match state.values with
      | accumulator :: remainingValues =>
        if (valueToData accumulator).asList.head?.getD (Data.l []) = Data.l [] then
          { control := remainingControl, values := accumulator :: remainingValues }
        else
          { control := .apply :: .whileStep bodyClosure :: remainingControl,
            values := accumulator :: bodyClosure :: remainingValues }
      | _ => { control := remainingControl, values := state.values }

/-! ### The driver

The initial state evaluates `program` in the singleton env holding the `input`, exactly
as `ComputesInTimeAndSpace` does. The machine has halted once its control stack is empty. -/

/-- Build the initial machine state for running `program` on `input`. -/
def initialState (program : Prog) (input : Data) : MachineState :=
  { control := [.eval [Value.data input] program], values := [] }

/-- The machine has finished when there is no more pending work. -/
def isHalted (state : MachineState) : Prop := state.control = []

open Classical in
/-- Run the machine to completion. Since the source language is Turing-complete this need not
terminate, so the definition is `noncomputable`: it iterates `step` for some number of steps
after which the machine has halted (and returns the unmodified start state if it never halts,
which cannot happen for a converging program). Halted states are fixed points of `step`, so any
such step count yields the same final state. -/
noncomputable def runToHalt (start : MachineState) : MachineState :=
  if existence : ∃ stepCount, isHalted (Nat.iterate step stepCount start) then
    Nat.iterate step (Classical.choose existence) start
  else
    start

/-- Evaluate `program` on `input`, returning the resulting runtime value (the empty value if the
machine never halts or leaves no result). -/
noncomputable def evaluateValue (program : Prog) (input : Data) : Value :=
  (runToHalt (initialState program input)).values.headD Value.empty

/-- Evaluate `program` on `input`, returning the resulting first-order data. -/
noncomputable def evaluate (program : Prog) (input : Data) : Data :=
  valueToData (evaluateValue program input)

end StackSim

end V4

end RoseTreeMachine

end Turing
