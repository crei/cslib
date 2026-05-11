/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- TODO create a "common file"?
public import Cslib.Computability.Machines.SingleTapeTuring.Basic

public import Mathlib.Data.Part

import Std
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Defs



inductive Data where
  | l : List Data → Data
deriving Repr, BEq

abbrev Data.empty := Data.l []

abbrev Data.asList
  | Data.l items => items

structure TapeIndex where
  id : ℕ
deriving Repr, BEq, Hashable

-- Is a program a map from Nat to operations which reference smaller indices?

inductive Operation
  | empty
  | copy (tape : TapeIndex)
  | cons (head tail : TapeIndex)
  -- | fold (list : TapeIndex) (step : List Operation)
deriving Repr

abbrev Program := List Operation

def eval (p : Program) (stack : List Data) : Part (List Data) :=
  match p with
  | [] => .some stack
  | .empty :: ops =>
    eval ops (stack.concat Data.empty)
  | .copy t :: ops =>
    -- TODO can we enforce that inside the program?
    if h : t.id < stack.length then
      eval ops (stack.concat stack[t.id])
    else
      Part.none
  | .cons head tail :: ops =>
    if h : head.id < stack.length ∧ tail.id < stack.length then
      eval ops (stack.concat (Data.l (stack[head.id] :: stack[tail.id].asList)))
    else
      Part.none
  -- | .fold list init step :: ops =>
  --   if h : list.id < initial.length then
  --     let listData := initial[list.id]
  --     match listData with
  --     | Data.l items =>
  --       let initData := initial.getLast'sorry
  --       let stepOps := step.map (fun op => op.mapTapeIndex (fun t => initial[t.id]))
  --   else
  --     Part.none


structure BuilderCtx where
  nextTapeIndex : ℕ
  program : Program
deriving Repr

abbrev Build (α : Type) := StateT BuilderCtx (Except String) α

def newTape (p : Program) : Build TapeIdx := do
  let env ← get
  let sid := env.next
  set { env with next := sid + 1, ops := env.ops ++ [op] }
  return ⟨sid⟩

-- ============================================================
-- SLOT PRIMITIVES
-- ============================================================

-- Allocate a slot holding Data.l []
def new : Build TapeIdx :=
  newTape Program.new

-- Prepend a as first child of b
-- O(1) time, O(1) space — one new heap node with two pointers
def cons (a b : Slot) : Build Slot :=
  newTape s!"cons({a.id},{b.id})"

-- Left fold over children of slot a
-- O(n) time — space = max live accumulator = size of final result
opaque fold
    {α : Type}
    (a    : Slot)
    (init : α)
    (step : Slot → α → Build α)
    : Build α

-- Right fold over children of slot a
-- O(n) time — needed for single-pass append/snoc
opaque foldr
    {α : Type}
    (a    : Slot)
    (init : α)
    (step : Slot → α → Build α)
    : Build α

-- Data.l [] if a = b, nonempty otherwise
-- eq_ a a = Data.l [] is correct: slots are immutable so same slot = same value
-- O(n) time structural equality, O(1) space
opaque eq_ (a b : Slot) : Build Slot

-- Branch on slot value: Data.l [] = false, anything else = true
opaque if_
    {α : Type}
    (cond  : Slot)
    (then_ : Build α)
    (else_ : Build α)
    : Build α

-- Loop until condition slot returned by step is Data.l []
-- Step: current state → (condition, next state)
-- Only source of non-termination in the system
opaque while_
    {α : Type}
    (step : α → Build (Slot × α))
    (init : α)
    : Build α

-- ============================================================
-- INPUT TAPE PRIMITIVES
-- All navigation is O(1) space (just moves the read head)
-- ============================================================

-- Move into first child
-- nonEmpty branch: cursor moves to first child's (
-- empty branch:    current node is Data.l [], cursor stays
-- O(1) time — peek right one cell
opaque down
    {α : Type}
    (nonEmpty : Build α)
    (empty    : Build α)
    : Build α

-- Move to parent
-- hasParent branch: cursor moves to parent's (
-- isRoot branch:    already at root, cursor stays
-- O(n) time — scan left past siblings counting brackets
opaque up
    {α : Type}
    (hasParent : Build α)
    (isRoot    : Build α)
    : Build α

-- Move to next sibling
-- hasNext branch: cursor moves to next sibling's (
-- isLast branch:  no next sibling (cursor lands on parent's ))
-- O(n) time — scan right past current subtree
opaque next
    {α : Type}
    (hasNext : Build α)
    (isLast  : Build α)
    : Build α

-- Move to previous sibling
-- hasPrev branch: cursor moves to previous sibling's (
-- isFirst branch: no previous sibling, cursor stays
-- O(n) time — scan left past previous subtree
opaque prev
    {α : Type}
    (hasPrev : Build α)
    (isFirst : Build α)
    : Build α

-- Copy the subtree at the current cursor position into a new slot
-- O(n) time, O(n) space
opaque readCursor : Build Slot

-- ============================================================
-- DERIVED: BOOLEAN SLOTS
-- ============================================================

def false_ : Build Slot := new
def true_  : Build Slot := do cons (← new) (← new)

-- ============================================================
-- DERIVED: BOUNDARY DETECTION
-- (all derived from navigation combinators)
-- ============================================================

def cursorEmpty : Build Slot :=
  down (do up (return ()) (return ()); false_) true_

def isFirst_ : Build Slot :=
  prev (do next (return ()) (return ()); false_) true_

def isLast_ : Build Slot :=
  next (do prev (return ()) (return ()); false_) true_

def isRoot_ : Build Slot :=
  up (do down (return ()) (return ()); false_) true_

-- ============================================================
-- DERIVED: SLOT CONSTRUCTORS
-- ============================================================

def wrap (a : Slot) : Build Slot :=
  cons a (← new)

def copy (a : Slot) : Build Slot :=
  fold a (← new) (fun child acc => cons child acc)

-- ============================================================
-- DERIVED: BOOLEAN OPERATIONS ON SLOTS
-- ============================================================

def not_ (a : Slot) : Build Slot :=
  if_ a false_ true_

def and_ (a b : Slot) : Build Slot :=
  if_ a (return b) false_

def or_ (a b : Slot) : Build Slot :=
  if_ a true_ (return b)

def xor_ (a b : Slot) : Build Slot :=
  not_ =<< eq_ a b

-- ============================================================
-- DERIVED: LIST OPERATIONS ON SLOTS
-- ============================================================

-- Append: children of a then children of b — O(|a|) time, O(|a|) space
def append_ (a b : Slot) : Build Slot :=
  foldr a b (fun child acc => cons child acc)

-- Reverse — O(n) time, O(n) space
def reverse_ (a : Slot) : Build Slot :=
  fold a (← new) (fun child acc => cons child acc)

-- Snoc: b as last child of a — O(n) time, O(n) space
def snoc (a b : Slot) : Build Slot :=
  foldr a (← wrap b) (fun child acc => cons child acc)

-- Filter — O(n) time, O(m) space where m = kept elements
def filter (a : Slot) (pred : Slot → Build Slot) : Build Slot :=
  fold a (← new) (fun child acc => do
    if_ (← pred child)
      (cons child acc)
      (return acc))

-- ============================================================
-- DERIVED: INPUT TAPE ITERATION
-- ============================================================

-- Fold over children of current cursor node
-- O(n) time — visits each child once
-- space = accumulator = O(output size)
def foldCursor {α : Type} (init : α) (step : α → Build α) : Build α :=
  down
    (do
      let result ← while_
        (fun acc => do
          let r    ← step acc
          let cond ← next
            (do false_)    -- has next sibling: condition = false = keep going
            (do true_)     -- no next sibling: condition = true = stop
          return (cond, r))
        init
      up (return ()) (return ())
      return result)
    (return init)          -- empty node: nothing to fold

-- Read all children of current node into a slot
-- O(n) time, O(n) space
def readChildren : Build Slot := do
  foldCursor (← new) (fun acc => do
    let child ← readCursor
    down (up (return ()) (return ())) (return ())  -- step into child and back
    cons child acc)

-- ============================================================
-- DERIVED: BINARY NATURAL NUMBERS IN SLOTS
--
-- Encoding: Data.l [b0, b1, ..., bn] LSB first
--   Data.l []  = bit 0
--   nonempty   = bit 1
-- ============================================================

def bit0 : Build Slot := new
def bit1 : Build Slot := true_

def addBits (a b carry : Slot) : Build (Slot × Slot) := do
  let sumBit   ← xor_ (← xor_ a b) carry
  let carryOut ← if_ (← and_ a b)
    true_
    (and_ b carry)
  return (sumBit, carryOut)

-- Add two binary numbers — O(n²) time, O(n) space
def add (a b : Slot) : Build Slot := do
  let (acc, bRest, carry) ← fold a (← new, b, ← bit0)
    (fun aBit (acc, bRest, carry) => do
      let (bBit, bTail) ← if_ bRest
        (fold bRest (← bit0, ← new)
          (fun h _ => return (h, ← new)))  -- take head of bRest
        (do return (← bit0, ← new))        -- b exhausted
      let (s, c) ← addBits aBit bBit carry
      return (← cons s acc, bTail, c))
  let (acc2, carry2) ← fold bRest (acc, carry)
    (fun bBit (acc, carry) => do
      let (s, c) ← addBits (← bit0) bBit carry
      return (← cons s acc, c))
  if_ carry2
    (cons (← bit1) acc2)
    (return acc2)

-- ============================================================
-- SEAL
-- ============================================================

structure CompiledRoutine where
  outputSlot : Nat
  ops        : List String
deriving Repr

-- Seal a routine that reads the input tape and produces one output slot
def seal (build : Build Slot) : Except String CompiledRoutine := do
  let (out, env) ← build.run SlotEnv.initial
  return ⟨out.id, env.ops⟩

-- Seal a routine that also takes explicit slot arguments
def seal1 (build : Slot → Build Slot) : Except String CompiledRoutine := do
  let (out, env) ← (build ⟨0⟩).run { SlotEnv.initial with next := 1 }
  return ⟨out.id, env.ops⟩

def seal2 (build : Slot → Slot → Build Slot) : Except String CompiledRoutine := do
  let (out, env) ← (build ⟨0⟩ ⟨1⟩).run { SlotEnv.initial with next := 2 }
  return ⟨out.id, env.ops⟩

-- ============================================================
-- MAIN
-- ============================================================

def main : IO Unit := do
  let run (name : String) (r : Except String CompiledRoutine) : IO Unit :=
    IO.println s!"\n=== {name} ===" >>
    match r with
    | .error e => IO.println s!"Error: {e}"
    | .ok r    => IO.println (repr r)

  -- Slot operations
  run "new"           (seal new)
  run "true_"         (seal true_)
  run "not(true)"     (seal do not_ (← true_))
  run "not(false)"    (seal do not_ (← false_))
  run "and(T,T)"      (seal do and_ (← true_) (← true_))
  run "and(F,T)"      (seal do and_ (← false_) (← true_))
  run "or(F,T)"       (seal do or_ (← false_) (← true_))
  run "xor(T,T)"      (seal do xor_ (← true_) (← true_))
  run "xor(F,T)"      (seal do xor_ (← false_) (← true_))
  run "append"        (seal2 fun a b => append_ a b)
  run "reverse"       (seal1 fun a => reverse_ a)
  run "snoc"          (seal2 fun a b => snoc a b)
  run "add"           (seal2 fun a b => add a b)

  -- Input tape operations
  run "readCursor"    (seal readCursor)
  run "cursorEmpty"   (seal cursorEmpty)
  run "isFirst"       (seal isFirst_)
  run "isLast"        (seal isLast_)
  run "isRoot"        (seal isRoot_)
  run "foldCursor"    (seal do
    foldCursor (← new) (fun acc => do
      let child ← readCursor
      cons child acc))
