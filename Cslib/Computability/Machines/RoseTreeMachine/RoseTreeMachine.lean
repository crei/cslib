import Mathlib.Data.Part
import Mathlib.Control.Fix
import Mathlib.Tactic
import Std

-- This is a proposal to define a machine model and related time and space measure
-- such that it is linearly space- and polynomially time-related to multi-tape Turing machines.

-- The goal would be that the machine model is flexible enough to implement algorithms easily,
-- but still close enough to Turing machines to allow defining logspace and even loglogspace.

-- The machine as defined below will allow stateless / pure functional programs.
-- If we store the input tape position as a number, we should be able to define logspace.
-- In order to go down to loglogspace, we need to use the input tape head as a "pointer"
-- and cannot count its position. This could be doable as well, but requires a more stateful
-- model at least for the input tape. The input tape is currently not modeled, but I have some
-- plans to define actions on the input tape as further elementary operations.

-- The main insight over my current work is that it does not hurt to
-- (1) create a new tape for every elementary operation (the program size is constant, so the number
--     of tapes is constant)
-- (2) disallow modifications to existing tapes (work tape space has been spent, it is fine
--     to copy it finitely often
-- (3) if we have a built-in `fold` operation, we should be able to implement the required
--     operations at linear space overhead, because the fold operation implicitly re-uses the
--     space used by the accumulator.



-- ================= Data structure



-- Rose-tree data structure, it allows us to
-- 1. map most of Lean's data structures in a "natural" manner
-- 2. define a "fold" operation
inductive Data where
  | l : List Data → Data
deriving Repr, BEq

def Data.asList
  | Data.l xs => xs

abbrev TapeIndex := ℕ


-- ================= Operations and programs

-- The machine is a "stack" machine, where each stack item represents a tape and holds a Data value.
-- Each operation creates a new stack entry (a new tape) and can read from previous
-- entries by index.

-- TODO: For the combinators (ite, fold, while_) I am not yet sure if we can/should restrict the
-- inner programs to return exactly one tape. Unrelated to that, the inner programs of `fold` and
-- `while_` are able to create "temporary" slots.

inductive Operation where
  -- create a new tape initialized with `Data.l []`
  | empty  : Operation
  -- copy tape i to a new tape -- not sure if this is needed
  | copy   : TapeIndex → Operation
  -- cons tape h and tape t to a new tape (h :: t)
  | cons   : TapeIndex → TapeIndex → Operation
  -- compare two tapes, returning empty if equal, nonempty otherwise
  | eq     : TapeIndex → TapeIndex → Operation
  -- branch on tape i: if empty then then_ else else_
  | ite    : TapeIndex → (List Operation) → (List Operation) → Operation
  -- fold over the children of tape l with initial accumulator tape i and body program b
  | fold   : TapeIndex → TapeIndex → (List Operation) → Operation
  -- while tape i is nonempty, run body b with stack extended by acc (the current value of tape i)
  | while_ : TapeIndex → (List Operation) → Operation

abbrev Prog := List Operation


-- TODO define a well-formedness Prop that ensures that tape indices are all in bounds.

-- One could define a monadic builder-pattern that handles tape index allocation:
-- def filter (a : TapeIndex) (predicate : TapeIndex → Build TapeIndex) : Build TapeIndex := do
--   fold a (← empty) (fun child acc => do
--     ite (← predicate child)
--       (cons child acc)
--       (return acc))


-- TODO define space measure:
-- elementary operations incur the size of their output as additional space
-- fold incurs space of init plus the max of the space of the step function - this is the crucial point
-- that allows us to build space-efficient algorithms: We implicitly overwrite the old
-- accumulator value even though there is no explicit "overwrite" or "free" operation.

-- Interpreter:
-- It returns Part.none if the program does not terminate and Part.some Option.none if the
-- program is not well-formed.
mutual
  def evalOp (stack : List Data) (op : Operation) : Part (Option (List Data)) := match op with
    | .empty      => .some (some (stack ++ [Data.l []]))
    | .copy  i    => .some (do stack ++ [← stack[i]?])
    | .cons  h t  =>
        .some (do
          let hv ← stack[h]?
          let tv ← stack[h]?
          return stack ++ [Data.l (hv :: tv.asList)])
    | .eq i j =>
        .some (do
          let a ← stack[i]?
          let b ← stack[j]?
          stack ++ [if a == b then Data.l [] else Data.l [Data.l []]])
    | .ite i then_ else_ =>
        match stack[i]? with
        | none     => .some none
        | some cond =>
          if cond == Data.l [] then evalProg then_ stack else evalProg else_ stack
    | .fold  l i body => match (stack[l]?, stack[i]?) with
        | (some list, some initial) =>
          (goFold list.asList initial stack body).map (fun result => result.map (stack ++ [·]))
        | _ => .some none
    | .while_ i body =>
        match stack[i]? with
        | none     => .some none
        | some acc => sorry -- use Part.fix


  def goFold (children : List Data) (acc : Data)
      (stack : List Data) (body : Prog) : Part (Option Data) :=
    match children with
    | []      => .some (some acc)
    | c :: cs =>
      -- Put the item and the accumulator on two new tapes and run the program.
      -- take the contents of the last tape as the result / new accumulator.
      (evalProg body (stack ++ [c, acc])).bind fun result =>
        match result >>= (·.getLast?) with
        | none      => .some none
        | some acc' => goFold cs acc' stack body

  def evalProg (p : Prog) (stack : List Data) : Part (Option (List Data)) := match p with
    | []           => .some (some stack)
    | op :: rest   =>
      (evalOp stack op).bind fun result =>
        match result with
        | none   => .some none
        | some stack' => evalProg rest stack'
end

-- `Part` is annoying but unfortunately needed. Since we are dealing with complexity, all programs
-- should compute total functions, so we define totality as a prop. Of course, any program that
-- does not use while_ is total. This can be hopefully derived structurally using simp lemmas and thus
-- should auto-solve in simp lemmas.

mutual
  def WhileFreeOp : Operation → Prop
    | .while_ _ _ => False
    | .fold _ _ b => WhileFreeProg b
    | _           => True

  def WhileFreeProg : Prog → Prop
    | []         => True
    | op :: rest => WhileFreeOp op ∧ WhileFreeProg rest
end

def ComputesTotalFunction (prog : Prog) : Prop :=
  ∀ (stack : List Data), (evalProg prog stack).Dom

theorem whileFree_total (prog : Prog) (hwf : WhileFreeProg prog) :
    ComputesTotalFunction prog := by sorry

def WellFormedTotal (prog : Prog) : Prop :=
  ∃ (h_total : ComputesTotalFunction prog), ∀ stack : List Data,
    ((evalProg prog stack).get (h_total stack)).isSome

-- Now the most important part: If a program is total, and well-formed we can talk about the
-- function computed by the program - this is something that was not really possible with my old
-- design:

def progFun (prog : Prog) (h_wft : WellFormedTotal prog) (stack : List Data) : Data :=
    -- TODO prove that the stack size increases by at least 1 or similar
  (((evalProg prog stack).get (h_wft.1 stack)).get (h_wft.2 stack)).getLast sorry

-- With these at hand, we can define simp lemmas and thus auto-derive semantics
-- and maybe even resource requirements of programs:

@[simp]
theorem evalFold_eq_foldl
    (stack : List Data) (l i : ℕ) (hl : l < stack.length) (hi : i < stack.length)
    (body : Prog) (h : WellFormedTotal body)
    (rest : Prog) :
    evalProg ((.fold l i body) :: rest) stack =
    .some (some (stack ++ [(stack[l].asList.foldl
      (fun (acc : Data) (el : Data) => progFun body h (stack ++ [el, acc]))
      stack[i])])) := by
  sorry


abbrev Build (α : Type) := StateT Prog (Except String) α

def appendOp (op : Operation) : Build TapeIndex := do
  let prog ← get
  let idx := prog.length
  set (prog ++ [op])
  return idx

def empty : Build TapeIndex := appendOp .empty

def copy (i : TapeIndex) : Build TapeIndex := appendOp (.copy i)

def cons (h t : TapeIndex) : Build TapeIndex := appendOp (.cons h t)

def eq (i j : TapeIndex) : Build TapeIndex := appendOp (.eq i j)

def ite_ (cond : TapeIndex) (then_ else_ : Prog) : Build TapeIndex := do
  appendOp (.ite cond (getThenProg) (getElseProg))
