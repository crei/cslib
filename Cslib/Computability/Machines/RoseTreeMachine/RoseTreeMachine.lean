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

abbrev Data.empty := Data.l []

abbrev Data.asList
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
  -- head of the data if it exists, or empty otherwise
  | head   : TapeIndex → Operation
  -- tail of the data
  | tail   : TapeIndex → Operation
  -- compare two tapes, returning empty if equal, nonempty otherwise
  | eq     : TapeIndex → TapeIndex → Operation
  -- branch on tape i: if empty then then_ else else_
  | ite    : TapeIndex → (List Operation) → (List Operation) → Operation
  -- fold over the children of tape l with initial accumulator tape i and body program b
  | fold   : TapeIndex → TapeIndex → (List Operation) → Operation
  -- while tape i is nonempty, run body b with stack extended by acc (the current value of tape i)
  | while_ : TapeIndex → (List Operation) → Operation

abbrev Prog := List Operation

mutual
  /-- `WFOp n op` states that `op` is well-formed when the current stack has `n` entries.
      All tape indices must be in bounds, and sub-programs must be well-formed at the
      appropriate derived stack heights. -/
  def WFOp (n : ℕ) : Operation → Prop
    | .empty      => True
    | .copy i     => i < n
    | .cons h t   => h < n ∧ t < n
    | .head i     => i < n
    | .tail i     => i < n
    | .eq i j     => i < n ∧ j < n
    | .ite i t e  => i < n ∧ WFProg n t ∧ WFProg n e
    | .fold l i b => l < n ∧ i < n ∧ WFProg (n + 2) b
    | .while_ i b => i < n ∧ WFProg (n + 1) b

  /-- `WFProg n p` states that `p` is well-formed given an initial stack of size `n`.
      Since each operation pushes exactly one value, the k-th operation (0-indexed) sees
      a stack of size `n + k`, so the tail of the program is checked at height `n + 1`. -/
  def WFProg : ℕ → Prog → Prop
    | n, []         => n ≠ 0 -- we require this because a program has to return a result.
    | n, op :: rest => WFOp n op ∧ WFProg (n + 1) rest
end

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

abbrev dataTrue := Data.l [Data.l []]
abbrev dataFalse := Data.l []


-- Interpreter:
-- It returns Part.none if the program does not terminate and Part.some Option.none if the
-- program is not well-formed.
mutual
  def evalOp (stack : List Data) (op : Operation) (h_wf : WFOp stack.length op) : Part Data := match op with
    | .empty => .some Data.empty
    | .copy i => .some stack[i]
    | .cons h t =>
      let ⟨h₁, h₂⟩ := h_wf
      .some (Data.l (stack[h] :: stack[t].asList))
    | .head i => .some (stack[i].asList.headD Data.empty)
    | .tail i => .some (Data.l stack[i].asList.tail)
    | .eq i j =>
      let ⟨h₁, h₂⟩ := h_wf
      .some (if stack[i] == stack[j] then dataTrue else dataFalse)
    | .ite i then_ else_ =>
       let ⟨h₁, h₂, h₃⟩ := h_wf
       if stack[i] == dataTrue then evalProg then_ stack h₂ else evalProg else_ stack h₃
    | .fold list initial body =>
       let ⟨h₁, h₂, h₃⟩ := h_wf
       goFold stack[list].asList stack[initial] stack body h₃
    | .while_ i body =>
       let ⟨h₁, h₂⟩ := h_wf
        -- recurse as long as the head of the returned value is true (the rest is used
        -- to pass data across iterations).
        let F := fun rec d =>
          (evalProg body (d :: stack) h₂).bind fun d =>
            if d.asList.head? == dataTrue then rec d else Data.l d.asList.tail
        Part.fix F stack[i]

  def goFold (items : List Data) (acc : Data) (stack : List Data) (body : Prog)
      (h_wf : WFProg (stack.length + 2) body) : Part Data :=
    match items with
    | []      => .some acc
    | c :: cs =>
      -- Put the item and the accumulator on two new tapes and run the program.
      -- take the contents of the last tape as the result / new accumulator.
      (evalProg body (c :: acc :: stack) h_wf).bind fun acc' => goFold cs acc' stack body h_wf

  def evalProg (prog : Prog) (stack : List Data) (h_wf : WFProg stack.length prog) : Part Data :=
    match prog with
      | []           => .some (stack.head (by grind [WFProg]))
      | op :: rest   =>
        let ⟨h_wf_head, h_wf_tail⟩ := h_wf
        (evalOp stack op h_wf_head).bind fun r => evalProg rest (r :: stack) h_wf_tail
end

structure WellFormedProgram where
  prog : Prog
  inputs : ℕ
  h_wf : WFProg inputs prog

def FunType (wf : WellFormedProgram) : Type :=
  let rec of_input_count := fun
    | 0 => Data
    | n + 1 => Data → of_input_count n
  of_input_count wf.inputs

def WellFormedProgram.eval (h_wf : WellFormedProgram)
    (stack : List Data) (h_len : stack.length = h_wf.inputs) : Part Data :=
  evalProg h_wf.prog stack (by simpa [h_len] using h_wf.h_wf)

def WellFormedProgram.Total (wfp : WellFormedProgram) : Prop :=
  ∀ (stack : List Data) (h_len : stack.length = wfp.inputs), (wfp.eval stack h_len).Dom


mutual
  def WhileFreeOp : Operation → Prop
    | .while_ _ _ => False
    | .fold _ _ b => WhileFreeProg b
    | _           => True

  def WhileFreeProg : Prog → Prop
    | []         => True
    | op :: rest => WhileFreeOp op ∧ WhileFreeProg rest
end

theorem whileFree_total (p : WellFormedProgram) (hwf : WhileFreeProg p.prog) : p.Total := by

  sorry

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
