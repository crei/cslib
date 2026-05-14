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
-- fold incurs space of init plus the max of the space of the step function
-- this is the crucial point that allows us to build space-efficient algorithms:
-- We implicitly overwrite the old accumulator value even though there is no
-- explicit "overwrite" or "free" operation.

abbrev dataTrue := Data.l [Data.l []]
abbrev dataFalse := Data.l []


-- Interpreter:
-- It returns Part.none if the program does not terminate and Part.some Option.none if the
-- program is not well-formed.
mutual
  def evalOp (stack : List Data) (op : Operation) (h_wf : WFOp stack.length op)
      : Part Data := match op with
    | .empty => .some Data.empty
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
  intro data h_len
  induction h : p.prog generalizing data with
  | nil =>
    simp [WellFormedProgram.eval, evalProg, h]
  | cons op rest ih =>
    simp [WellFormedProgram.eval, h]
    cases op with
    | empty =>
      unfold evalProg evalOp
      simp
      sorry
    | cons h t => sorry
    | head i => sorry
    | tail i => sorry
    | eq i j => sorry
    | ite i then_ else_ => sorry
    | fold l i body => sorry
    | while_ i body => sorry


-- Now the most important part: If a program is total, and well-formed we can talk about the
-- function computed by the program - this is something that was not really possible with my old
-- design:

-- With these at hand, we can define simp lemmas and thus auto-derive semantics
-- and maybe even resource requirements of programs:

-- @[simp]
-- theorem evalFold_eq_foldl
--     (stack : List Data) (l i : ℕ) (hl : l < stack.length) (hi : i < stack.length)
--     (body : Prog) (h : WellFormedTotal body)
--     (rest : Prog) :
--     evalProg ((.fold l i body) :: rest) stack =
--     .some (some (stack ++ [(stack[l].asList.foldl
--       (fun (acc : Data) (el : Data) => progFun body h (stack ++ [el, acc]))
--       stack[i])])) := by
--   sorry


-- ================= Builder monad
--
-- The problem with writing programs directly is that tape indices are top-relative
-- (0 = newest item), so every push shifts all existing indices by 1.
--
-- The builder monad solves this by working with *bottom-indexed* references internally.
-- A `Ref` stores the absolute position of a stack slot counting from the bottom (oldest = 0).
-- Bottom-indices are stable: pushing a new item never changes any existing Ref.
-- When an Operation is about to be emitted, `Ref.toIdx` converts the stored bottom-index
-- to the top-relative index expected by the machine: `currentHeight - 1 - bottomIndex`.
--
-- Sub-program builders (for ite/fold/while_) are created with `n_initial` set to the
-- outer stack height at the point of the combinator plus any extra items prepended by
-- the combinator (2 for fold, 1 for while_). Outer Refs pass into sub-builders unchanged
-- because their bottom-indices remain valid.

/-- Monad state: the initial stack size for this (sub-)program and the ops collected so far. -/
structure BuildCtx where
  n_initial : ℕ
  prog : Prog := []

/-- The builder monad. -/
abbrev Build (α : Type) := StateT BuildCtx (Except String) α

/-- A stable reference to a stack slot.  The value is the slot's bottom-index:
    position from the bottom of the conceptual stack (oldest item = 0).
    Using `abbrev` so all `ℕ` instances (LE, Sub, ToString, …) are inherited. -/
abbrev Ref := ℕ

/-- Current stack height (= n_initial + number of ops emitted so far). -/
def Build.currentHeight : Build ℕ := do
  let ctx ← get
  return ctx.n_initial + ctx.prog.length

/-- Convert a stable `Ref` to its current top-relative index (for use in Operations).
    Throws if the ref is out of range. -/
def Ref.toIdx (r : Ref) : Build TapeIndex := do
  let h ← Build.currentHeight
  if r ≥ h then throw s!"Ref {r} is out of range (current height {h})"
  return h - 1 - r

/-- Emit one operation and return a `Ref` to the slot it creates. -/
private def emit (op : Operation) : Build Ref := do
  let ctx ← get
  let b : Ref := ctx.n_initial + ctx.prog.length
  set { ctx with prog := ctx.prog ++ [op] }
  return b

/-- Obtain a `Ref` to an item that already exists in the initial stack.
    `j = 0` is the top of the initial stack, `j = n_initial - 1` is the bottom. -/
def Build.inputRef (j : TapeIndex) : Build Ref := do
  let ctx ← get
  if j ≥ ctx.n_initial then
    throw s!"inputRef {j} is out of range (n_initial = {ctx.n_initial})"
  return ctx.n_initial - 1 - j

-- ── Primitive operations ──────────────────────────────────────────────────────

def Build.empty : Build Ref := emit .empty

def Build.cons (h t : Ref) : Build Ref := do emit (.cons (← h.toIdx) (← t.toIdx))

def Build.head (r : Ref) : Build Ref := do emit (.head (← r.toIdx))

def Build.tail (r : Ref) : Build Ref := do emit (.tail (← r.toIdx))

def Build.eq (r s : Ref) : Build Ref := do emit (.eq (← r.toIdx) (← s.toIdx))

-- ── Combinators ───────────────────────────────────────────────────────────────

/-- Run a sub-program builder in a fresh context whose initial stack = the current
    outer stack height plus `extra` items prepended on top.
    Returns the compiled `Prog`.  The `Ref`s returned by `inner` are bottom-indices
    valid in the sub-context; `extraRefs` are the `Ref`s for the `extra` prepended
    items (index 0 = topmost prepended item). -/
private def Build.subProg (extra : ℕ) (inner : Array Ref → Build Ref)
    : Build Prog := do
  let h ← Build.currentHeight
  let n_initial_inner := h + extra
  -- Bottom-indices for the `extra` prepended items (top item = h + extra - 1, …)
  let extraRefs : Array Ref := (Array.range extra).map (fun k => h + extra - 1 - k)
  let (_, innerCtx) ←
    liftM (StateT.run (inner extraRefs) ({ n_initial := n_initial_inner } : BuildCtx))
  return innerCtx.prog

/-- Branch on `cond`: if `cond == dataTrue` run `then_`, else run `else_`.
    Both branches receive no extra prepended items (same stack as the outer context
    at the ite op).  Each branch builder must return the `Ref` it wants as the result. -/
def Build.ite (cond : Ref) (then_ else_ : Build Ref) : Build Ref := do
  let ci ← cond.toIdx
  let thenProg ← Build.subProg 0 (fun _ => then_)
  let elseProg ← Build.subProg 0 (fun _ => else_)
  emit (.ite ci thenProg elseProg)

/-- Fold over the children of `list_`, starting with accumulator `acc_`, using `body`.
    `body` receives two `Ref`s: the current child (index 0) and the current accumulator
    (index 1), plus all outer `Ref`s remain valid unchanged. -/
def Build.fold (list_ acc_ : Ref) (body : Ref → Ref → Build Ref) : Build Ref := do
  let li ← list_.toIdx
  let ai ← acc_.toIdx
  let bodyProg ← Build.subProg 2 (fun extra => body extra[0]! extra[1]!)
  emit (.fold li ai bodyProg)

/-- While `cond_` is nonempty, run `body`.
    `body` receives one `Ref` for the current accumulator (= current value of `cond_`). -/
def Build.while_ (cond_ : Ref) (body : Ref → Build Ref) : Build Ref := do
  let ci ← cond_.toIdx
  let bodyProg ← Build.subProg 1 (fun extra => body extra[0]!)
  emit (.while_ ci bodyProg)

-- ── Running the builder ───────────────────────────────────────────────────────

/-- Run a builder that starts with `n_initial` pre-existing stack items.
    The builder returns the `Ref` it considers the result.
    `run` checks that the result `Ref` is the top of the final stack (top-index 0),
    i.e., the result is the last emitted op, and returns the completed `Prog`. -/
def Build.run (n_initial : ℕ) (b : Build Ref) : Except String Prog := do
  let (resultRef, ctx) ← StateT.run b { n_initial }
  let finalHeight := n_initial + ctx.prog.length
  if finalHeight = 0 then throw "empty program with empty initial stack"
  let resultIdx := finalHeight - 1 - resultRef
  if resultIdx ≠ 0 then
    throw s!"result Ref is not at the top of the stack (top-index {resultIdx}, expected 0)"
  return ctx.prog

/-- `Build.run` for programs that take no initial input (n_initial = 0 would violate
    WFProg at the empty case, so callers must ensure at least one op is emitted). -/
def Build.runFresh (b : Build Ref) : Except String Prog := Build.run 0 b
