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
  -- compare two tapes, returning non-empty if equal, empty otherwise
  | eq     : TapeIndex → TapeIndex → Operation
  -- branch on tape i: if empty then then_ else else_
  | ite    : TapeIndex → (List Operation) → (List Operation) → Operation
  -- fold over the children of tape l with initial accumulator tape i and body program b
  | fold   : TapeIndex → TapeIndex → (List Operation) → Operation
  -- while tape i is nonempty, run body b with stack extended by acc (the current value of tape i)
  | while_ : TapeIndex → (List Operation) → Operation
deriving Repr

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
    | .cons h t => .some (Data.l (stack[h]'h_wf.1 :: (stack[t]'h_wf.2).asList))
    | .head i => .some (stack[i].asList.headD Data.empty)
    | .tail i => .some (Data.l stack[i].asList.tail)
    | .eq i j => .some (if stack[i]'h_wf.1 == stack[j]'h_wf.2 then dataTrue else dataFalse)
    | .ite i then_ else_ =>
      if stack[i]'h_wf.1 == dataTrue then
        evalProg then_ stack h_wf.2.1
      else
        evalProg else_ stack h_wf.2.2
    | .fold list initial body =>
      goFold (stack[list]'h_wf.1).asList (stack[initial]'h_wf.2.1) stack body h_wf.2.2
    | .while_ i body =>
        -- recurse as long as the head of the returned value is true (the rest is used
        -- to pass data across iterations).
        let F := fun rec d =>
          (evalProg body (d :: stack) h_wf.2).bind fun d =>
            if d.asList.head? == dataTrue then rec d else Data.l d.asList.tail
        Part.fix F (stack[i]'h_wf.1)

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

@[simp]
lemma evalProg_cons
    (op : Operation)
    (rest : Prog)
    (stack : List Data)
    (h_wf : WFProg stack.length (op :: rest)) :
    evalProg (op :: rest) stack h_wf =
      (evalOp stack op h_wf.1).bind fun r => evalProg rest (r :: stack) h_wf.2 := by
  sorry

structure WellFormedProgram where
  prog : Prog
  inputs : ℕ
  h_wf : WFProg inputs prog

def FunType (wf : WellFormedProgram) : Type :=
  let rec of_input_count := fun
    | 0 => Data
    | n + 1 => Data → of_input_count n
  of_input_count wf.inputs

@[simp]
def WellFormedProgram.eval (p : WellFormedProgram)
    (stack : List Data) (h_len : stack.length = p.inputs) : Part Data :=
  evalProg p.prog stack (by simpa [h_len] using p.h_wf)

def WellFormedProgram.Total (p : WellFormedProgram) : Prop :=
  ∀ (stack : List Data) (h_len : stack.length = p.inputs), (p.eval stack h_len).Dom

-- examples:
def prog_true : WellFormedProgram := {
  prog := [.empty, .cons 0 0],
  inputs := 0,
  h_wf := by simp [WFProg, WFOp]
}
def prog_false : WellFormedProgram := {
  prog := [.empty],
  inputs := 0,
  h_wf := by simp [WFProg, WFOp]
}
def prog_negate : WellFormedProgram := {
  prog := [.eq 0 0],
  inputs := 1,
  h_wf := by simp [WFProg, WFOp]
}
lemma prog_true.semantics : prog_true.eval [] rfl = .some dataTrue := by
  simp [prog_true, evalOp]

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
-- When an Operation is about to be emitted, we convert the stored bottom-index
-- to the top-relative index expected by the machine: `currentHeight - 1 - bottomIndex`.
--
-- The builder additionally **carries a proof of well-formedness** in its state, so that
-- `Build.run` returns a `WellFormedProgram` *by construction*, with no exceptions, no
-- `Option`, and no post-hoc decidable check.

/-- A weakening of `WFProg` that holds for the empty program at any `n` (including `0`).
    Used as the in-flight invariant of the builder, since intermediate states may have
    `prog = []` while `n_initial = 0`. -/
def WFProgRaw : ℕ → Prog → Prop
  | _, []         => True
  | n, op :: rest => WFOp n op ∧ WFProgRaw (n + 1) rest

/-- Snoc a single op (well-formed at the post-state height) onto a `WFProgRaw` program. -/
theorem WFProgRaw.append_op :
    ∀ {n : ℕ} {prog : Prog} {op : Operation},
      WFProgRaw n prog → WFOp (n + prog.length) op → WFProgRaw n (prog ++ [op])
  | n, [], op, _, h_op => by
    refine ⟨?_, trivial⟩
    show WFOp n op
    simpa using h_op
  | n, o :: rest, op, h_p, h_op => by
    obtain ⟨h_o, h_rest⟩ := h_p
    refine ⟨h_o, ?_⟩
    have h_op' : WFOp (n + 1 + rest.length) op := by
      have heq : n + (o :: rest).length = n + 1 + rest.length := by
        simp [List.length_cons]; omega
      rw [heq] at h_op
      exact h_op
    exact WFProgRaw.append_op h_rest h_op'

/-- A `WFProgRaw` program with at least one element on the post-execution stack
    (i.e. `n_initial + prog.length > 0`) lifts to a full `WFProg`. -/
theorem WFProgRaw_to_WFProg :
    ∀ {n : ℕ} {prog : Prog}, WFProgRaw n prog → n + prog.length ≠ 0 → WFProg n prog
  | n, [], _, hpos => by simpa using hpos
  | _, _ :: rest, h_p, _ => by
    obtain ⟨h_op, h_rest⟩ := h_p
    refine ⟨h_op, ?_⟩
    apply WFProgRaw_to_WFProg h_rest
    simp

/-- Monad state: the initial stack size, the ops collected so far, and a proof that
    the collected ops form a well-formed program at that initial stack size. -/
structure BuildCtx where
  n_initial : ℕ
  prog : Prog := []
  h_wf : WFProgRaw n_initial prog := by trivial

/-- The current stack height of a build context. -/
@[simp] def BuildCtx.height (c : BuildCtx) : ℕ := c.n_initial + c.prog.length

/-- The builder monad: a state monad over `BuildCtx`. -/
abbrev Build := StateM BuildCtx

/-- A stable reference to a stack slot.  `val` is the slot's bottom-index (oldest = 0).
    `bound` is a snapshot of `currentHeight` at the moment the ref was minted; the
    invariant `val < bound` is what makes the ref usable.  All refs produced by the
    builder API satisfy `bound ≤ currentHeight` from the moment of mint onwards
    (since heights only grow). -/
structure Ref where
  val : ℕ
  bound : ℕ
  h_lt : val < bound

/-- Current stack height (= `n_initial + prog.length`). -/
def Build.currentHeight : Build ℕ := do
  let ctx ← get
  return ctx.height

/-- Extend a `BuildCtx` by appending one well-formed operation. -/
private def BuildCtx.extend (ctx : BuildCtx) (op : Operation) (h_op : WFOp ctx.height op) :
    BuildCtx :=
  { n_initial := ctx.n_initial
    prog := ctx.prog ++ [op]
    h_wf := WFProgRaw.append_op ctx.h_wf (by simpa [BuildCtx.height] using h_op) }

@[simp] theorem BuildCtx.extend_n_initial (ctx : BuildCtx) (op : Operation)
    (h_op : WFOp ctx.height op) : (ctx.extend op h_op).n_initial = ctx.n_initial := rfl

@[simp] theorem BuildCtx.extend_height (ctx : BuildCtx) (op : Operation)
    (h_op : WFOp ctx.height op) : (ctx.extend op h_op).height = ctx.height + 1 := by
  simp [BuildCtx.extend, BuildCtx.height, List.length_append, Nat.add_assoc]

/-- Obtain a `Ref` to an item that already exists in the initial stack.
    `j = 0` is the top of the initial stack, `j = n_initial - 1` is the bottom.
    If `j ≥ n_initial` the resulting `Ref` will be invalid; calls using such a ref will
    silently fall back to emitting `.empty`. -/
def Build.inputRef (j : TapeIndex) : Build Ref := do
  let ctx ← get
  let h := ctx.height
  if hp : ctx.n_initial > 0 then
    -- val = ctx.n_initial - 1 - j (clamped at 0 for j ≥ n_initial); bound = h ≥ n_initial > 0
    let v := if j < ctx.n_initial then ctx.n_initial - 1 - j else 0
    return ⟨v, h, by simp [v, BuildCtx.height]; split <;> sorry⟩
  else
    -- No initial inputs: return a sentinel; can't be used since bound > val always fails.
    return ⟨0, 1, Nat.lt_succ_self _⟩

-- ── Primitive operations ──────────────────────────────────────────────────────

/-- Emit an `.empty` operation; returns a `Ref` to the new (empty) item on top. -/
def Build.empty : Build Ref := do
  let ctx ← get
  let h := ctx.height
  let h_op : WFOp h .empty := trivial
  set (ctx.extend .empty h_op)
  return ⟨h, h + 1, Nat.lt_succ_self _⟩

/-- Emit `.cons h t`. If either ref's bound exceeds the current height (impossible by
    API contract), silently emits `.empty` instead so that the WF invariant is preserved. -/
def Build.cons (h t : Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hh : h.bound ≤ height then
    if ht : t.bound ≤ height then
      have h_hv : h.val < height := Nat.lt_of_lt_of_le h.h_lt hh
      have h_tv : t.val < height := Nat.lt_of_lt_of_le t.h_lt ht
      let i := height - 1 - h.val
      let j := height - 1 - t.val
      let op : Operation := .cons i j
      have hi : i < height := by simp [i]; omega
      have hj : j < height := by simp [j]; omega
      have h_op : WFOp height op := ⟨hi, hj⟩
      set (ctx.extend op h_op)
      return ⟨height, height + 1, Nat.lt_succ_self _⟩
    else
      Build.empty
  else
    Build.empty

/-- Emit `.head r`; falls back to `.empty` on an out-of-bound ref (impossible by contract). -/
def Build.head (r : Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hr : r.bound ≤ height then
    have h_v : r.val < height := Nat.lt_of_lt_of_le r.h_lt hr
    let i := height - 1 - r.val
    let op : Operation := .head i
    have hi : i < height := by simp [i]; omega
    have h_op : WFOp height op := hi
    set (ctx.extend op h_op)
    return ⟨height, height + 1, Nat.lt_succ_self _⟩
  else
    Build.empty

/-- Emit `.tail r`; falls back to `.empty` on an out-of-bound ref (impossible by contract). -/
def Build.tail (r : Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hr : r.bound ≤ height then
    have h_v : r.val < height := Nat.lt_of_lt_of_le r.h_lt hr
    let i := height - 1 - r.val
    let op : Operation := .tail i
    have hi : i < height := by simp [i]; omega
    have h_op : WFOp height op := hi
    set (ctx.extend op h_op)
    return ⟨height, height + 1, Nat.lt_succ_self _⟩
  else
    Build.empty

/-- Emit `.eq r s`; falls back to `.empty` on an out-of-bound ref (impossible by contract). -/
def Build.eq (r s : Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hr : r.bound ≤ height then
    if hs : s.bound ≤ height then
      have h_rv : r.val < height := Nat.lt_of_lt_of_le r.h_lt hr
      have h_sv : s.val < height := Nat.lt_of_lt_of_le s.h_lt hs
      let i := height - 1 - r.val
      let j := height - 1 - s.val
      let op : Operation := .eq i j
      have hi : i < height := by simp [i]; omega
      have hj : j < height := by simp [j]; omega
      have h_op : WFOp height op := ⟨hi, hj⟩
      set (ctx.extend op h_op)
      return ⟨height, height + 1, Nat.lt_succ_self _⟩
    else
      Build.empty
  else
    Build.empty

-- ── Combinators ───────────────────────────────────────────────────────────────

/-- Run a sub-program builder in a fresh context whose initial stack height is `subN`,
    returning the compiled `Prog` together with a `WFProg subN` proof.
    The caller must supply `h_pos : subN > 0` so that the empty-`prog` case is handled.
    `extraRefs` are the `Ref`s for the `subN - h` items prepended on top of the outer
    stack (e.g. `[child, acc]` for `fold`). -/
private def Build.subProg (subN : ℕ) (h_pos : subN > 0)
    (extraRefs : Array Ref) (inner : Array Ref → Build Ref) :
    Build { p : Prog // WFProg subN p } := do
  let init : BuildCtx := { n_initial := subN, prog := [], h_wf := trivial }
  let (_, subCtx) := StateT.run (inner extraRefs) init
  -- Trust that the smart constructors do not change `n_initial`; if some user code
  -- did, we fall back to a trivial WF program of length 1.
  if h_eq : subCtx.n_initial = subN then
    have h_wf_raw : WFProgRaw subN subCtx.prog := h_eq ▸ subCtx.h_wf
    have h_pos' : subN + subCtx.prog.length ≠ 0 := by omega
    return ⟨subCtx.prog, WFProgRaw_to_WFProg h_wf_raw h_pos'⟩
  else
    have h_wf : WFProg subN [Operation.empty] := by
      refine ⟨trivial, ?_⟩
      show subN + 1 ≠ 0
      omega
    return ⟨[Operation.empty], h_wf⟩

/-- Build the bottom-index `Ref`s for the `extra` items prepended on top of the outer
    stack `h` when entering a sub-builder.  Returns refs in order
    `[topmost prepended, …, bottommost prepended]`. -/
private def Build.extraRefs (h extra : ℕ) : Array Ref :=
  (Array.range extra).map fun k =>
    let v := h + extra - 1 - k
    have h_lt : v < h + extra := by simp [v]; omega
    ⟨v, h + extra, h_lt⟩

/-- Branch on `cond`: if `cond == dataTrue` run `then_`, else run `else_`.
    Both branches see the same outer stack.  Each branch must return the `Ref` it
    wants as the result. -/
def Build.ite (cond : Ref) (then_ else_ : Build Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hc : cond.bound ≤ height then
    have h_v : cond.val < height := Nat.lt_of_lt_of_le cond.h_lt hc
    let i := height - 1 - cond.val
    have hi : i < height := by simp [i]; omega
    have h_pos : height > 0 := by omega
    let ⟨thenProg, h_then⟩ ← Build.subProg height h_pos (Build.extraRefs height 0) (fun _ => then_)
    let ⟨elseProg, h_else⟩ ← Build.subProg height h_pos (Build.extraRefs height 0) (fun _ => else_)
    let op : Operation := .ite i thenProg elseProg
    have h_op : WFOp height op := ⟨hi, h_then, h_else⟩
    set (ctx.extend op h_op)
    return ⟨height, height + 1, Nat.lt_succ_self _⟩
  else
    Build.empty

/-- Fold over the children of `list_`, starting with accumulator `acc_`, using `body`.
    `body` receives `(child, acc)` as `Ref`s; outer `Ref`s remain valid unchanged. -/
def Build.fold (list_ acc_ : Ref) (body : Ref → Ref → Build Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hl : list_.bound ≤ height then
    if ha : acc_.bound ≤ height then
      have h_lv : list_.val < height := Nat.lt_of_lt_of_le list_.h_lt hl
      have h_av : acc_.val < height := Nat.lt_of_lt_of_le acc_.h_lt ha
      let li := height - 1 - list_.val
      let ai := height - 1 - acc_.val
      have hli : li < height := by simp [li]; omega
      have hai : ai < height := by simp [ai]; omega
      have h_pos : height + 2 > 0 := by omega
      let ⟨bodyProg, h_body⟩ ← Build.subProg (height + 2) h_pos
        (Build.extraRefs height 2) (fun extra => body extra[0]! extra[1]!)
      let op : Operation := .fold li ai bodyProg
      have h_op : WFOp height op := ⟨hli, hai, h_body⟩
      set (ctx.extend op h_op)
      return ⟨height, height + 1, Nat.lt_succ_self _⟩
    else
      Build.empty
  else
    Build.empty

/-- While `cond_` is nonempty, run `body`.  `body` receives one `Ref` for the current
    accumulator (= the current value of `cond_` on top of the outer stack). -/
def Build.while_ (cond_ : Ref) (body : Ref → Build Ref) : Build Ref := do
  let ctx ← get
  let height := ctx.height
  if hc : cond_.bound ≤ height then
    have h_v : cond_.val < height := Nat.lt_of_lt_of_le cond_.h_lt hc
    let i := height - 1 - cond_.val
    have hi : i < height := by simp [i]; omega
    have h_pos : height + 1 > 0 := by omega
    let ⟨bodyProg, h_body⟩ ← Build.subProg (height + 1) h_pos
      (Build.extraRefs height 1) (fun extra => body extra[0]!)
    let op : Operation := .while_ i bodyProg
    have h_op : WFOp height op := ⟨hi, h_body⟩
    set (ctx.extend op h_op)
    return ⟨height, height + 1, Nat.lt_succ_self _⟩
  else
    Build.empty

-- ── Running the builder ───────────────────────────────────────────────────────

/-- Run a builder that starts with `n_initial` pre-existing stack items, producing a
    `WellFormedProgram` *by construction*.  If the user's builder produces no ops and
    `n_initial = 0`, an `.empty` op is appended so that the result is always a
    syntactically valid `WFProg` (which requires the post-execution stack to be
    non-empty). -/
def Build.run (n_initial : ℕ) (b : Build Ref) : WellFormedProgram :=
  let init : BuildCtx := { n_initial, prog := [], h_wf := trivial }
  let (_, ctx) := StateT.run b init
  if h_pos : ctx.height ≠ 0 then
    ⟨ctx.prog, ctx.n_initial, WFProgRaw_to_WFProg ctx.h_wf (by simpa [BuildCtx.height] using h_pos)⟩
  else
    -- height = 0 ⇒ n_initial = 0 ∧ prog = []; emit a sentinel `.empty` to satisfy WFProg.
    let extended := ctx.extend .empty trivial
    have h_pos' : extended.n_initial + extended.prog.length ≠ 0 := by
      simp [extended, BuildCtx.extend, List.length_append]
    ⟨extended.prog, extended.n_initial, WFProgRaw_to_WFProg extended.h_wf h_pos'⟩

/-- Convenience: `Build.run` for programs that take no initial input. -/
def Build.runFresh (b : Build Ref) : WellFormedProgram := Build.run 0 b


def funFalse : WellFormedProgram := Build.runFresh do
  Build.empty

def funTrue : WellFormedProgram := Build.runFresh do
  let a ← Build.empty
  Build.cons a a

#eval funFalse.prog
#eval funTrue.prog
