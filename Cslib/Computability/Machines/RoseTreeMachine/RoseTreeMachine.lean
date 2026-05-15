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

--- Encoding length of d.
def Data.size : Data → ℕ
  | Data.l xs => 2 + (xs.map Data.size |>.sum)

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
  | fold   : (List Operation) → TapeIndex → TapeIndex → Operation
  -- while tape i is nonempty, run body b with stack extended by acc (the current value of tape i)
  | while_ : TapeIndex → (List Operation) → Operation
  -- call executes a sub-program and returns its stack top. This is not strictly needed, but
  -- makes it easier to write programs.
  | call : (List Operation) → Operation
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
    | .fold b i l => l < n ∧ i < n ∧ WFProg (n + 2) b
    | .while_ i b => i < n ∧ WFProg (n + 1) b
    | .call b => WFProg n b

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

mutual
  --- Evaluate a single operation and return the return value, additional time and additional space.
  def meteredEvalOp (stack : List Data) (op : Operation) (h_wf : WFOp stack.length op) :
      Part (Data × ℕ × ℕ) :=
    match op with
    | .empty => .some (Data.empty, 1, 1)
    | .cons h t =>
      let result := Data.l (stack[h]'h_wf.1 :: (stack[t]'h_wf.2).asList)
      .some (result, 1 + result.size, 1 + result.size)
    | .head i =>
      let result := stack[i].asList.headD Data.empty
      .some (result, 1 + result.size, 1 + result.size)
    | .tail i =>
      let result := Data.l stack[i].asList.tail
      .some (result, 1 + result.size, 1 + result.size)
    | .eq i j => .some
      (if stack[i]'h_wf.1 == stack[j]'h_wf.2 then dataTrue else dataFalse,
      1 + (min (stack[i]'h_wf.1).size (stack[j]'h_wf.2).size),
      1)
    | .ite i then_ else_ =>
      (if stack[i]'h_wf.1 == dataTrue then
        meteredEvalProg then_ stack h_wf.2.1
      else
        meteredEvalProg else_ stack h_wf.2.2).map (fun (r, t, s) => (r, 1 + t, s))
    | .fold body initial list =>
      -- Time: 1 + Σ_iterations (1 + body_time).
      -- Space: init.size + max_iterations(body_space).
      (goMeteredFold (stack[list]'h_wf.1).asList (stack[initial]'h_wf.2.1) stack body h_wf.2.2)
    | .while_ i body =>
      -- Same accounting as fold: time sums per-iteration costs (each iteration adds 1 + body_time);
      -- space is init.size plus the max body space across iterations.
      let init := stack[i]'h_wf.1
      let F : ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) →
              (Data × ℕ × ℕ) → Part (Data × ℕ × ℕ) :=
        fun rec d_ts =>
          let (d, t, s) := d_ts
          (meteredEvalProg body (d :: stack) h_wf.2).bind fun (d', tBody, sBody) =>
            let t' := t + 1 + tBody
            let s' := max s sBody
            if d'.asList.head? == .some dataTrue then rec (d', t', s')
            else .some (Data.l d'.asList.tail, t', s')
      (Part.fix F (init, 0, 0)).map fun (r, t, s) => (r, 1 + t, init.size + s)
    | .call body => meteredEvalProg body stack h_wf

  /-- Metered analogue of `goFold`: walks the items, threading the accumulator and accumulating
      `(sum of (1 + body_time), max of body_space)` across iterations. -/
  def goMeteredFold (items : List Data) (acc : Data) (stack : List Data) (body : Prog)
      (h_wf : WFProg (stack.length + 2) body) : Part (Data × ℕ × ℕ) :=
    match items with
    | []      => .some (acc, acc.size, acc.size)
    | c :: cs =>
      (meteredEvalProg body (c :: acc :: stack) h_wf).bind fun (acc', tBody, sBody) =>
        (goMeteredFold cs acc' stack body h_wf).map fun (r, t, s) =>
          (r, 1 + tBody + t, max sBody s)

  @[simp]
  def meteredEvalProg (prog : Prog) (stack : List Data) (h_wf : WFProg stack.length prog) :
      Part (Data × ℕ × ℕ) :=
    match prog with
    | [] => .some (stack.head (by grind [WFProg]), 0, 0)
    | op :: rest => do
      let (r, opTime, opSpace) ← meteredEvalOp stack op h_wf.1
      let (r, time, space) ← meteredEvalProg rest (r :: stack) h_wf.2
      (r, opTime + time, opSpace + space)

end

@[simp]
lemma goMeteredFold_nil (acc : Data) (stack : List Data) (h_wf : WFProg (stack.length + 2) body) :
    goMeteredFold [] acc stack body h_wf = .some (acc, acc.size, acc.size) := by
  simp [goMeteredFold]

@[simp]
lemma goMeteredFold_cons (head : Data) (tail : List Data) (acc : Data) (stack : List Data)
    (h_wf : WFProg (stack.length + 2) body) :
    goMeteredFold (head :: tail) acc stack body h_wf =
      (meteredEvalProg body (head :: acc :: stack) h_wf).bind fun (acc', tBody, sBody) =>
        (goMeteredFold tail acc' stack body h_wf).map fun (r, t, s) =>
          (r, 1 + tBody + t, max sBody s) := by
  simp [goMeteredFold]

structure WellFormedProgram (inputs : ℕ) where
  prog : Prog
  h_wf : WFProg inputs prog

--- The output stack size of the program.
abbrev WellFormedProgram.stackSize {inputs : ℕ} (p : WellFormedProgram inputs) : ℕ := inputs + p.prog.length

def FunType (inputs : ℕ) : Type := match inputs with
  | 0 => Data
  | n + 1 => Data → FunType n

@[simp]
def WellFormedProgram.eval {inputs : ℕ} (p : WellFormedProgram inputs)
    (stack : List Data) (h_len : stack.length = inputs) : Part Data :=
  (meteredEvalProg p.prog stack (by simpa [h_len] using p.h_wf)).map fun (d, _, _) => d

@[simp]
def WellFormedProgram.time {inputs : ℕ} (p : WellFormedProgram inputs)
    (stack : List Data) (h_len : stack.length = inputs) : Part ℕ :=
  (meteredEvalProg p.prog stack (by simpa [h_len] using p.h_wf)).map fun (_, t, _) => t

@[simp]
def WellFormedProgram.space {inputs : ℕ} (p : WellFormedProgram inputs)
    (stack : List Data) (h_len : stack.length = inputs) : Part ℕ :=
  (meteredEvalProg p.prog stack (by simpa [h_len] using p.h_wf)).map fun (_, _, s) => s

def WellFormedProgram.Total {inputs : ℕ} (p : WellFormedProgram inputs) : Prop :=
  ∀ (stack : List Data) (h_len : stack.length = inputs), (p.eval stack h_len).Dom

def WellFormedProgram.as_fun {inputs : ℕ} (p : WellFormedProgram inputs) (h_total : p.Total) :
    FunType inputs :=
  sorry

-- examples:
def prog_true : WellFormedProgram 0 := {
  prog := [.empty, .cons 0 0],
  h_wf := by simp [WFProg, WFOp]
}
def prog_false : WellFormedProgram 0 := {
  prog := [.empty],
  h_wf := by simp [WFProg, WFOp]
}
def prog_negate : WellFormedProgram 1 := {
  prog := [.eq 0 0],
  h_wf := by simp [WFProg, WFOp]
}
lemma prog_true.semantics : prog_true.eval [] rfl = .some dataTrue := by
  simp [prog_true, meteredEvalOp]

lemma prog_true.space : prog_true.space [] rfl = .some 6 := by
  simp [prog_true, meteredEvalOp, Data.size]

lemma prog_true.time : prog_true.time [] rfl = .some 6 := by
  simp [prog_true, meteredEvalOp, Data.size]

def WellFormedProgram.append {in₁ in₁ : ℕ}
    (p₁ : WellFormedProgram in₁) (p₂ : WellFormedProgram in₂) (h_le : in₂ ≤ p₁.stackSize) :
    WellFormedProgram in₁ :=
  { prog := p₁.prog ++ p₂.prog, h_wf := by sorry }

class DataEncode (α : Type) where
  encode : α → Data
  h_inj : encode.Injective

instance : DataEncode Bool where
  encode b := if b then dataTrue else dataFalse
  h_inj := by intros a b h_eq; grind

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  h_inj := by sorry

instance (α : Type) [DataEncode α] : DataEncode (Option α) where
  encode := fun
    | none => Data.l []
    | some x => Data.l [DataEncode.encode x]
  h_inj := by sorry

instance : DataEncode ℕ where
  encode x := DataEncode.encode (Nat.bits x)
  h_inj := by sorry

def RunsInSpace {inputs : ℕ} (p : WellFormedProgram inputs) (s : ℕ → ℕ) : Prop :=
  ∃ s₁ s₂, ∀ x, (h_l : x.length = inputs) → ∃ s' ≤ s₁ * (s (Data.l x).size) + s₂,
  p.space x h_l = .some s'

def RunsInTime {inputs : ℕ} (p : WellFormedProgram inputs) (t : ℕ → ℕ) : Prop :=
  ∃ t₁ t₂, ∀ x, (h_l : x.length = inputs) → ∃ t' ≤ t₁ * (t (Data.l x).size) + t₂,
  p.time x h_l = .some t'

def ComputesInTimeAndSpace {α β : Type} [DataEncode α] [DataEncode β]
  (p : WellFormedProgram 1) (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ t₁ t₂ s₁ s₂,
    (∀ x : α, p.eval [DataEncode.encode x] rfl = .some (DataEncode.encode (f x))) ∧
    (∀ x : α, ∃ t' ≤ t₁ * (t (DataEncode.encode x).size) + t₂,
        p.time [DataEncode.encode x] rfl = .some t') ∧
    (∀ x : α, ∃ s' ≤ s₁ * (s (DataEncode.encode x).size) + s₂,
        p.space [DataEncode.encode x] sorry = .some s')

def ComputableInTimeAndSpace (α β : Type) [DataEncode α] [DataEncode β]
  (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ (p : WellFormedProgram 1), ComputesInTimeAndSpace p f t s


lemma fold_space_linear {s : ℕ → ℕ} {step : Data → Data → Data}
    (hbody : ∀ (c acc : Data),
      meteredEvalOp stack .fold  body (c :: acc :: stack) h_wf =
        .some (step c acc, stepTime c acc, stepSpace c acc)) :
    ∀ (xs : List Data) (acc : Data) (stack : List Data) (h_wf : WFProg (stack.length + 2) body),
      goMeteredFold xs acc stack body h_wf =
        .some (xs.foldl (fun a x => step x a) acc,
               foldTime stepTime step xs acc,
               foldSpace stepSpace step xs acc) := by
  exact goMeteredFold_of_step hbody

def prog_reverse : WellFormedProgram 1 := {
  prog := [
    .empty,
    .fold [
      .cons 0 1
    ] 0 1
  ],
  h_wf := by simp [WFProg, WFOp]
}

theorem ComputesInTimeAndSpace_reverse {α : Type} [DataEncode α]
  : ComputesInTimeAndSpace prog_reverse (List.reverse : List α → List α)
    (fun n => 1 + 2 * n + n * n) (fun n => 1 + 2 * n + n * n) := by
  refine ⟨_, _, _, _, ?_⟩
  · intro xs; simp [prog_reverse, meteredEvalOp, Data.asList, List.reverse]
  · intro xs; simp [prog_reverse, meteredEvalOp, Data.asList, List.reverse]; use 1 + 2 * xs.size + xs.size * xs.size; omega
  · intro xs; simp [prog_reverse, meteredEvalOp, Data.asList, List.reverse]; use 1 + 2 * xs.size + xs.size * xs.size; omega

/-- Generic time cost of a metered fold whose body acts as a pure step
    `(item, acc) ↦ acc'` with per-iteration time `stepTime item acc`. -/
def foldTime (stepTime : Data → Data → ℕ) (step : Data → Data → Data)
    : List Data → Data → ℕ
  | [],      acc => acc.size
  | x :: xs, acc => 1 + stepTime x acc + foldTime stepTime step xs (step x acc)

/-- Generic space cost: max of per-iteration body space and the rest of the fold. -/
def foldSpace (stepSpace : Data → Data → ℕ) (step : Data → Data → Data)
    : List Data → Data → ℕ
  | [],      acc => acc.size
  | x :: xs, acc => max (stepSpace x acc) (foldSpace stepSpace step xs (step x acc))

/-- Generic semantics + time + space for any well-formed fold body that acts as a pure
    deterministic step.

    The hypothesis `hbody` must hold for every iteration: running `body` on a stack of the
    form `c :: acc :: stack` (for any `c, acc`) produces `step c acc` with cost
    `(stepTime c acc, stepSpace c acc)`. -/
lemma goMeteredFold_of_step {body : Prog} {stack : List Data}
    (h_wf : WFProg (stack.length + 2) body)
    (step : Data → Data → Data) (stepTime stepSpace : Data → Data → ℕ)
    (hbody : ∀ (c acc : Data),
      meteredEvalProg body (c :: acc :: stack) h_wf =
        .some (step c acc, stepTime c acc, stepSpace c acc))
    (xs : List Data) (acc : Data) :
    goMeteredFold xs acc stack body h_wf =
      .some (xs.foldl (fun a x => step x a) acc,
             foldTime stepTime step xs acc,
             foldSpace stepSpace step xs acc) := by
  induction xs generalizing acc with
  | nil => simp [foldTime, foldSpace]
  | cons x xs ih => simp [hbody, ih, foldTime, foldSpace]

/-- Time cost of running the body `[.cons 0 1]` repeatedly over `xs`, threading `acc`. -/
def revFoldTime (xs : List Data) (acc : Data) : ℕ :=
  foldTime (fun x a => 1 + (Data.l (x :: a.asList)).size)
           (fun x a => Data.l (x :: a.asList)) xs acc

/-- Space cost of the same fold: maximum live size across iterations. -/
def revFoldSpace (xs : List Data) (acc : Data) : ℕ :=
  foldSpace (fun x a => 1 + (Data.l (x :: a.asList)).size)
            (fun x a => Data.l (x :: a.asList)) xs acc

/-- Combined semantics + time + space for the inner fold of `prog_reverse`. -/
lemma goMeteredFold_reverseBody (xs : List Data) (acc : Data) (stack : List Data)
    (h_wf : WFProg (stack.length + 2) [Operation.cons 0 1]) :
    goMeteredFold xs acc stack [Operation.cons 0 1] h_wf =
      .some (xs.foldl (fun a x => Data.l (x :: a.asList)) acc,
             revFoldTime xs acc, revFoldSpace xs acc) := by
  exact goMeteredFold_of_step h_wf
    (fun x a => Data.l (x :: a.asList))
    (fun x a => 1 + (Data.l (x :: a.asList)).size)
    (fun x a => 1 + (Data.l (x :: a.asList)).size)
    (by intro c acc'; simp [meteredEvalOp]) xs acc

/-- The reverse-body fold reverses the input list, prepended onto the accumulator. -/
lemma foldl_reverseBody (xs : List Data) (acc : Data) :
    xs.foldl (fun a x => Data.l (x :: a.asList)) acc =
      Data.l (xs.reverse ++ acc.asList) := by
  induction xs generalizing acc with
  | nil => cases acc with | l _ => simp [Data.asList]
  | cons x xs ih => cases acc with | l _ => simp [ih, Data.asList, List.reverse_cons]

/-- `prog_reverse` reverses its input list, with concrete time and space cost. -/
theorem prog_reverse.semantics (xs : List Data) :
    meteredEvalProg prog_reverse.prog [Data.l xs] prog_reverse.h_wf
      = .some (Data.l xs.reverse,
               1 + revFoldTime xs Data.empty,
               1 + revFoldSpace xs Data.empty) := by
  have h := goMeteredFold_reverseBody xs Data.empty [Data.empty, Data.l xs]
    (by simp [WFProg, WFOp])
  simp [prog_reverse, meteredEvalOp, h, foldl_reverseBody, Data.asList]

/-- Convenient corollary: `prog_reverse.eval` returns the reversed list. -/
theorem prog_reverse.eval_eq (xs : List Data) :
    prog_reverse.eval [Data.l xs] rfl = .some (Data.l xs.reverse) := by
  simp [WellFormedProgram.eval, prog_reverse.semantics]

-- Binary addition
def prog_inc : WellFormedProgram := {
  prog := [
    .fold 0 1 [
      .cons 0 2, -- cons the bit to the accumulator
      .ite 2 [ -- if the new accumulator is nonempty (the bit was 1)
        .cons 1 2, -- add the carry from the previous bit
        .empty -- else just put the carry (0 or 1) as the new accumulator
      ] [
         .cons 1 2 -- if the new bit is zero, we only get a carry if the previous carry was one
      ]
    ]
    -- TODO
  ],
  inputs := 2,
  h_wf := by sorry
}

def add (x y : List Bool) : List Bool :=

  match prog_add.eval [DataEncode.encode x, DataEncode.encode y] rfl with
  | .some d => d.asList.map (fun b => b == dataTrue)
  | .none => [] -- this should never happen since the program is total

theorem prog_add_semantics : ∀ (x y : ℕ),
    prog_add.eval [DataEncode.encode x, DataEncode.encode y] rfl =
      .some (DataEncode.encode (x + y)) := by
  sorry


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
