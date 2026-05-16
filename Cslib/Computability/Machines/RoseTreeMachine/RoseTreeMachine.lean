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

@[simp]
lemma Data.asList_empty : Data.empty.asList = [] := by simp [Data.empty]

@[simp]
lemma Data.asList_l : Data.l xs.asList = xs := by grind

--- Encoding length of d.
def Data.size : Data → ℕ
  | Data.l xs => 2 + (xs.map Data.size |>.sum)

@[simp]
lemma Data.size_empty : Data.empty.size = 2 := by simp [Data.empty, Data.size]

@[simp]
lemma Data.cons_size {h : Data} {t : List Data} :
    (Data.l (h :: t)).size = h.size + (Data.l t).size := by
  simp [Data.size, Nat.add_assoc, Nat.add_comm]

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

def Operation.Total (op : Operation) (h_wf : WFOp n op) : Prop :=
  ∀ (stack : List Data) (h_len : stack.length = n),
  (meteredEvalOp stack op (h_len ▸ h_wf)).Dom

def Prog.Total {n : ℕ} (body : Prog) (h_wf : WFProg n body) : Prop :=
  ∀ (stack : List Data) (h_len : stack.length = n),
    (meteredEvalProg body stack (h_len ▸ h_wf)).Dom

mutual
  @[simp]
  def Operation.WhileFree (op : Operation) : Prop :=
    match op with
    | .ite _ a b => Prog.WhileFree a ∧ Prog.WhileFree b
    | .while_ _ _ => False
    | .fold b _ _ => Prog.WhileFree b
    | .call p => Prog.WhileFree p
    | _ => True
  @[simp]
  def Prog.WhileFree (body : Prog) : Prop :=
    match body with
    | [] => True
    | op :: rest => Operation.WhileFree op ∧ Prog.WhileFree rest
end

@[simp]
theorem Prog_total_of_WhileFree {n : ℕ} {body : Prog}
    (h_wf : WFProg n body) (h_whileFree : Prog.WhileFree body) :
    Prog.Total body h_wf := by
  sorry

@[simp]
theorem Op_total_of_WhileFree {n : ℕ} {op : Operation}
    (h_wf : WFOp n op) (h_whileFree : Operation.WhileFree op) :
    Operation.Total op h_wf := by
  sorry

@[simp]
theorem Dom_meteredEvalOp_of_WhileFree {op : Operation} {stack : List Data}
    (h_wf : WFOp stack.length op) (h_whf : Operation.WhileFree op) :
    (meteredEvalOp stack op h_wf).Dom :=
  Op_total_of_WhileFree h_wf h_whf stack rfl

-- We now introduce some simplification lemmas. Because of the dependent types involed
-- in Part and for other reasons, we only do this for while-free programs.
-- It is not sufficient for a program to be total, because this does not imply that all
-- sub-programs are total, which is what we would need for simp lemmas to be clearly statable.

def Operation.meteredEvalT (op : Operation) (stack : List Data) (h_wf : WFOp stack.length op)
    (h_whf : Operation.WhileFree op) : Data × ℕ × ℕ :=
  (meteredEvalOp stack op h_wf).get (by simp [h_whf])

def Prog.meteredEvalT (body : Prog) (stack : List Data)
    (h_wf : WFProg stack.length body)
    (h_whf : Prog.WhileFree body) : Data × ℕ × ℕ :=
  (meteredEvalProg body stack h_wf).get (Prog_total_of_WhileFree h_wf h_whf stack rfl)

@[simp]
lemma Operation.meteredEvalT_empty {stack : List Data} {h_wf : WFOp stack.length .empty} :
    Operation.meteredEvalT .empty stack h_wf (by simp) = (Data.empty, 1, 1) := by
  simp [Operation.meteredEvalT, meteredEvalOp]

@[simp]
lemma Operation.meteredEvalT_cons
    {stack : List Data}
    {h_wf : WFOp stack.length (.cons h t)} :
    Operation.meteredEvalT (.cons h t) stack h_wf (by simp) =
      (Data.l (stack[h]'h_wf.1 :: (stack[t]'h_wf.2).asList),
      1 + (Data.l (stack[h]'h_wf.1 :: (stack[t]'h_wf.2).asList)).size,
      1 + (Data.l (stack[h]'h_wf.1 :: (stack[t]'h_wf.2).asList)).size) := by
  simp [Operation.meteredEvalT, meteredEvalOp]

@[simp]
lemma Operation.meteredEvalT_fold {body : Prog} {initial list : TapeIndex} {stack : List Data}
    {h_wf : WFOp stack.length (.fold body initial list)}
    {h_whf : Operation.WhileFree (.fold body initial list)}
    (h_body_total : body.Total h_wf.2.2) :
    Operation.meteredEvalT (.fold body initial list) stack h_wf h_whf =
      ( -- data: fold over accumulator
        (stack[list]'h_wf.1).asList.foldl
          (fun acc x => (Prog.meteredEvalT body (x :: acc :: stack) h_wf.2.2
            (by simpa using h_whf)).1)
          (stack[initial]'h_wf.2.1),
        -- time: thread (acc, time), then add final acc size
        (let (a', t) := (stack[list]'h_wf.1).asList.foldl
            (fun (acc, t) x =>
              let (r, t', _) := Prog.meteredEvalT body (x :: acc :: stack) h_wf.2.2
                (by simpa using h_whf)
              (r, t + 1 + t'))
            (stack[initial]'h_wf.2.1, 0);
          t + a'.size),
        -- space: thread (acc, max-space), then max with final acc size
        (let (a', s) := (stack[list]'h_wf.1).asList.foldl
            (fun (acc, s) x =>
              let (r, _, s') := Prog.meteredEvalT body (x :: acc :: stack) h_wf.2.2
                (by simpa using h_whf)
              (r, max s s'))
            (stack[initial]'h_wf.2.1, 0);
          max s a'.size)
      )
      := by
  sorry

/-- Recursive form of the per-iteration accumulator threading used by `meteredEvalT_fold`.
    Mirrors `goMeteredFold` directly, but on the `meteredEvalT` side: every body run
    is a total `Data × ℕ × ℕ` (no `Part`). -/
def Operation.foldRec (body : Prog) (stack : List Data)
    (h_wf : WFProg (stack.length + 2) body)
    (h_whf : Prog.WhileFree body) :
    List Data → Data → Data × ℕ × ℕ
  | [], acc => (acc, acc.size, acc.size)
  | x :: rest, acc =>
    let (acc', t, s) := Prog.meteredEvalT body (x :: acc :: stack) h_wf h_whf
    let (r, t', s') := Operation.foldRec body stack h_wf h_whf rest acc'
    (r, 1 + t + t', max s s')

/-- Recursive analog of `Operation.meteredEvalT_fold`: instead of three `List.foldl`s,
    express the fold operation's result by structural recursion on the list. -/
lemma Operation.meteredEvalT_fold_rec
    {body : Prog} {initial list : TapeIndex} {stack : List Data}
    {h_wf : WFOp stack.length (.fold body initial list)}
    {h_whf : Operation.WhileFree (.fold body initial list)} :
    Operation.meteredEvalT (.fold body initial list) stack h_wf h_whf =
      Operation.foldRec body stack h_wf.2.2 (by simpa using h_whf)
        (stack[list]'h_wf.1).asList (stack[initial]'h_wf.2.1) := by
  sorry


/-- Space bound for a fold operation. If the initial accumulator fits within `B`,
    and for every accumulator with `acc.size ≤ B` the body uses space `≤ B` and
    produces a new accumulator with size `≤ B`, then the entire fold uses space
    `≤ B`. -/
lemma fold_bounded_space {body : Prog} {initial list : TapeIndex} {stack : List Data}
    {h_wf : WFOp stack.length (.fold body initial list)}
    {h_whf : Operation.WhileFree (.fold body initial list)}
    (B : ℕ)
    (h_init : (stack[initial]'h_wf.2.1).size ≤ B)
    (h_step : ∀ acc x, acc.size ≤ B → x ∈ (stack[list]'h_wf.1).asList →
      let (acc', _, s) := Prog.meteredEvalT body (x :: acc :: stack) h_wf.2.2 (by simpa using h_whf)
      s ≤ B ∧ acc'.size ≤ B) :
    (Operation.meteredEvalT (.fold body initial list) stack h_wf h_whf).2.2 ≤ B := by
  sorry

/-- Induction principle for `Operation.meteredEvalT` on a `.fold` operation.
    To prove `motive` of the final `(acc, time, space)` triple, the caller supplies:
    * `h_init`: the motive holds on `(initial, 0, 0)`;
    * `h_step`: for every iteration item `x ∈ list`, the motive is preserved by one
      body invocation — old triple `(acc, t, s)` is taken to
      `(r.1, t + 1 + r.2.1, max s r.2.2)` where `r` is the body's result;
    * `h_finish`: from the motive on the post-loop triple `(acc, t, s)`, derive
      the motive on the final adjusted triple `(acc, t + acc.size, max s acc.size)`,
      which accounts for the `[]` base case of `goMeteredFold`. -/
lemma Operation.meteredEvalT_fold_induction
    {body : Prog} {initial list : TapeIndex} {stack : List Data}
    {h_wf : WFOp stack.length (.fold body initial list)}
    {h_whf : Operation.WhileFree (.fold body initial list)}
    (motive : Data → ℕ → ℕ → Prop)
    (h_init : motive (stack[initial]'h_wf.2.1) 0 0)
    (h_step : ∀ acc t s x, x ∈ (stack[list]'h_wf.1).asList → motive acc t s →
      let (r, t', s') := Prog.meteredEvalT body (x :: acc :: stack) h_wf.2.2 (by simpa using h_whf)
      motive r (t + 1 + t') (max s s'))
    (h_finish : ∀ acc t s, motive acc t s → motive acc (t + acc.size) (max s acc.size)) :
    let (r, t, s) := Operation.meteredEvalT (.fold body initial list) stack h_wf h_whf
    motive r t s := by
  sorry

@[simp]
lemma Prog.meteredEvalT_nil
    {stack : List Data}
    {h_wf : WFProg stack.length []} :
    Prog.meteredEvalT [] stack h_wf (by simp) = (stack.head (by grind [WFProg]), 0, 0) := by
  simp [Prog.meteredEvalT]

@[simp]
lemma Prog.meteredEvalT_cons
    {op : Operation} {rest : Prog} {stack : List Data}
    {h_wf : WFProg stack.length (op :: rest)}
    {h_whf : Prog.WhileFree (op :: rest)} :
    Prog.meteredEvalT (op :: rest) stack h_wf h_whf =
      let (r, opT, opS) := op.meteredEvalT stack h_wf.1 h_whf.1
      let (stack, t, s) := meteredEvalT rest (r :: stack) h_wf.2 h_whf.2
      (stack, opT + t, opS + s) := by
  sorry


------------------------------------------------------------------------------
-- Example program
---------------------------------------------------------------------------

def prog_reverse : Prog := [
    .empty,
    .fold [ .cons 0 1 ] 0 1
  ]

lemma prog_reverse.semantics (x : Data) (xs : List Data) :
    (prog_reverse.meteredEvalT
      (x :: xs)
      (by simp [prog_reverse, WFProg, WFOp])
      (by simp [prog_reverse])).1 =
      Data.l (x.asList).reverse := by
  have h (xs : List Data) (init : Data) : xs.foldl (fun a x => Data.l (x :: a.asList)) init =
      Data.l (xs.reverse ++ init.asList) := by
    induction xs generalizing init with
    | nil => simp
    | cons x xs ih => simp [List.foldl, ih]
  simp [prog_reverse, h]

lemma prog_reverse.time (x : Data) (xs : List Data) :
    (prog_reverse.meteredEvalT
      (x :: xs)
      (by simp [prog_reverse, WFProg, WFOp])
      (by simp [prog_reverse])).2 =
      sorry := by
  simp [prog_reverse]
  sorry

lemma prog_reverse.space (list : Data) (xs : List Data) :
    (prog_reverse.meteredEvalT
      (list :: xs)
      (by simp [prog_reverse, WFProg, WFOp])
      (by simp [prog_reverse])).2.2 ≤ 8 * list.size + 8 := by
  sorry
  -- have h (stack list : List Data) (acc : Data) :
  --     (Operation.foldRec [.cons 0 1] stack sorry sorry list acc).2.2 ≤ 8 * (Data.l list).size := by
  --   induction list with
  --   | nil => simp [Operation.foldRec]
  --   | cons x xs ih => sorry
  -- simp only [prog_reverse, Prog.meteredEvalT_cons, Operation.meteredEvalT_empty,
  --   Prog.meteredEvalT_nil, List.head_cons, add_zero, Prod.mk.eta, ge_iff_le]
  -- rw [Operation.meteredEvalT_fold_rec]
  -- simp
  -- specialize h (Data.empty :: list :: xs) list.asList Data.empty
  -- simp at h
  -- grind

-- TODO the successor function is not too easy, because
-- we also need to concatenate at the end.
-- so maybe it is easier to have some kind of fold-map-routine (i.e. a map that also has shared
-- state in an accumulator)?
-- where the "cons" is handeled by the fold-map routine?

def prog_true : Prog := [
    .empty,
    .cons 0 0
  ]

def prog_bit_add : Prog := [
    .empty,
    .cons 0 1,
    .cons 0 1,
    .ite 0
      [ .cons 0 1 ] -- if first bit is 1, add second bit to result
      [ .head 1 ]     -- if first bit is 0, result is just second bit
  ]

def prog_succ : Prog := [
    .call prog_true,
    .fold [ .cons 0 1 ] 0 1
  ]

-----------------------------------------------------------------------------------------
--- The stuff below here still needs some work
-----------------------------------------------------------------------------

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
    (stack : List Data) (h_len : stack.length ≥ inputs) : Part Data :=
  (meteredEvalProg p.prog stack (by sorry)).map fun (d, _, _) => d

@[simp]
def WellFormedProgram.time {inputs : ℕ} (p : WellFormedProgram inputs)
    (stack : List Data) (h_len : stack.length = inputs) : Part ℕ :=
  (meteredEvalProg p.prog stack (by simpa [h_len] using p.h_wf)).map fun (_, t, _) => t

@[simp]
def WellFormedProgram.space {inputs : ℕ} (p : WellFormedProgram inputs)
    (stack : List Data) (h_len : stack.length = inputs) : Part ℕ :=
  (meteredEvalProg p.prog stack (by simpa [h_len] using p.h_wf)).map fun (_, _, s) => s

structure TotalProgram (inputs : ℕ) extends WellFormedProgram inputs where
  h_total : toWellFormedProgram.prog.Total toWellFormedProgram.h_wf

def TotalProgram.eval {inputs : ℕ} (p : TotalProgram inputs)
    (stack : List Data) (h_len : stack.length ≥ inputs) : Data :=
  (p.toWellFormedProgram.eval stack h_len).get (p.h_total stack sorry)

/-- Unfolding lemma that lets `simp` "execute" a `TotalProgram` step-by-step: it
    rewrites `p.eval stack h_len` into a form mentioning `meteredEvalProg` directly,
    so the `@[simp]` equations for `meteredEvalProg`/`meteredEvalOp` together with
    `Part.some_bind`, `Part.map_some`, `Part.get_some` can reduce the program. -/
@[simp]
theorem TotalProgram.eval_eq {inputs : ℕ} (p : TotalProgram inputs)
    (stack : List Data) (h_len : stack.length ≥ inputs) :
    p.eval stack h_len =
      ((meteredEvalProg p.prog stack (by sorry)).get
         (by simpa [WellFormedProgram.eval] using p.h_total stack sorry)).1 := by
  simp [TotalProgram.eval, WellFormedProgram.eval]

def TotalProgram.as_fun {inputs : ℕ} (p : TotalProgram inputs) :
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
    (∀ x : α, p.eval [DataEncode.encode x] sorry = .some (DataEncode.encode (f x))) ∧
    (∀ x : α, ∃ t' ≤ t₁ * (t (DataEncode.encode x).size) + t₂,
        p.time [DataEncode.encode x] rfl = .some t') ∧
    (∀ x : α, ∃ s' ≤ s₁ * (s (DataEncode.encode x).size) + s₂,
        p.space [DataEncode.encode x] sorry = .some s')

def ComputableInTimeAndSpace (α β : Type) [DataEncode α] [DataEncode β]
  (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ (p : WellFormedProgram 1), ComputesInTimeAndSpace p f t s


def prog_reverse : TotalProgram 1 := {
  prog := [
    .empty,
    .fold [
      .cons 0 1
    ] 0 1
  ],
  h_wf := by simp [WFProg, WFOp]
  h_total := by simp
}

-- TODO continue here: Now we need a good lemma for goMeteredFold.

/-- The `(result, time, space)` triple produced by a single execution of a total fold
    body on `c :: acc :: stack`. Derived from `meteredEvalProg`, so no extra data is
    needed beyond the body, its well-formedness, and a totality witness. -/
def Prog.foldStep {body : Prog} {stack : List Data}
    (h_wf : WFProg (stack.length + 2) body) (h_total : body.Total h_wf)
    (c acc : Data) : Data × ℕ × ℕ :=
  (meteredEvalProg body (c :: acc :: stack) h_wf).get
    (h_total (c :: acc :: stack) (by simp))

lemma Prog.meteredEvalProg_eq_foldStep {body : Prog} {stack : List Data}
    (h_wf : WFProg (stack.length + 2) body) (h_total : body.Total h_wf)
    (c acc : Data) :
    meteredEvalProg body (c :: acc :: stack) h_wf =
      .some (Prog.foldStep h_wf h_total c acc) :=
  (Part.some_get _).symm

/-- Simp form of `goMeteredFold_of_step`: a *total* body uniquely determines the fold
    semantics, with no free `step`/`stepTime`/`stepSpace` variables for `simp` to
    invent. The data result is exactly `List.foldl` over `Prog.foldStep`. -/
@[simp]
lemma goMeteredFold_of_total {body : Prog} {stack : List Data}
    (h_wf : WFProg (stack.length + 2) body) (h_total : body.Total h_wf)
    (xs : List Data) (acc : Data) :
    goMeteredFold xs acc stack body h_wf = .some
      (xs.foldl (fun a x => (Prog.foldStep h_wf h_total x a).1) acc,
       foldTime (fun c a => (Prog.foldStep h_wf h_total c a).2.1)
                (fun c a => (Prog.foldStep h_wf h_total c a).1) xs acc,
       foldSpace (fun c a => (Prog.foldStep h_wf h_total c a).2.2)
                 (fun c a => (Prog.foldStep h_wf h_total c a).1) xs acc) := by
  induction xs generalizing acc with
  | nil => simp [foldTime, foldSpace, goMeteredFold]
  | cons x xs ih =>
    simp [ih, foldTime, foldSpace, goMeteredFold]
    rw [Prog.meteredEvalProg_eq_foldStep h_wf h_total]
    simp_all

-- TODO: summary of current problems: We canont re-write the stuff inside a
-- `Part.bind` because that would change the type (although it is equal)
-- Solution: Get rid of Part

lemma prog_reverse.semantics (x : Data) (xs : List Data) :
    (prog_reverse.prog.meteredEvalT (x :: xs) (by simp; sorry) (by simp [prog_reverse])).1 =
      Data.l (x.asList).reverse := by
  have h (xs : List Data) (init : Data) : xs.foldl (fun a x => Data.l (x :: a.asList)) init =
      Data.l (xs.reverse ++ init.asList) := by
    induction xs generalizing init with
    | nil => simp
    | cons x xs ih => simp [List.foldl, ih]
  simp [prog_reverse, h]

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

/-- Generic space bound for `foldSpace` via a single budget `B`:
    if `init.size ≤ B`, and for every reachable accumulator each iteration's per-step
    space and the resulting accumulator both stay within `B`, then the entire fold's
    space is at most `B`. -/
lemma foldSpace_le {step : Data → Data → Data} {stepSpace : Data → Data → ℕ}
    (B : ℕ) (xs : List Data) (init : Data) (hInit : init.size ≤ B)
    (hStep : ∀ acc c, acc.size ≤ B → c ∈ xs →
                stepSpace c acc ≤ B ∧ (step c acc).size ≤ B) :
    foldSpace stepSpace step xs init ≤ B := by
  induction xs generalizing init with
  | nil => simpa [foldSpace] using hInit
  | cons x xs ih =>
    have ⟨hSp, hAcc⟩ := hStep init x hInit (List.mem_cons_self ..)
    refine max_le hSp
      (ih _ hAcc fun acc c hAcc' hc => hStep acc c hAcc' (List.mem_cons_of_mem _ hc))

/-- Linear-space body + constant-size init ⟹ linear-space fold.

    If every step costs space at most `s₁ * (c.size + acc.size) + s₂`, the accumulator
    grows by at most `c.size + k` per item, and `init.size ≤ c₀`, then `foldSpace` is
    linear in `(xs.map Data.size).sum + xs.length * k + c₀`. -/
lemma fold_space_linear {step : Data → Data → Data} {stepSpace : Data → Data → ℕ}
    {s₁ s₂ k c₀ : ℕ}
    (hStepSpace : ∀ c acc, stepSpace c acc ≤ s₁ * (c.size + acc.size) + s₂)
    (hGrowth : ∀ c acc, (step c acc).size ≤ acc.size + c.size + k)
    (xs : List Data) (init : Data) (hInit : init.size ≤ c₀) :
    foldSpace stepSpace step xs init ≤
      max (c₀ + (xs.map Data.size).sum + xs.length * k)
          (s₁ * ((xs.map Data.size).sum + c₀ + xs.length * k) + s₂) := by
  -- Strengthen by allowing any starting bound `c₀'` on `init.size`.
  suffices h : ∀ (xs : List Data) (init : Data) (c₀' : ℕ), init.size ≤ c₀' →
      foldSpace stepSpace step xs init ≤
        max (c₀' + (xs.map Data.size).sum + xs.length * k)
            (s₁ * ((xs.map Data.size).sum + c₀' + xs.length * k) + s₂) from h xs init c₀ hInit
  clear hInit init xs
  intro xs
  induction xs with
  | nil => intro init c₀' hInit; simpa [foldSpace] using Or.inl (by omega)
  | cons x xs ih =>
    intro init c₀' hInit
    have hStepSize : (step x init).size ≤ c₀' + x.size + k := by
      have := hGrowth x init; omega
    have ih' := ih (step x init) (c₀' + x.size + k) hStepSize
    have hSp : stepSpace x init ≤
        s₁ * (x.size + (xs.map Data.size).sum + c₀' + (xs.length + 1) * k) + s₂ := by
      have := Nat.mul_le_mul_left s₁
        (show x.size + init.size ≤ x.size + (xs.map Data.size).sum + c₀' + (xs.length + 1) * k by
          omega)
      have h1 := hStepSpace x init
      omega
    simp only [foldSpace, List.length_cons, List.map_cons, List.sum_cons]
    refine max_le (le_trans hSp (le_max_right _ _)) (le_trans ih' (max_le_max ?_ ?_))
    · have : (xs.length + 1) * k = xs.length * k + k := by ring
      omega
    · apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      have : (xs.length + 1) * k = xs.length * k + k := by ring
      omega

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
