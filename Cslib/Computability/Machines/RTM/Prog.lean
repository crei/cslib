/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Data
public import Cslib.Computability.Machines.RTM.DataEncode


/-!
# Programs in a rose tree machine (RTM)

This file contains the main definition of the rose tree machine, its programs including
semantics and time and space resource consumption.

## Main definitions and notations

- `Prog` - the program
- `ProgSem` - semantics and resource consumption
- `InPlace` - a fragment of the language that can be easily simulated using multi-tape Turing
    machines.
- `Prog.ComputesInTimeAndSpace` - this defines the complexity notion for the RTM computation model,
    based on `Data` values.
- `Prog.ComputesBoolFunInTimeAndSpace` - the complexity notion transferred to functions on binary
    strings, this making it compatible to all other computation models.
- `ComputableInOTime` - generic time-complexity in the RTM model
- `ComputableInOSpace` - generic space-complexity in the RTM model
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/--
Prog is the syntax representation of a functional language that has a resource consumption
model which is compatible to that of a Turing machine.
The data structure it operates on is a rose tree (`Data`). The advantage of this data structure
is that the majority of lean data types have a direct encoding.
-/
inductive Prog where
  /-- Variable reference at de Bruijn level `id`. -/
  | var (id : ℕ)
  /-- The empty constructor of `Data`. -/
  | empty
  /-- The `cons` constructor of `Data`: prepend the value of `h` to the list value of `t`. -/
  | cons (h t : Prog)
  /-- Destructor of `Data`: evaluate `v`; if it is `empty`, run `emp`; otherwise destructure into
      `head` and `tail` and apply the function `cs` to `head` and then to `tail`. -/
  | elim (v emp cs : Prog)
  /-- Equality comparison: If `x` evaluates to the same data as `y`, run `then_`, else
  run `else_`.
  This can be simulated using `while_` below, but it is useful to have. -/
  | ifEq (x y then_ else_ : Prog)
  /-- While loop: evaluate `init` to the starting accumulator; `body` must evaluate
      to a one-argument function which is applied to the current accumulator on each
      iteration. Return the accumulator if its head is empty. -/
  | while_ (init body : Prog)
  /-- Abstraction / closure in one variable. -/
  | fn (body : Prog)
  /-- Function application. -/
  | app (fn arg : Prog)
deriving Repr

/-- Runtime values for the semantics predicate `ProgSem`. -/
inductive Value where
  | data (d : Data)
  | closure (body : Prog) (env : List Value)
deriving Repr

def Value.size : Value → ℕ
  | .data d => d.size
  | .closure _ env => 2 + (env.map Value.size).sum

abbrev Value.empty : Value := .data (Data.l [])

@[simp]
lemma Value.size_data {d : Data} : (Value.data d).size = d.size := by simp [Value.size]

lemma Value.size_pos {v : Value} : 0 < v.size := by
  cases v with
  | data d => simp only [Value.size]; exact Data.size_le
  | closure _ env => simp only [Value.size]; omega

mutual
/-- Semantics of `Prog` including time and space resource bounds.
`ProgSem σ p x t s` means that on environment `σ`, the program `p` evaluates to the value
`x` and uses `t` time and `s` space. -/
inductive ProgSem : (List Value) → Prog → Value → ℕ → ℕ → Prop
  | var :
      ProgSem σ (.var i) (σ[i]?.getD Value.empty)
        (σ[i]?.getD Value.empty).size (σ[i]?.getD Value.empty).size
  | empty : ProgSem σ .empty Value.empty 2 2
  | cons (h₁ : ProgSem σ head (.data hd) hd_t hd_s) (h₂ : ProgSem σ tail (.data tl) tl_t tl_s) :
      ProgSem σ (.cons head tail) (.data (Data.l (hd :: tl.asList))) (hd_t + tl_t) (hd_s + tl_s)
  /-- `elim`, empty branch: `v` is the empty list, so run `emp` in the current environment. -/
  | elim_nil
      (h₁ : ProgSem σ val (.data (Data.l [])) t_v s_v)
      (h₂ : ProgSem σ emp r t_emp s_emp) :
      ProgSem σ (.elim val emp cs) r (t_v + t_emp) (max s_v s_emp)
  /-- `elim`, cons branch: `v` destructures to `hd :: tl`; evaluate the function `cs` to a
      closure and apply it first to `hd` and then to `tl` (so `cs` is a curried
      two-argument function).
      TODO: We could syntactically require that the `cs` argument always has the form
      `.fn .fn ...`, then we could change the cost function so that we do not need to charge
      for creating the closure (and the same for all similar constructs).
       -/
  | elim_cons
      (h_v : ProgSem σ val (.data (Data.l (hd :: tl))) t_v s_v)
      (h_cs : ProgSem σ cs cv t_cs s_cs)
      (h_app₁ : AppSem cv (.data hd) cv' t₁ s₁)
      (h_app₂ : AppSem cv' (.data (Data.l tl)) r t₂ s₂) :
      ProgSem σ (.elim val emp cs) r (t_v + t_cs + t₁ + t₂)
        (max (max (max s_v s_cs) s₁) s₂)
  | ifEq_then
      (h_x : ProgSem σ x (.data vx) t_x s_x)
      (h_y : ProgSem σ y (.data vx) t_y s_y)
      (h_then : ProgSem σ then_ r t_then s_then) :
      ProgSem σ (.ifEq x y then_ else_) r
        (t_x + t_y + t_then)
        (max (max s_x s_y) s_then)
  | ifEq_else
      (h_x : ProgSem σ x (.data vx) t_x s_x)
      (h_y : ProgSem σ y (.data vy) t_y s_y)
      (h_neq : vx ≠ vy)
      (h_else : ProgSem σ else_ r t_else s_else) :
      ProgSem σ (.ifEq x y then_ else_) r
        (t_x + t_y + t_else)
        (max (max s_x s_y) s_else)
  /-- `while_ init body`: evaluate `init` to the starting accumulator and `body` to a
      one-argument closure, then iterate the closure via `WhileSem` until it halts. -/
  | while_
      (h_init : ProgSem σ init (.data acc) t_init s_init)
      (h_body : ProgSem σ body bodyVal t_body s_body)
      (h_while : WhileSem bodyVal acc r t_w s_w) :
      ProgSem σ (.while_ init body) (.data r) (t_init + t_body + t_w)
        (max (max s_init s_body) s_w)
  /-- `fn body`: evaluate to a closure capturing the current environment `σ`. The cost is the
      size of the resulting closure (mirroring `var`, which charges the size of the value it
      produces).
      TODO: We could charge only the size of the referenced variables, which would make it
      more or less free to create a non-capturing closure. -/
  | fn :
      ProgSem σ (.fn body) (.closure body σ)
        (Value.closure body σ).size (Value.closure body σ).size
  /-- `app fn arg`: evaluate `fn` to a closure, evaluate `arg` to a value, then run the
      closure's body in the *captured* environment extended with the argument (static
      scoping). -/
  | app
      (h_fn : ProgSem σ fn fv t_f s_f)
      (h_arg : ProgSem σ arg v t_a s_a)
      (h_app : AppSem fv v r t_b s_b) :
      ProgSem σ (.app fn arg) r (t_f + t_a + t_b) (max (max s_f s_a) s_b)

/-- Application of a value to an argument value. `AppSem f v r t s` means that applying the
closure `f` to the argument `v` yields `r` using `t` time and `s` space. Only closures can be
applied; applying a first-order value has no derivation (the program is stuck). -/
inductive AppSem : Value → Value → Value → ℕ → ℕ → Prop
  | mk (h_body : ProgSem (σ ++ [v]) body r t s) :
      AppSem (.closure body σ) v r t s

/-- Iterates the closure `bodyVal` of a `while_` loop, threading the accumulator.
`WhileSem bodyVal acc r t s` means that, starting from accumulator `acc`, repeatedly applying
`bodyVal` to the current accumulator eventually yields result `r` using `t` time and `s` space.
Before each iteration the halting condition is checked on the current accumulator: iteration
terminates (with the accumulator as result) when `acc` is empty or its head is empty.
Otherwise `bodyVal` is applied and its result becomes the new accumulator. Non-terminating
loops simply have no derivation. -/
inductive WhileSem : Value → Data → Data → ℕ → ℕ → Prop
  | halt
      (h_stop : acc.asList.head?.getD (Data.l []) = Data.l []) :
      WhileSem bodyVal acc acc acc.size acc.size
  | step
      (h_cont : acc.asList.head?.getD (Data.l []) ≠ Data.l [])
      (h_app : AppSem bodyVal (.data acc) (.data v) t_b s_b)
      (h_rest : WhileSem bodyVal v r t_r s_r) :
      WhileSem bodyVal acc r (t_b + t_r) (max s_b s_r)
end

/-- The program `p` computes the value `y` from the value `x` in time `t` and space `s`. -/
def Prog.ComputesInTimeAndSpace (p : Prog) (x y : Data) (t : ℕ) (s : ℕ) : Prop :=
  ProgSem [.data x] p (.data y) t s

/-- The program `p` computes the function `f` (on binary strings) in time `t` and space `s`.
This is the main definition that defines complexity for this computation model. -/
def Prog.ComputesBoolFunInTimeAndSpace
  (p : Prog) (f : List Bool → List Bool) (t : ℕ → ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ x, ∃ t' ≤ t x.length, ∃ s' ≤ s x.length,
  Prog.ComputesInTimeAndSpace p (DataEncode.encode x) (DataEncode.encode (f x)) t' s'

/-- The function `f` is computable in time `t` in the RTM model, up to constant factors -/
def ComputableInOTime (f : List Bool → List Bool) (t : ℕ → ℕ) : Prop :=
  ∃ p a s, Prog.ComputesBoolFunInTimeAndSpace p f (fun n => a * (t n) + a) s

/-- The function `f` is computable in space `s` in the RTM model, up to constant factors -/
def ComputableInOSpace (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∃ p a t, Prog.ComputesBoolFunInTimeAndSpace p f t (fun n => a * (s n) + a)

/-- The *in-place* (first-order) fragment of the functional language.

`InPlace p` holds when every `fn` in `p` occurs in an immediately-consumed position — as the
operator of an `app`, or as the (curried) branch of an `elim`/`while_`. Consequently no
closure ever escapes: every abstraction is created and used on the spot, so all values that
flow through the environment are first-order `Data`. This is exactly the fragment a
defunctionalising compiler targets, and it is closed under the operational semantics.

A Turing machine can directly implement this fragment without the need for closures:
One tape is used for each "node" in the syntax tree.
-/
inductive InPlace : Prog → Prop
  | var : InPlace (.var i)
  | empty : InPlace .empty
  | cons (hh : InPlace h) (ht : InPlace t) : InPlace (.cons h t)
  /-- `elim` over an in-place value, empty branch, and a curried two-argument function
      branch `fn (fn body)` binding `head` and `tail`. -/
  | elim (hv : InPlace v) (hemp : InPlace emp) (hbody : InPlace body) :
      InPlace (.elim v emp (.fn (.fn body)))
  | ifEq (hx : InPlace x) (hy : InPlace y) (hthen : InPlace then_) (helse : InPlace else_) :
      InPlace (.ifEq x y then_ else_)
  /-- `while_` whose body is a literal one-argument function `fn body` binding the
      accumulator. -/
  | while_ (hinit : InPlace init) (hbody : InPlace body) :
      InPlace (.while_ init (.fn body))
  /-- `app` whose operator is a literal one-argument function `fn body` (a `let` binding):
      the abstraction is created and immediately consumed, so no closure escapes. -/
  | app (hbody : InPlace body) (harg : InPlace arg) :
      InPlace (.app (.fn body) arg)


end RoseTreeMachine

end Turing
