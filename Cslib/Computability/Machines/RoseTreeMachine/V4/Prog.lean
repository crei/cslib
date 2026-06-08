/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V3.Data
public import Cslib.Computability.Machines.RoseTreeMachine.V3.DataEncode

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

/-- A variable, referenced by its de Bruijn level into the environment. -/
def Var := ℕ
deriving Repr

/-- The full functional language.

Unlike the first-order language, this language has functions (`fn`) and application (`app`)
as its *only* binding mechanism: `elim` and `while_` no longer extend the environment
themselves but instead take ordinary program terms that must evaluate to functions
(closures) which are then applied to the bound values.

A first-order program is recovered as the fragment in which every `fn` is the immediate
operator of an `app` (or the curried branch of an `elim`/`while_`), so that no closure ever
escapes; that fragment is the target of a later defunctionalising compiler. -/
inductive Prog where
  /-- Variable reference at de Bruijn level `id`. -/
  | var (id : Var)
  /-- The empty rose tree `[]`. -/
  | empty
  /-- `cons h t`: prepend the value of `h` (a rose tree) to the list value of `t`. -/
  | cons (h t : Prog)
  /-- `elim v em cs`: evaluate `v`; if it is `empty`, run `em`; otherwise destructure into
      `head` and `tail` and apply the function `cs` to `head` and then to `tail`. `cs` is
      therefore a *curried two-argument function* (e.g. `fn (fn body)`). -/
  | elim (v em cs : Prog)
  /-- `while_ init body`: evaluate `init` to the starting accumulator; `body` must evaluate
      to a one-argument function which is applied to the current accumulator on each
      iteration until the halting condition holds. -/
  | while_ (init body : Prog)
  /-- Abstraction / closure in one variable. -/
  | fn (body : Prog)
  /-- Function application. -/
  | app (fn arg : Prog)
deriving Repr

/-- Runtime values produced by `ProgSem`. A value is either first-order `Data` or a
`closure` capturing the environment in force at its creation together with the body of an
`fn`. Closures are not representable as `Data`, hence the dedicated value space. -/
inductive Value where
  /-- A first-order rose-tree value. -/
  | data (d : Data)
  /-- A closure: the environment `env` captured when the enclosing `fn` was evaluated,
      paired with the abstraction's `body`. -/
  | closure (body : Prog) (env : List Value)
deriving Repr

/-- Size (encoding length) of a value. Mirrors `Data.size` on first-order data; a closure
costs a small constant plus the sizes of its captured environment (the body is treated as a
constant-size code pointer and not counted). -/
def Value.size : Value → ℕ
  | .data d => d.size
  | .closure _ env => 2 + (env.map Value.size).sum

/-- The empty first-order value. -/
abbrev Value.empty : Value := .data (Data.l [])

@[simp]
lemma Value.size_data {d : Data} : (Value.data d).size = d.size := by simp [Value.size]

@[simp]
lemma Value.size_empty : Value.empty.size = 2 := by simp

mutual
/-- Semantics of `Prog` including time and space resource bounds.
`ProgSem σ p x t s` means that on environment `σ`, the program `p` evaluates to the value
`x` and uses `t` time and `s` space. The environment holds `Value`s so that closures (the
results of `fn`) can be bound to variables and passed as arguments. -/
inductive ProgSem : (List Value) → Prog → Value → ℕ → ℕ → Prop
  | var :
      ProgSem σ (.var (i : ℕ)) (σ[i]?.getD Value.empty)
        (σ[i]?.getD Value.empty).size (σ[i]?.getD Value.empty).size
  | empty : ProgSem σ .empty Value.empty 2 2
  | cons (h₁ : ProgSem σ head (.data hd) hd_t hd_s) (h₂ : ProgSem σ tail (.data tl) tl_t tl_s) :
      ProgSem σ (.cons head tail) (.data (Data.l (hd :: tl.asList))) (hd_t + tl_t) (hd_s + tl_s)
  /-- `elim`, empty branch: `v` is the empty list, so run `em` in the current environment. -/
  | elim_nil
      (h₁ : ProgSem σ val (.data (Data.l [])) t_v s_v)
      (h₂ : ProgSem σ emp r t_em s_em) :
      ProgSem σ (.elim val emp cs) r (t_v + t_em) (max s_v s_em)
  /-- `elim`, cons branch: `v` destructures to `hd :: tl`; evaluate the function `cs` to a
      closure and apply it first to `hd` and then to `tl` (so `cs` is a curried
      two-argument function). -/
  | elim_cons
      (h_v : ProgSem σ val (.data (Data.l (hd :: tl))) t_v s_v)
      (h_cs : ProgSem σ cs cv t_cs s_cs)
      (h_app₁ : AppSem cv (.data hd) cv' t₁ s₁)
      (h_app₂ : AppSem cv' (.data (Data.l tl)) r t₂ s₂) :
      ProgSem σ (.elim val emp cs) r (t_v + t_cs + t₁ + t₂)
        (max (max (max s_v s_cs) s₁) s₂)
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
  | mk (h_body : ProgSem (σ' ++ [v]) body r t s) :
      AppSem (.closure body σ') v r t s

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

def Prog.ComputesBoolFunInTimeAndSpace
  (p : Prog) (f : List Bool → List Bool) (t : ℕ → ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ x, ∃ t' ≤ t x.length, ∃ s' ≤ s x.length,
  Prog.ComputesInTimeAndSpace p (DataEncode.encode x) (DataEncode.encode (f x)) t' s'

/-- The *in-place* (first-order) fragment of the functional language.

`InPlace p` holds when every `fn` in `p` occurs in an immediately-consumed position — as the
operator of an `app`, or as the (curried) branch of an `elim`/`while_`. Consequently no
closure ever escapes: every abstraction is created and used on the spot, so all values that
flow through the environment are first-order `Data`. This is exactly the fragment a
defunctionalising compiler targets, and it is closed under the operational semantics.

The hope is that a Turing machine can directly implement the in-place fragment without needing to
represent closures.

Concretely:
* `elim` requires its branch to be a literal curried two-argument function `fn (fn body)`
  (binding `head` and `tail`); a `let x = e in body` is encoded as
  `elim (cons e empty) _ (fn (fn body))`.
* `while_` requires its body to be a literal one-argument function `fn body`.
* there is no rule for a bare `fn` and no rule for `app`, so `fn` only ever appears as an
  `elim`/`while_` branch and no closure is ever applied or escapes. -/
inductive InPlace : Prog → Prop
  | var : InPlace (.var i)
  | empty : InPlace .empty
  | cons (hh : InPlace h) (ht : InPlace t) : InPlace (.cons h t)
  /-- `elim` over an in-place value, empty branch, and a curried two-argument function
      branch `fn (fn body)` binding `head` and `tail`. -/
  | elim (hv : InPlace v) (hemp : InPlace emp) (hbody : InPlace body) :
      InPlace (.elim v emp (.fn (.fn body)))
  /-- `while_` whose body is a literal one-argument function `fn body` binding the
      accumulator. -/
  | while_ (hinit : InPlace init) (hbody : InPlace body) :
      InPlace (.while_ init (.fn body))

end V4

end RoseTreeMachine

end Turing
