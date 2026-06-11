/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.ReduceOption
public import Cslib.Computability.Machines.RTM.PB
public import Cslib.Computability.Machines.RTM.DataEncode

/-! # Tools for rose tree machines

Derived program-builder combinators and their semantics for working with basic data types like
pairs, `Option`, etc. plus a set of lemmas to help reasoning about the semantics of while loops.

## Main definitions and notations

- `PB.head`, `PB.tail` - get the head and tail of a list-valued builder
- `PB.fst`, `PB.snd` - get the first and second component of a pair (encoded as a two-element list)
- `PB.some` - encode an `Option.some` as a singleton list
- `PB.optionElim` - eliminate an `Option` by branching on whether a builder is empty or not
- `PB.toPair` - encode a pair as a two-element list
- `PB.constant` - build a builder that evaluates to a constant `Data` value

- `PB.fold` - left fold of a body over a list, implemented with `while_`
- `PB.evalFunGraph` - evaluate a function given as a graph (list of input-output pairs) at an
    argument, implemented with `while_`

-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace PB

variable {env : List Value}
variable {α : Type} [DataEncode α]
variable {β : Type} [DataEncode β]

/-- Returns the tail of a list-valued builder (`[]` when empty). -/
def tail (x : PB) : PB := .elim x .empty (fun _hd tl => tl)

/-- Returns the head of a list-valued builder (`Data.l []` when empty). -/
def head (x : PB) : PB := .elim x .empty (fun hd _tl => hd)

@[simp]
lemma tail_computes {x : PB} {dx : Data} (hx : x.Computes env (.data dx)) :
    (tail x).Computes env (.data (Data.l dx.asList.tail)) := by
  obtain ⟨dx⟩ := dx
  cases dx with
  | nil => simpa [PB.tail] using elim_nil_computes hx empty_computes
  | cons hd tl =>
    refine elim_cons_computes hx ?_
    intro ext
    simpa [PB.computesFun₂, var] using
      var_computesFun (binds := [.data hd, .data (Data.l tl)]) (j := 1) ext

@[simp]
lemma head_computes {x : PB} {dx : Data} (hx : x.Computes env (.data dx)) :
    Computes env (PB.head x) (.data (dx.asList.headD (Data.l []))) := by
  obtain ⟨dx⟩ := dx
  cases dx with
  | nil => simpa [PB.head] using elim_nil_computes hx empty_computes
  | cons hd tl =>
    refine elim_cons_computes hx ?_
    intro ext
    simpa [PB.computesFun₂, var] using
      var_computesFun (binds := [.data hd, .data (Data.l tl)]) (j := 0) ext

/-- First projection (`head`). -/
def fst (x : PB) : PB := head x

lemma fst_ComputesEnc {x : PB} {a : α × β} (hx : x.ComputesEnc env a) :
    (fst x).ComputesEnc env a.fst := by
  obtain ⟨a, b⟩ := a
  apply PB.head_computes hx

/-- Second projection (`head` of `tail`). -/
def snd (x : PB) : PB := head (PB.tail x)

lemma snd_ComputesEnc {x : PB} {a : α × β} (hx : x.ComputesEnc env a) :
    (snd x).ComputesEnc env a.snd := by
  obtain ⟨a, b⟩ := a
  apply PB.head_computes (PB.tail_computes hx)

/-- `Option.some` as a singleton list. -/
def some (x : PB) : PB := cons x empty

lemma some_ComputesEnc {x : PB} {a : α} (hx : x.ComputesEnc env a) :
    (PB.some x).ComputesEnc env (Option.some a) := by
  apply PB.cons_computes hx empty_computes

/-- Eliminate an `Option`: on `none` (empty) run `noneCase`, on `some v` run `someCase v`. -/
def optionElim (x noneCase : PB) (someCase : PB → PB) : PB :=
  elim x noneCase (fun v _ => someCase v)

lemma optionElim_computesEnc_none
    {x noneCase : PB} {someCase : PB → PB}
    (hx : x.ComputesEnc env (none : Option α))
    {a : β}
    (h_none : noneCase.ComputesEnc env a) :
    (optionElim x noneCase someCase).ComputesEnc env a := by
  apply PB.elim_nil_computes hx h_none

lemma optionElim_computesEnc_some
    {x noneCase : PB} {someCase : PB → PB}
    {a : α}
    {b : β}
    (hx : x.ComputesEnc env (Option.some a))
    (h_some : PB.computesFun₂ env (.data (DataEncode.encode a)) (.data (Data.l []))
      (fun v _ => someCase v) (.data (DataEncode.encode b))) :
    (optionElim x noneCase someCase).ComputesEnc env b := by
  apply PB.elim_cons_computes (head := DataEncode.encode a) (tail := [])
    (by simpa [ComputesEnc, DataEncode.encode] using hx) h_some

/-- Build the two-element list `[a, b]` (used as an encoded pair). -/
def toPair (a b : PB) : PB := cons a (PB.cons b empty)

lemma toPair_computesEnc
    {a : α} {b : β} {pa pb : PB}
    (ha : pa.ComputesEnc env a) (hb : pb.ComputesEnc env b) :
    (toPair pa pb).ComputesEnc env (a, b) := by
  apply PB.cons_computes ha (PB.cons_computes hb empty_computes)

/-- Program that evaluates to the constant `a`. -/
def constant (a : Data) : PB := match a with
  | Data.l [] => .empty
  | Data.l (x :: xs) => .cons (constant x) (constant (Data.l xs))

@[simp]
lemma constant_computes {a : Data} : (constant a).Computes env (.data a) := by
  induction a using Data.inductionL with
  | nil => simp [constant]
  | cons hd tl ih_hd ih_tl =>
    simpa [constant] using cons_computes ih_hd ih_tl

def constantEnc {α : Type} [DataEncode α] (a : α) : PB := constant (DataEncode.encode a)

@[simp]
lemma constantEnc_computesEnc {α : Type} [DataEncode α] {a : α} :
    (constantEnc a).ComputesEnc env a := by
  simp [ComputesEnc, constantEnc]


------------- while semantics ------------------------


/-- `fold body init list`: left fold of `body` (taking `acc` then `el`) over `list`.

Implemented with `while_` over a `[remaining, acc]` pair: the loop halts once `remaining`
(the *head* of the accumulator, which is what `while_` inspects) becomes empty; otherwise it
splits off the first element `el`, updates the accumulator to `[rest, body acc el]`, and
continues. The fold's result is the final `acc` (the second component). -/
def fold (body : PB → PB → PB) (init list : PB) : PB :=
  snd (PB.while_ (PB.toPair list init)
    (fun st => elim (PB.fst st) empty
      (fun el rest => toPair rest (body (PB.snd st) el))))


-- Evaluate a function `f` at `arg` where the function is given as a graph (list of pairs).
-- Returns `some y` for the first `x` in the graph such that `f x = y` and `none` otherwise.
def evalFunGraph (graph : PB) (arg : PB) : PB :=
  snd (PB.while_
    (toPair graph .empty)
    (fun acc => .elim acc.fst
      .empty -- cannot happen
      fun pair rest =>
        ifEq pair.fst arg
          (toPair .empty (PB.some pair.snd))
          (toPair rest .empty)))

private def evalFunGraphInner : PB → PB → PB :=
  fun arg acc => .elim acc.fst
    .empty -- cannot happen
    fun pair rest =>
      ifEq pair.fst arg
        (toPair .empty (PB.some pair.snd))
        (toPair rest .empty)

private lemma evalFunGraphInner_computesFun₁ [DecidableEq α]
  (arg : α)
  {p_arg : PB}
  (h_arg : p_arg.ComputesEnc env arg)
  {graph : List (α × β)}
  {x : α}
  {y : β} :
  computesFun₁ env
    (.data (DataEncode.encode (((x, y) :: graph), (.none : Option β))))
    (evalFunGraphInner p_arg)
    (.data (DataEncode.encode (if x == arg then
      ([], Option.some y)
    else
      (graph, Option.none)))) := by
  apply PB.computesFun₁_branch
  intro ext
  unfold evalFunGraphInner
  refine PB.elim_cons_computes (PB.fst_ComputesEnc (PB.var_computes_fresh ext [])) ?_
  apply PB.computesFun₂_branch2
  intro ext2
  -- Names for the extended environment and its fresh bindings.
  set acc := Value.data (DataEncode.encode (((x, y) :: graph), (.none : Option β)))
  set pv := Value.data (DataEncode.encode (x, y)) with hpv
  set rv := Value.data (Data.l (graph.map DataEncode.encode)) with hrv
  -- `arg` (= `p_arg`) is still available after the environment grows.
  have h_arg' := ((h_arg.extend ext).extend [acc]).extend ext2 |>.extend [pv, rv]
  by_cases h : x = arg
  · subst h
    simp only [beq_self_eq_true, if_true]
    exact ifeq_eq_computes
      (fst_ComputesEnc (var_computes_fresh ext2 [rv]))
      h_arg'
      (toPair_computesEnc
        (empty_computes) (some_ComputesEnc (snd_ComputesEnc (var_computes_fresh ext2 [rv]))))
  · refine PB.ifeq_ne_computes (PB.fst_ComputesEnc (var_computes_fresh ext2 [rv])) h_arg'
      (fun he => h (DataEncode.h_inj he)) ?_
    rw [if_neg (by simpa using h)]
    exact PB.toPair_computesEnc
      (var_computes_fresh' ext2 [pv, rv] (j := 1) (by simp)) (empty_computes)


/-- Semantic spec of `eval_fun_graph`: given an encoded graph (list of
`(α × β)`-pairs) and an encoded argument `a : α`, returns
`(graph.find? (·.1 = a)).map (·.2)`, i.e. `some y` for the first pair `(a, y)`
in the graph, else `none`. -/
lemma evalFunGraph_computes
    [DecidableEq α]
    {p_graph p_arg : PB}
    {graph : List (α × β)}
    {a : α}
    (h_graph : p_graph.ComputesEnc env graph)
    (h_arg : p_arg.ComputesEnc env a) :
    (evalFunGraph p_graph p_arg).ComputesEnc env
      ((graph.find? (fun p => p.1 = a)).map (·.2)) := by
  -- The loop iterates the body from `(g, none)` to `([], find-result)` for any remaining list `g`.
  have h_loop : ∀ g : List (α × β),
      WhileComputes env (evalFunGraphInner p_arg)
        (DataEncode.encode (g, (none : Option β)))
        (DataEncode.encode (([] : List (α × β)),
          (g.find? (fun p => p.1 = a)).map (·.2))) := by
    intro g
    induction g with
    | nil =>
      -- Empty remaining list: the loop halts immediately on the empty head.
      apply WhileComputes.halt
      simp [DataEncode.encode]
    | cons hd tl ih =>
      obtain ⟨x, y⟩ := hd
      by_cases h : x = a
      · -- Match on the first element: body sets the result to `some y`, then the loop halts.
        subst h
        have hfind : (((x, y) :: tl).find? (fun p => p.1 = x)).map (·.2) = Option.some y := by
          simp
        rw [hfind]
        have hb := evalFunGraphInner_computesFun₁ (env := env) x h_arg
          (graph := tl) (x := x) (y := y)
        simp only [beq_self_eq_true, if_true] at hb
        refine WhileComputes.step ?_ hb ?_
        · simp [DataEncode.encode]
        · apply WhileComputes.halt
          simp [DataEncode.encode]
      · -- No match on the first element: body drops it, keeps `none`, and recurses.
        have hfind : (((x, y) :: tl).find? (fun p => p.1 = a)).map (·.2)
            = (tl.find? (fun p => p.1 = a)).map (·.2) := by
          simp [h]
        rw [hfind]
        have hb := evalFunGraphInner_computesFun₁ (env := env) a h_arg
          (graph := tl) (x := x) (y := y)
        rw [if_neg (show ¬ ((x == a) = true) by simpa using h)] at hb
        exact WhileComputes.step (by simp [DataEncode.encode]) hb ih
  -- Initial accumulator: `(graph, none)`.
  have h_init : (toPair p_graph .empty).ComputesEnc env (graph, (none : Option β)) :=
    toPair_computesEnc h_graph (empty_computes)
  exact snd_ComputesEnc (while_computes h_init (h_loop graph))


lemma evalFunGraph_Computes_of_fun
    [Fintype α]
    {p_graph p_arg : PB}
    {a : α}
    {f : α → β}
    (h_graph : p_graph.ComputesEnc env (Fintype.elems.toList.map (fun a => (a, f a))))
    (h_arg : p_arg.ComputesEnc env a) :
    (PB.evalFunGraph p_graph p_arg).head.ComputesEnc env (f a) := by
  classical
  have heq : ∀ (L : List α), a ∈ L →
      ((L.map (fun a' => (a', f a'))).find?
        (fun p => p.1 = a)).map (·.2) = Option.some (f a) := by
    intro L hmem
    induction L with
    | nil => exact absurd hmem (by simp)
    | cons hd tl ih => grind
  have h := PB.evalFunGraph_computes h_graph h_arg
  rw [heq _ (Finset.mem_toList.mpr (Fintype.complete a))] at h
  apply PB.head_computes h


end PB

end RoseTreeMachine

end Turing
