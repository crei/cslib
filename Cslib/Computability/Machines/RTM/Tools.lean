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

- `PB.foldl` - left fold of a body over a list, implemented with `while_`
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

/-- The infinite loop. -/
def diverge : PB := .while_ (.toPair (.cons .empty .empty) .empty) fun acc => acc

/-- Inversion for `ProgSem` on a variable: the result is exactly the looked-up value, and the
time charged equals the size of that value. -/
private lemma progSem_var_inv {σ : List Value} {i : ℕ} {r : Value} {t s : ℕ}
    (h : ProgSem σ (.var i) r t s) : r = σ[i]?.getD Value.empty ∧ t = r.size := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Helper for `diverge_not_progSem`: a `while_` loop whose body is the identity closure
`fun acc => acc` never terminates as long as the current accumulator's head is non-empty,
so it has no `WhileSem` derivation. Proved by strong induction on the loop's running time. -/
private lemma diverge_while_false : ∀ (t_w : ℕ) {σ : List Value} {acc r : Data} {s_w : ℕ},
    WhileSem (.closure (.var σ.length) σ) acc r t_w s_w →
    acc.asList.head?.getD (Data.l []) ≠ Data.l [] → False := by
  intro t_w
  induction t_w using Nat.strong_induction_on with
  | _ t_w ih =>
    intro σ acc r s_w hw h_head
    cases hw with
    | halt h_stop => exact h_head h_stop
    | step h_cont h_app h_rest =>
      rename_i v t_b s_b t_r s_r
      cases h_app with
      | mk h_b =>
        obtain ⟨hval, ht⟩ := progSem_var_inv h_b
        have : v = acc := by simpa using hval
        subst this
        have hpos : 0 < t_b := by rw [ht, Value.size_data]; simp
        exact ih t_r (by omega) h_rest h_head

/-- `diverge` has no `ProgSem` derivation: it genuinely diverges. -/
lemma diverge_not_progSem {out : Value} {t s : ℕ} :
    ¬ ProgSem env (diverge env.length) out t s := by
  intro h
  cases h with
  | while_ h_init h_body h_while =>
    cases h_body
    cases h_init with
    | cons h₁ h₂ => exact diverge_while_false _ h_while (by cases h₁; simp)

lemma diverge_computes {out : Value} : ¬ diverge.Computes env out := by
  intro h_div
  obtain ⟨t, s, hps⟩ := h_div []
  simp only [List.append_nil, List.length_nil, Nat.add_zero] at hps
  exact diverge_not_progSem hps


/-- `foldl f init list`: left fold of `f` (taking `acc` then `el`) over `list`. -/
def foldl (f : PB → PB → PB) (init list : PB) : PB :=
  snd (PB.while_ (toPair list init)
    (fun st => elim st.fst empty
      (fun el rest => toPair rest (f st.snd el))))

lemma foldl_computes
    {p_f : PB → PB → PB} {p_init p_list : PB}
    {init : α} {list : List β} {f : α → β → α}
    (h_init : p_init.ComputesEnc env init)
    (h_list : p_list.ComputesEnc env list)
    (h_f : ∀ {e : List Value} {pa pb : PB} {a : α} {b : β},
      pa.ComputesEnc e a → pb.ComputesEnc e b → (p_f pa pb).ComputesEnc e (f a b)) :
    (foldl p_f p_init p_list).ComputesEnc env (list.foldl f init) := by
  -- One iteration of the loop body: from `(hd :: tl, acc)` to `(tl, f acc hd)`.
  have foldl_step : ∀ (acc : α) (hd : β) (tl : List β),
      computesFun₁ env (.data (DataEncode.encode (hd :: tl, acc)))
        (fun st => elim st.fst empty (fun el rest => toPair rest (p_f st.snd el)))
        (.data (DataEncode.encode (tl, f acc hd))) := by
    intro acc hd tl
    apply computesFun₁_branch
    intro ext
    refine elim_cons_computes
      (fst_ComputesEnc (var_computes_fresh ext [])) (computesFun₂_branch2 ?_)
    intro ext2
    refine toPair_computesEnc (var_computes_fresh2 ext2 []) (h_f ?_ (var_computes_fresh ext2 _))
    exact snd_ComputesEnc
        (((var_computes_fresh ext []).extend ext2).extend [_, _])
  -- Iterate the body from `(li, acc)` to its final folded accumulator `([], li.foldl f acc)`.
  have h_loop : ∀ (li : List β) (acc : α),
      WhileComputes env
        (fun st => elim st.fst empty
          (fun el rest => toPair rest (p_f st.snd el)))
        (DataEncode.encode (li, acc))
        (DataEncode.encode (([] : List β), li.foldl f acc)) := by
    intro li
    induction li with
    | nil =>
      intro acc
      apply WhileComputes.halt
      simp [DataEncode.encode]
    | cons hd tl ih =>
      intro acc
      simp only [List.foldl_cons]
      exact WhileComputes.step (by simp [DataEncode.encode]) (foldl_step acc hd tl) (ih (f acc hd))
  exact snd_ComputesEnc (while_computes
    (toPair_computesEnc h_list h_init) (h_loop list init))

/-- Models `List.reverse`. -/
def reverse (x : PB) : PB :=
  foldl (fun acc el => cons el acc) empty x

lemma reverse_computes {p : PB} {l : List α} (h : p.ComputesEnc env l) :
    (reverse p).ComputesEnc env l.reverse := by
  have h_fold : l.reverse = l.foldl (fun acc el => el :: acc) [] := by simp
  rw [h_fold]
  apply foldl_computes (by simp) h
  intro env p_tl p_hd tl hd h_tl h_hd
  exact cons_computesEnc h_hd h_tl

/-- Models `List.map`. -/
def listMap (x : PB) (f : PB → PB) : PB :=
  reverse (foldl (fun acc el => cons (f el) acc) empty x)

lemma listMap_computes
    {p_l : PB} {p_f : PB → PB}
    {l : List α}
    {f : α → β}
    (h_l : p_l.ComputesEnc env l)
    (h_f : ∀ {e : List Value} {px : PB} {x : α},
      px.ComputesEnc e x → (p_f px).ComputesEnc e (f x)) :
    (listMap p_l p_f).ComputesEnc env (l.map f) := by
  have : l.map f = (l.foldl (fun acc el => f el :: acc) []).reverse := by simp
  rw [this]
  apply reverse_computes (foldl_computes (empty_computesEnc β) h_l ?_)
  intro e p_acc p_el acc el h_acc h_el
  exact cons_computesEnc (h_f h_el) h_acc


/-- Models `List.reduceOption`, i.e. discards `none` elements, keeping the `some` payloads. -/
def listReduceOption (x : PB) : PB :=
  reverse (foldl
    (fun acc el => optionElim el acc (fun y => PB.cons y acc))
    empty x)

lemma listReduceOption_computes {p : PB} {l : List (Option α)} (h : p.ComputesEnc env l) :
    (listReduceOption p).ComputesEnc env l.reduceOption := by
  have h_reduceOption_via_fold (m : List (Option α)) : ∀ (a : List α),
      (m.foldl (fun acc el => match el with | .none => acc | .some y => y :: acc) a).reverse
        = a.reverse ++ m.reduceOption := by
    induction m with
    | nil => simp
    | cons hd tl ih =>
      cases hd with | none | some _ => simp [ih]
  rw [show l.reduceOption = (l.foldl _ []).reverse
      from by simpa using (h_reduceOption_via_fold l []).symm]
  apply reverse_computes ((foldl_computes (empty_computesEnc α) h) ?_)
  intro e p_acc p_el acc el h_acc h_el
  cases el with
  | none => exact optionElim_computesEnc_none h_el h_acc
  | some y =>
    apply optionElim_computesEnc_some h_el (computesFun₂_branch (fun ext => ?_))
    exact cons_computesEnc (var_computes_fresh ext _) ((h_acc.extend ext).extend _)

/-- Models `List.head?` -/
def listHeadOption (input : PB) : PB :=
  PB.elim input empty (fun hd _tl => some hd)

lemma listHeadOption_computes {p : PB} {l : List α} (h : p.ComputesEnc env l) :
    (listHeadOption p).ComputesEnc env l.head? := by
  cases l with
  | nil =>
    apply PB.elim_nil_computes h (empty_computes)
  | cons hd tl =>
    apply PB.elim_cons_computes h (PB.computesFun₂_branch2 (fun ext => ?_))
    refine PB.cons_computes (var_computes_fresh ext _) empty_computes

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
