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


def isEq (x y : PB) : PB :=
  ifEq x y (constantEnc true) (constantEnc false)

lemma isEq_computes {α : Type} [DecidableEq α] [DataEncode α]
    {a b : α} {pa pb : PB}
    (ha : pa.ComputesEnc env a) (hb : pb.ComputesEnc env b) :
    (isEq pa pb).ComputesEnc env (a == b) := by
  by_cases h : a = b
  · rw [show (a == b) = true by simp [h]]
    exact PB.ifeq_eq_computes ha (h ▸ hb) (constantEnc_computesEnc (a := true))
  · rw [show (a == b) = false by simp [h]]
    exact PB.ifeq_ne_computes ha hb (fun heq => h (DataEncode.h_inj heq))
      (constantEnc_computesEnc (a := false))

def boolNot (x : PB) : PB :=
  isEq x (constantEnc false)

lemma boolNot_computes {x : PB} {b : Bool} (hx : x.ComputesEnc env b) :
    (boolNot x).ComputesEnc env (!b) := by
  rw [show not b = (b == false) by simp]
  exact isEq_computes hx (constantEnc_computesEnc (a := false))

def boolXor (x y : PB) : PB :=
  boolNot (isEq x y)

lemma boolXor_computes {x y : PB} {b1 b2 : Bool}
    (hx : x.ComputesEnc env b1) (hy : y.ComputesEnc env b2) :
    (boolXor x y).ComputesEnc env (b1 ^^ b2) := by
  exact boolNot_computes (isEq_computes hx hy)

def boolIte (cond thenBranch elseBranch : PB) : PB :=
  ifEq cond (constantEnc true) thenBranch elseBranch

lemma boolIte_computes {p_cond p_then p_else : PB} {cond : Bool} {x y : α}
    (h_cond : p_cond.ComputesEnc env cond)
    (h_then : p_then.ComputesEnc env x)
    (h_else : p_else.ComputesEnc env y) :
    (boolIte p_cond p_then p_else).ComputesEnc env (if cond then x else y) := by
  by_cases h : cond
  · rw [if_pos h]
    exact ifeq_eq_computes h_cond (h ▸ constantEnc_computesEnc (a := true)) h_then
  · rw [if_neg h]
    refine ifeq_ne_computes h_cond (constantEnc_computesEnc (a := true)) ?_ h_else
    simp [h, DataEncode.h_inj.eq_iff]

def boolAnd (x y : PB) : PB :=
  boolIte x y (constantEnc false)

lemma boolAnd_computes {x y : PB} {b1 b2 : Bool}
    (hx : x.ComputesEnc env b1) (hy : y.ComputesEnc env b2) :
    (boolAnd x y).ComputesEnc env (b1 && b2) := by
  rw [show (b1 && b2) = if b1 then b2 else false by simp]
  exact boolIte_computes hx hy (constantEnc_computesEnc (a := false))

def boolOr (x y : PB) : PB :=
  boolIte x (constantEnc true) y

lemma boolOr_computes {x y : PB} {b1 b2 : Bool}
    (hx : x.ComputesEnc env b1) (hy : y.ComputesEnc env b2) :
    (boolOr x y).ComputesEnc env (b1 || b2) := by
  rw [show (b1 || b2) = if b1 then true else b2 by simp]
  exact boolIte_computes hx (constantEnc_computesEnc (a := true)) hy

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

def listAppend (x y : PB) : PB :=
  foldl (fun acc el => cons el acc) y (reverse x)

lemma listAppend_computes {p_x p_y : PB} {l1 l2 : List α}
    (h_x : p_x.ComputesEnc env l1) (h_y : p_y.ComputesEnc env l2) :
    (listAppend p_x p_y).ComputesEnc env (l1 ++ l2) := by
  have h_eq : l1 ++ l2 = l1.reverse.foldl (fun acc el => el :: acc) l2 := by
    simp
  rw [h_eq]
  apply foldl_computes h_y (reverse_computes h_x) ?_
  intro e p_acc p_el acc el h_acc h_el
  exact cons_computesEnc h_el h_acc

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

/-- The fold step used by `succBin`: given the running `(carry, acc)` and the next `bit`, emit the
new carry `carry && bit` and prepend the output bit `carry ^^ bit`. -/
def succBinStep (p : Bool × List Bool) (bit : Bool) : Bool × List Bool :=
  (p.1 && bit, (p.1 ^^ bit) :: p.2)

def succBin (n : List Bool) : List Bool :=
  let (final_carry, rev_res) := n.foldl succBinStep (true, [])
  (if final_carry then true :: rev_res else rev_res).reverse

/-- With carry `false`, the fold never produces a carry and simply reverses the remaining bits onto
the accumulator. -/
lemma foldl_succBinStep_false (bs : List Bool) (acc : List Bool) :
    bs.foldl succBinStep (false, acc) = (false, bs.reverse ++ acc) := by
  induction bs generalizing acc with
  | nil => simp
  | cons hd tl ih => simp [succBinStep, ih (hd :: acc)]

/-- The accumulator threads through the fold independently of the computed carry and output bits. -/
lemma foldl_succBinStep_acc (bs : List Bool) (c : Bool) (acc : List Bool) :
    bs.foldl succBinStep (c, acc)
      = ((bs.foldl succBinStep (c, [])).1, (bs.foldl succBinStep (c, [])).2 ++ acc) := by
  induction bs generalizing c acc with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, show succBinStep (c, acc) hd = (c && hd, (c ^^ hd) :: acc) from rfl,
      ih (c && hd) ((c ^^ hd) :: acc), List.foldl_cons,
      show succBinStep (c, ([] : List Bool)) hd = (c && hd, [c ^^ hd]) from rfl,
      ih (c && hd) [c ^^ hd]]
    simp

lemma succ_bin_correct (n : ℕ) : succBin n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rw [Nat.zero_bits]; rfl
  | bit b m hb ih =>
    rw [Nat.bits_append_bit m b hb]
    unfold succBin
    cases b with
    | false =>
      rw [List.foldl_cons,
        show succBinStep (true, []) false = (false, [true]) from rfl,
        foldl_succBinStep_false, Nat.bit_false_apply, Nat.bit1_bits]
      simp
    | true =>
      rw [List.foldl_cons,
        show succBinStep (true, []) true = (true, [false]) from rfl,
        foldl_succBinStep_acc, Nat.bit_true_apply,
        show 2 * m + 1 + 1 = 2 * (m + 1) from by omega,
        Nat.bit0_bits (m + 1) (Nat.succ_ne_zero m), ← ih]
      unfold succBin
      dsimp only
      split <;> simp [List.reverse_append]

def succ_foldl_body (st bit : PB) : PB :=
  let carry := st.fst
  let acc := st.snd
  toPair (boolAnd carry bit) (cons (boolXor carry bit) acc)

/-- Compute ℕ.succ (in its default binary encoding). -/
def succ (x : PB) : PB :=
  let loop_result := foldl
    succ_foldl_body
    (toPair (constantEnc true) empty)
    x
  let final_carry := loop_result.fst
  let result_rev := loop_result.snd
  -- If final carry, prepend 1; otherwise just reverse back
  reverse (boolIte final_carry (cons (constantEnc true) result_rev) result_rev)

/-- The `succ` program computes `succBin` on the underlying bit list, independently of whether
that list is a canonical ℕ encoding. -/
lemma succ_computes_list {p : PB} {l : List Bool} (h : p.ComputesEnc env l) :
    (succ p).ComputesEnc env (succBin l) := by
  have h_body : ∀ {e : List Value} {pa pb : PB} {a : Bool × List Bool} {b : Bool},
      pa.ComputesEnc e a → pb.ComputesEnc e b →
      (succ_foldl_body pa pb).ComputesEnc e
        ((fun (st : Bool × List Bool) bit => (st.1 && bit, (st.1 ^^ bit) :: st.2)) a b) := by
    intro e pa pb a b ha hb
    exact toPair_computesEnc (boolAnd_computes (fst_ComputesEnc ha) hb)
      (cons_computesEnc (boolXor_computes (fst_ComputesEnc ha) hb) (snd_ComputesEnc ha))
  have h_fold := foldl_computes
    (toPair_computesEnc (constantEnc_computesEnc (a := true)) (empty_computesEnc Bool))
    h h_body
  apply reverse_computes (boolIte_computes (fst_ComputesEnc h_fold) ?_ (snd_ComputesEnc h_fold))
  exact cons_computesEnc constantEnc_computesEnc (snd_ComputesEnc h_fold)

lemma succ_computes {p : PB} {n : ℕ} (h : p.ComputesEnc env n) :
    (succ p).ComputesEnc env (n + 1) := by
  change (succ p).ComputesEnc env (n + 1).bits
  rw [← succ_bin_correct]
  exact succ_computes_list h

/-- Computes addition of three bits, returning `(sum, carry)`. -/
def fullAdder (x y carry : Bool) : Bool × Bool :=
  (x ^^ y ^^ carry, (x && y) || (carry && (x ^^ y)))

/-- One ripple-carry step. The state `(toAdd, carry, acc)` carries the remaining bits of the second
addend (`toAdd`), the running `carry`, and the reversed output bits (`acc`). Each step consumes the
next bit of the first addend together with the front bit of `toAdd` (or `false` once `toAdd` is
exhausted), emitting the sum bit onto `acc`. -/
def addBinStep (p : List Bool × Bool × List Bool) (bit : Bool) : List Bool × Bool × List Bool :=
  match p.1 with
  | [] => ([], (fullAdder false bit p.2.1).2, (fullAdder false bit p.2.1).1 :: p.2.2)
  | a :: as => (as, (fullAdder a bit p.2.1).2, (fullAdder a bit p.2.1).1 :: p.2.2)

/-- Adds the bit lists `x` and `y` with an incoming `carry`. -/
def addCarry (carry : Bool) (x y : List Bool) : List Bool :=
  let (toAdd, finalCarry, rev) := x.foldl addBinStep (y, carry, [])
  rev.reverse ++ (if finalCarry then succBin toAdd else toAdd)

def addBin (x y : List Bool) : List Bool := addCarry false x y

/-- The accumulator threads through the `addBinStep` fold independently of the remaining addend and
carry. -/
lemma foldl_addBinStep_acc (xs ys : List Bool) (c : Bool) (acc : List Bool) :
    xs.foldl addBinStep (ys, c, acc)
      = ((xs.foldl addBinStep (ys, c, [])).1, (xs.foldl addBinStep (ys, c, [])).2.1,
         (xs.foldl addBinStep (ys, c, [])).2.2 ++ acc) := by
  induction xs generalizing ys c acc with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons]
    cases ys with
    | nil =>
      simp only [addBinStep]
      rw [ih [] _ _, ih [] _ [_]]
      simp
    | cons d ds =>
      simp only [addBinStep]
      rw [ih ds _ _, ih ds _ [_]]
      simp

/-- Evaluating `addBinStep` on `y.bits` exposes the next sum bit and carry via `fullAdder`,
independently of whether `y` is zero. -/
lemma addBinStep_bits (y : ℕ) (c b : Bool) (acc : List Bool) :
    addBinStep (y.bits, c, acc) b
      = (y.div2.bits, (fullAdder (Nat.bodd y) b c).2, (fullAdder (Nat.bodd y) b c).1 :: acc) := by
  cases y using Nat.binaryRec' with
  | zero => simp [addBinStep, Nat.zero_bits]
  | bit d m hd => rw [Nat.bits_append_bit m d hd]; simp [addBinStep]

/-- Peeling the first bit of the first addend in `addCarry`, when the second addend is `y.bits`. -/
lemma addCarry_cons_bits (c b : Bool) (xs : List Bool) (y : ℕ) :
    addCarry c (b :: xs) y.bits
      = (fullAdder (Nat.bodd y) b c).1
        :: addCarry (fullAdder (Nat.bodd y) b c).2 xs y.div2.bits := by
  unfold addCarry
  rw [List.foldl_cons, addBinStep_bits,
    foldl_addBinStep_acc xs y.div2.bits (fullAdder (Nat.bodd y) b c).2
      [(fullAdder (Nat.bodd y) b c).1]]
  simp [List.reverse_append]

lemma addCarry_correct (c : Bool) (x y : ℕ) :
    addCarry c x.bits y.bits = (x + y + c.toNat).bits := by
  induction x using Nat.binaryRec' generalizing c y with
  | zero => cases c <;> simp [addCarry, Nat.zero_bits, succ_bin_correct]
  | bit b m hb ih =>
    rw [Nat.bits_append_bit m b hb, addCarry_cons_bits, ih]
    have hy := Nat.bodd_add_div2 y
    rw [show Nat.bit b m + y + c.toNat
        = Nat.bit (fullAdder (Nat.bodd y) b c).1
            (m + y.div2 + (fullAdder (Nat.bodd y) b c).2.toNat) from by
          simp only [Nat.bit_val, fullAdder]
          cases b <;> cases c <;> cases hbd : Nat.bodd y <;> simp_all <;> omega]
    rw [Nat.bits_append_bit]
    rintro hzero
    have hb' : b = true := hb (by omega)
    subst hb'
    simp only [fullAdder] at hzero ⊢
    cases c <;> cases hbd : Nat.bodd y <;> simp_all

lemma addBin_correct (x y : ℕ) : addBin x.bits y.bits = (x + y).bits := by
  rw [addBin, addCarry_correct]
  simp

/-- The sum bit of a full adder, as a builder. -/
def addSumPB (a bit carry : PB) : PB := boolXor (boolXor a bit) carry

/-- The carry-out bit of a full adder, as a builder. -/
def addCarryPB (a bit carry : PB) : PB :=
  boolOr (boolAnd a bit) (boolAnd carry (boolXor a bit))

lemma addSumPB_computes {pa pbit pc : PB} {av bv cv : Bool}
    (ha : pa.ComputesEnc env av) (hbit : pbit.ComputesEnc env bv)
    (hc : pc.ComputesEnc env cv) :
    (addSumPB pa pbit pc).ComputesEnc env (fullAdder av bv cv).1 := by
  simp only [fullAdder, addSumPB]
  exact boolXor_computes (boolXor_computes ha hbit) hc

lemma addCarryPB_computes {pa pbit pc : PB} {av bv cv : Bool}
    (ha : pa.ComputesEnc env av) (hbit : pbit.ComputesEnc env bv)
    (hc : pc.ComputesEnc env cv) :
    (addCarryPB pa pbit pc).ComputesEnc env (fullAdder av bv cv).2 := by
  simp only [fullAdder, addCarryPB]
  exact boolOr_computes (boolAnd_computes ha hbit)
    (boolAnd_computes hc (boolXor_computes ha hbit))

/-- The fold body implementing `addBinStep`. The state encodes the triple `(toAdd, carry, acc)`:
consume the front bit of `toAdd` (or `false` once it is exhausted) together with the current bit
`bit` of the first addend, emitting the sum bit onto `acc` and threading the new carry. -/
def add_foldl_body (st bit : PB) : PB :=
  elim st.fst
    (toPair empty
      (toPair (addCarryPB (constantEnc false) bit st.snd.fst)
        (cons (addSumPB (constantEnc false) bit st.snd.fst) st.snd.snd)))
    (fun hd tl =>
      toPair tl
        (toPair (addCarryPB hd bit st.snd.fst)
          (cons (addSumPB hd bit st.snd.fst) st.snd.snd)))

/-- Compute binary addition in the default ℕ encoding. Mirrors `addBin`/`addCarry`: fold
`add_foldl_body` over the first addend `x` starting from state `(y, false, [])`, then reverse the
emitted bits and append the leftover high bits (incremented when a final carry remains). -/
def add (x y : PB) : PB :=
  let loop := foldl add_foldl_body (toPair y (toPair (constantEnc false) empty)) x
  listAppend (reverse loop.snd.snd) (boolIte loop.snd.fst (succ loop.fst) loop.fst)

/-- The `add` program computes `addBin` on the underlying bit lists, for any lists (not just
canonical ℕ encodings). -/
lemma add_computes_list {px py : PB} {l1 l2 : List Bool}
    (hx : px.ComputesEnc env l1) (hy : py.ComputesEnc env l2) :
    (add px py).ComputesEnc env (addBin l1 l2) := by
  have h_body : ∀ {e : List Value} {pa pb : PB}
      {a : List Bool × Bool × List Bool} {b : Bool},
      pa.ComputesEnc e a → pb.ComputesEnc e b →
      (add_foldl_body pa pb).ComputesEnc e (addBinStep a b) := by
    intro e pa pb a b ha hb
    obtain ⟨toAdd, carry, acc⟩ := a
    cases toAdd with
    | nil =>
      refine elim_nil_computes (fst_ComputesEnc ha) ?_
      exact toPair_computesEnc (empty_computesEnc Bool)
        (toPair_computesEnc
          (addCarryPB_computes constantEnc_computesEnc hb
            (fst_ComputesEnc (snd_ComputesEnc ha)))
          (cons_computesEnc
            (addSumPB_computes constantEnc_computesEnc hb
              (fst_ComputesEnc (snd_ComputesEnc ha)))
            (snd_ComputesEnc (snd_ComputesEnc ha))))
    | cons hd tl =>
      refine elim_cons_computes (fst_ComputesEnc ha) (computesFun₂_branch2 ?_)
      intro ext
      have ha' := (ha.extend ext).extend
        [Value.data (DataEncode.encode hd), Value.data (DataEncode.encode tl)]
      have hb' := (hb.extend ext).extend
        [Value.data (DataEncode.encode hd), Value.data (DataEncode.encode tl)]
      exact toPair_computesEnc (var_computes_fresh2 ext [])
        (toPair_computesEnc
          (addCarryPB_computes (var_computes_fresh ext _) hb'
            (fst_ComputesEnc (snd_ComputesEnc ha')))
          (cons_computesEnc
            (addSumPB_computes (var_computes_fresh ext _) hb'
              (fst_ComputesEnc (snd_ComputesEnc ha')))
            (snd_ComputesEnc (snd_ComputesEnc ha'))))
  have h_fold := foldl_computes
    (toPair_computesEnc hy
      (toPair_computesEnc (constantEnc_computesEnc (a := false)) (empty_computesEnc Bool)))
    hx h_body
  unfold addBin addCarry
  generalize hE : l1.foldl addBinStep (l2, false, []) = E at h_fold ⊢
  obtain ⟨tA, fC, rv⟩ := E
  unfold add
  exact listAppend_computes (reverse_computes (snd_ComputesEnc (snd_ComputesEnc h_fold)))
    (boolIte_computes (fst_ComputesEnc (snd_ComputesEnc h_fold))
      (succ_computes_list (fst_ComputesEnc h_fold))
      (fst_ComputesEnc h_fold))

lemma add_computes {px py : PB} {x y : ℕ}
    (hx : px.ComputesEnc env x) (hy : py.ComputesEnc env y) :
    (add px py).ComputesEnc env (x + y) := by
  change (add px py).ComputesEnc env (x + y).bits
  rw [← addBin_correct]
  exact add_computes_list hx hy

/-- Doubles a binary number (the math-level `· * 2`), keeping the canonical encoding: prepend a
`false` low bit, except for `0` (the empty list) which stays empty. -/
def doubleBin (l : List Bool) : List Bool :=
  match l with
  | [] => []
  | _ => false :: l

lemma doubleBin_bits (Y : ℕ) : doubleBin Y.bits = (2 * Y).bits := by
  cases Y using Nat.binaryRec' with
  | zero => simp [doubleBin, Nat.zero_bits]
  | bit b m hb =>
    have hYne : Nat.bit b m ≠ 0 := Nat.bit_ne_zero_iff.mpr hb
    rw [Nat.bits_append_bit m b hb, Nat.bit0_bits _ hYne, Nat.bits_append_bit m b hb]
    rfl

/-- One shift-and-add step of binary multiplication. The state `(shiftedY, product)` holds the
second addend shifted left by the current position and the running product. Each step doubles
`shiftedY` and, when the current bit of the multiplier is set, adds `shiftedY` into `product`. -/
def mulBinStep (st : List Bool × List Bool) (bit : Bool) : List Bool × List Bool :=
  (doubleBin st.1, if bit then addBin st.2 st.1 else st.2)

/-- Multiplies the bit lists `x` and `y` by folding `mulBinStep` over `x`. -/
def mulBin (x y : List Bool) : List Bool :=
  (x.foldl mulBinStep (y, [])).2

/-- Generalised correctness of the multiplication fold: folding `mulBinStep` over `n.bits`
starting from `(Y, P)` accumulates `P + n * Y` into the product component. -/
lemma mulBin_foldl (n Y P : ℕ) :
    (n.bits.foldl mulBinStep (Y.bits, P.bits)).2 = (P + n * Y).bits := by
  induction n using Nat.binaryRec' generalizing Y P with
  | zero => simp [Nat.zero_bits]
  | bit b m hb ih =>
    rw [Nat.bits_append_bit m b hb, List.foldl_cons]
    have hstep : mulBinStep (Y.bits, P.bits) b
        = ((2 * Y).bits, (if b then P + Y else P).bits) := by
      cases b <;> simp [mulBinStep, doubleBin_bits, addBin_correct]
    rw [hstep, ih]
    congr 1
    have hb2 : (if b then P + Y else P) = P + b.toNat * Y := by cases b <;> simp
    rw [hb2, Nat.bit_val, ← Nat.mul_assoc, Nat.mul_comm m 2, Nat.add_mul]
    omega

lemma mulBin_correct (x y : ℕ) : mulBin x.bits y.bits = (x * y).bits := by
  have h := mulBin_foldl x y 0
  rw [Nat.zero_bits] at h
  unfold mulBin
  rw [h]
  simp

/-- The PB builder doubling a binary number, implementing `doubleBin`. -/
def doublePB (l : PB) : PB :=
  elim l empty (fun hd tl => cons (constantEnc false) (cons hd tl))

lemma doublePB_computes {p : PB} {l : List Bool} (h : p.ComputesEnc env l) :
    (doublePB p).ComputesEnc env (doubleBin l) := by
  cases l with
  | nil => exact elim_nil_computes h (empty_computesEnc Bool)
  | cons hd tl =>
    refine elim_cons_computes h (computesFun₂_branch2 ?_)
    intro ext
    exact cons_computesEnc constantEnc_computesEnc
      (cons_computesEnc (var_computes_fresh ext _) (var_computes_fresh2 ext []))

/-- The fold body implementing `mulBinStep`: double the shifted second addend and conditionally
add it to the running product. -/
def mulFoldlBody (st bit : PB) : PB :=
  toPair (doublePB st.fst) (boolIte bit (add st.snd st.fst) st.snd)

/-- Compute binary multiplication in the default ℕ encoding. Fold `mul_foldl_body` over the first
factor `x`, starting from state `(y, [])`; the product component of the final state is the result.
The second factor `y` is copied into the accumulator (rather than read from the environment). -/
def mul (x y : PB) : PB :=
  snd (foldl mulFoldlBody (toPair y empty) x)

lemma mul_computes {px py : PB} {x y : ℕ}
    (hx : px.ComputesEnc env x) (hy : py.ComputesEnc env y) :
    (mul px py).ComputesEnc env (x * y) := by
  have h_body : ∀ {e : List Value} {pa pb : PB}
      {a : List Bool × List Bool} {b : Bool},
      pa.ComputesEnc e a → pb.ComputesEnc e b →
      (mulFoldlBody pa pb).ComputesEnc e (mulBinStep a b) := by
    intro e pa pb a b ha hb
    refine toPair_computesEnc (doublePB_computes (fst_ComputesEnc ha)) ?_
    exact boolIte_computes hb
      (add_computes_list (snd_ComputesEnc ha) (fst_ComputesEnc ha)) (snd_ComputesEnc ha)
  change (mul px py).ComputesEnc env (x * y).bits
  rw [← mulBin_correct]
  exact snd_ComputesEnc (foldl_computes
    (toPair_computesEnc hy (empty_computesEnc Bool)) hx h_body)

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
