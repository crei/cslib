/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.PB
public import Cslib.Computability.Machines.RTM.DataEncode

/-! # RoseTreeMachine V4 — Tools

Derived program-builder combinators. Because the V4 builder keeps the same HOAS `elim`
signature as the first-order development, these definitions are identical to their
counterparts there; only the underlying semantics (functional `elim`/`while_`) differs.
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

/-- `fold body init list`: left fold of `body` (taking `acc` then `el`) over `list`.

Implemented with `while_` over a `[remaining, acc]` pair: the loop halts once `remaining`
(the *head* of the accumulator, which is what `while_` inspects) becomes empty; otherwise it
splits off the first element `el`, updates the accumulator to `[rest, body acc el]`, and
continues. The fold's result is the final `acc` (the second component). -/
def fold (body : PB → PB → PB) (init list : PB) : PB :=
  snd (PB.while_ (PB.toPair list init)
    (fun st => elim (PB.fst st) empty
      (fun el rest => toPair rest (body (PB.snd st) el))))



end PB

end RoseTreeMachine

end Turing
