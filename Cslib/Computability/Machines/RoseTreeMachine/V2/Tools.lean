/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V2.PB

/-! # RoseTreeMachine V2 — Tools

Part of the RoseTreeMachine V2 development; see
`Cslib/Computability/Machines/RoseTreeMachine/V2.lean` for an overview.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- Program that evaluates to the constant `a`. -/
def constant (a : Data) : PB := match a with
  | Data.l [] => PB.empty
  | Data.l (x :: xs) => PB.cons (constant x) (constant (Data.l xs))

lemma constant_computes {env : List Data} {a : Data} :
    (constant a).computes_at env a := by
  induction a using Data.inductionL with
  | nil => simp [constant]
  | cons x xs ihx ihxs =>
    simpa [constant] using PB.cons_computes_at ihx ihxs

def encConst {α : Type} [DataEncode α] (a : α) : PB := constant (DataEncode.encode a)

def PB.ifEq (a b : PB) (then_ else_ : PB) : PB :=
  .elim (PB.eq a b)
    else_
    fun _ _ => then_

lemma PB.ifEq_computes_at {env : List Data} {a b then_ else_ : PB} {da db dr : Data}
    (ha : PB.computes_at env a da) (hb : PB.computes_at env b db)
    (hthen : da = db → PB.computes_at env then_ dr)
    (helse : da ≠ db → PB.computes_at env else_ dr) :
    (PB.ifEq a b then_ else_).computes_at env dr := by
  unfold PB.ifEq
  by_cases h : da = db
  · have heq : PB.computes_at env (PB.eq a b) (Data.l [Data.l []]) := by
      simpa [h] using PB.eq_computes_at ha hb
    refine PB.elim_cons_computes_at heq ?_
    intro ext
    have h' := (hthen h).extend (ext := ext ++ [Data.l [], Data.l []])
    simpa [List.append_assoc] using h'
  · have heq : PB.computes_at env (PB.eq a b) (Data.l []) := by
      simpa [h] using PB.eq_computes_at ha hb
    exact PB.elim_nil_computes_at heq (helse h)

------------------------------------------------------
----------- Tools
-----------------------------------------------------------


def PB.fst (x : PB) : PB := head x

-- Compute fun x => x.snd
def PB.snd (x : PB) : PB := head (tail x)

-- Compute x => Option.some x
def PB.some (x : PB) : PB := cons x empty

def PB.optionElim (x : PB) (noneCase : PB) (someCase : PB → PB) : PB :=
  elim x noneCase (fun hd _ => someCase hd)

----------------- Typed computation

-- def PB.computes_encoded {α β : Type} [DataEncode α] [DataEncode β] (x : PB) (f : α → β) : Prop :=
--     PB.computes x (fun DataEncode.encode a)

def PB.computes_at_encoded {α : Type} [DataEncode α] (env : List Data) (x : PB) (a : α) : Prop :=
    PB.computes_at env x (DataEncode.encode a)

@[simp]
lemma PB.atSlot_last_computes_at_encoded {α : Type} [DataEncode α]
    {env ext : List Data} {a : α} :
    PB.computes_at_encoded (env ++ ext ++ [DataEncode.encode a])
      (PB.atSlot (env.length + ext.length)) a :=
  PB.atSlot_last_computes_at

@[simp]
lemma PB.atSlot_last_computes_at_encoded_right {α : Type} [DataEncode α]
    {env ext : List Data} {a : α} :
    PB.computes_at_encoded (env ++ (ext ++ [DataEncode.encode a]))
      (PB.atSlot (env.length + ext.length)) a :=
  PB.atSlot_last_computes_at_right

/-- Encoded body-of-binder hypothesis: the body computes a typed value `a`
under any outer env extension. -/
abbrev PB.computes_at_body_encoded {α : Type} [DataEncode α]
    (env : List Data) (bindings : List Data)
    (mkBody : (Fin bindings.length → PB) → PB) (a : α) : Prop :=
  PB.computes_at_body env bindings mkBody (DataEncode.encode a)

abbrev PB.computes_at_body₁_encoded {α β : Type} [DataEncode α] [DataEncode β]
    (env : List Data) (a : α) (body : PB → PB) (b : β) : Prop :=
  PB.computes_at_body₁ env (DataEncode.encode a) body (DataEncode.encode b)

abbrev PB.computes_at_body₂_encoded {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]
    (env : List Data) (a : α) (b : β) (body : PB → PB → PB) (c : γ) : Prop :=
  PB.computes_at_body₂ env (DataEncode.encode a) (DataEncode.encode b) body (DataEncode.encode c)

lemma PB.fst_computes_at_encoded {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {a : α × β}
    (hx : PB.computes_at_encoded env x a) :
    PB.computes_at_encoded env (PB.fst x) a.fst := by
  obtain ⟨a, b⟩ := a
  simpa [Data.asList] using PB.head_computes_at hx

lemma PB.snd_computes_at_encoded {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {a : α × β}
    (hx : PB.computes_at_encoded env x a) :
    PB.computes_at_encoded env (PB.snd x) a.snd := by
  obtain ⟨a, b⟩ := a
  simpa [Data.asList] using PB.head_computes_at (PB.tail_computes_at hx)

lemma PB.some_computes_at_encoded {α : Type} [DataEncode α]
    {env : List Data} {x : PB} {a : α}
    (hx : PB.computes_at_encoded env x a) :
    PB.computes_at_encoded env (PB.some x) (Option.some a) := by
  apply PB.cons_computes_at hx PB.empty_computes_at

lemma PB.optionElim_computes_none {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {noneCase : PB} {someCase : PB → PB}
    (hx : x.computes_at_encoded env (none : Option α))
    {a : β}
    (h_none : noneCase.computes_at_encoded env a) :
    (PB.optionElim x noneCase someCase).computes_at_encoded env a := by
  apply PB.elim_nil_computes_at hx h_none

lemma PB.optionElim_computes_some {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {noneCase : PB} {someCase : PB → PB}
    {a : α}
    (hx : x.computes_at_encoded env (Option.some a))
    {b : β}
    (h_some : PB.computes_at_body₁_encoded env a someCase b) :
    (PB.optionElim x noneCase someCase).computes_at_encoded env b := by
  apply PB.elim_cons_computes_at hx
  intro ext
  simpa [List.append_assoc] using (h_some ext).extend

lemma PB.letIn_computes_at_encoded {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {val : PB} {body : PB → PB} {v : α} {b : β}
    (hv : val.computes_at_encoded env v)
    (hbody : PB.computes_at_body₁_encoded env v body b) :
    (PB.letIn val body).computes_at_encoded env b :=
  PB.letIn_computes_at hv hbody

/-- Encoded variant of `PB.fold_computes_at`: typed accumulator `a : α`, typed
list elements of type `β`, and a typed step function `f : α → β → α`. The body
hypothesis is `PB.computes_at_body₂_encoded` parameterised over `acc : α` and
`el : β`. -/
lemma PB.fold_computes_at_encoded
    {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {init list : PB} {body : PB → PB → PB}
    {a : α} {l : List β} {f : α → β → α}
    (hi : init.computes_at_encoded env a)
    (hl : list.computes_at_encoded env l)
    (hbody : ∀ acc el, PB.computes_at_body₂_encoded env acc el body (f acc el)) :
    PB.computes_at_encoded env (PB.fold body init list) (l.foldl f a) := by
  intro ext
  simp only [PB.fold]
  have hl' :
      (list (env.length + ext.length)).eval (env ++ ext)
        = .some (Data.l (l.map DataEncode.encode)) := hl ext
  refine Prog.fold_eval (hi ext) hl'
    (fun k => DataEncode.encode ((l.take k).foldl f a)) rfl (by simp) ?_
  intro k hk
  have hk' : k < l.length := by simpa using hk
  have h := (hbody ((l.take k).foldl f a) l[k] ext).here
  have hfoldl_succ :
      (l.take (k+1)).foldl f a = f ((l.take k).foldl f a) l[k] := by
    rw [List.take_succ, List.foldl_append]
    simp [List.getElem?_eq_getElem hk']
  have hget : (l.map DataEncode.encode)[k] = DataEncode.encode l[k] := by simp
  simp only [hget, hfoldl_succ]
  simpa [PB.atSlot, List.append_assoc] using h
-------------------------------------------------------------------
---------------- Universal Turing Machine (simulation of a SingleTapeTM)
---------------------------------------------------------------------------


end RoseTreeMachine

end Turing
