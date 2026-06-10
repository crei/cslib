/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V3.Prog
public import Cslib.Computability.Machines.RoseTreeMachine.V3.DataEncode
public import Cslib.Computability.Machines.RoseTreeMachine.V3.PB

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- Program that evaluates to the constant `a`. -/
def constant (a : Data) : PB := match a with
  | Data.l [] => .empty
  | Data.l (x :: xs) => .cons (constant x) (constant (Data.l xs))

@[simp]
lemma constant_computes {n : ℕ} {env : List Data} {a : Data} :
    ProgSem env (constant a n) a a.size a.size := by
  induction a using Data.inductionL with
  | nil => simp [constant, PB.empty, ProgSem.empty]
  | cons x xs ihx ihxs =>
    simpa [constant] using ProgSem.cons ihx ihxs

def encConst {α : Type} [DataEncode α] (a : α) : PB := constant (DataEncode.encode a)


/-- Returns the tail of a list-valued builder. -/
def PB.tail (x : PB) : PB := .elim x .empty (fun _hd tl => tl)

/-- Returns the head of a list-valued builder (`Data.l []` when empty). -/
def PB.head (x : PB) : PB := .elim x .empty (fun hd _tl => hd)

@[computes]
lemma PB.tail_computes {env : List Data} {x : PB} {dx : Data} (hx : PB.computes env x dx) :
    PB.computes env (.tail x) (Data.l dx.asList.tail) := by
  obtain ⟨dx⟩ := dx
  cases dx with
  | nil => grind [PB.tail]
  | cons hd tl =>
    refine PB.elim_cons_computes hx ?_
    intro ext
    simpa using PB.var_computesFun ext

@[computes]
lemma PB.head_computes {env : List Data} {x : PB} {dx : Data}
    (hx : PB.computes env x dx) :
    PB.computes env (PB.head x) (dx.asList.headD (Data.l [])) := by
  obtain ⟨dx⟩ := dx
  cases dx with
  | nil => grind [PB.head]
  | cons hd tl =>
    refine PB.elim_cons_computes hx ?_
    intro ext
    simpa using PB.var_computesFun_zero _

def PB.fst (x : PB) : PB := PB.head x

/-- Compute `fun x => x.snd`. -/
def PB.snd (x : PB) : PB := PB.head (PB.tail x)

/-- Compute `fun x => Option.some x`. -/
def PB.some (x : PB) : PB := PB.cons x PB.empty

def PB.optionElim (x noneCase : PB) (someCase : PB → PB) : PB :=
  PB.elim x noneCase (fun x _ => someCase x)

----------------- Typed computation

-- @[simp]
-- lemma PB.atSlot_last_computes_enc {α : Type} [DataEncode α]
--     {env ext : List Data} {a : α} :
--     PB.computes_enc (env ++ ext ++ [DataEncode.encode a])
--       (PB.atSlot (env.length + ext.length)) a :=
--   PB.atSlot_last_computes_at

-- @[simp]
-- lemma PB.atSlot_last_computes_enc_right {α : Type} [DataEncode α]
--     {env ext : List Data} {a : α} :
--     PB.computes_enc (env ++ (ext ++ [DataEncode.encode a]))
--       (PB.atSlot (env.length + ext.length)) a :=
--   PB.atSlot_last_computes_at_right

-- /-- Encoded body-of-binder hypothesis: the body computes a typed value `a`
-- under any outer env extension. -/
-- abbrev PB.computes_at_body_encoded {α : Type} [DataEncode α]
--     (env : List Data) (bindings : List Data)
--     (mkBody : (Fin bindings.length → PB) → PB) (a : α) : Prop :=
--   PB.computes_at_body env bindings mkBody (DataEncode.encode a)

-- abbrev PB.computes_at_body₁_encoded {α β : Type} [DataEncode α] [DataEncode β]
--     (env : List Data) (a : α) (body : PB → PB) (b : β) : Prop :=
--   PB.computes_at_body₁ env (DataEncode.encode a) body (DataEncode.encode b)

-- abbrev PB.computes_at_body₂_encoded {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]
--     (env : List Data) (a : α) (b : β) (body : PB → PB → PB) (c : γ) : Prop :=
--   PB.computes_at_body₂ env (DataEncode.encode a) (DataEncode.encode b) body (DataEncode.encode c)

@[computes]
lemma PB.fst_computes_enc {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {a : α × β}
    (hx : PB.computes_enc env x a) :
    PB.computes_enc env (PB.fst x) a.fst := by
  obtain ⟨a, b⟩ := a
  simpa [Data.asList] using PB.head_computes hx

@[computes]
lemma PB.snd_computes_enc {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {a : α × β}
    (hx : PB.computes_enc env x a) :
    PB.computes_enc env (PB.snd x) a.snd := by
  obtain ⟨a, b⟩ := a
  simpa [Data.asList] using PB.head_computes (PB.tail_computes hx)

@[computes]
lemma PB.some_computes_enc {α : Type} [DataEncode α]
    {env : List Data} {x : PB} {a : α}
    (hx : PB.computes_enc env x a) :
    PB.computes_enc env (PB.some x) (Option.some a) := by
  simpa using PB.cons_computes hx PB.empty_computes

lemma PB.optionElim_computes_none {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x noneCase : PB} {someCase : PB → PB}
    (hx : x.computes_enc env (none : Option α))
    {a : β}
    (h_none : noneCase.computes_enc env a) :
    (PB.optionElim x noneCase someCase).computes_enc env a := by
  apply PB.elim_nil_computes hx h_none

/-- `some`-branch of `PB.optionElim`. Since `some a = Data.l [encode a]`, eliminating it binds the
contained value `encode a` together with the (empty) list tail `Data.l []`, so the obligation is a
`computesFun₂` whose second binding is the unused empty tail. -/
lemma PB.optionElim_computes_some {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {x : PB} {noneCase : PB} {someCase : PB → PB}
    {a : α}
    (hx : x.computes_enc env (Option.some a))
    {b : β}
    (h_some : PB.computesFun₂ env (DataEncode.encode a) (Data.l []) (fun v _ => someCase v)
      (DataEncode.encode b)) :
    (PB.optionElim x noneCase someCase).computes_enc env b := by
  exact PB.elim_cons_computes hx h_some

/-- Build a `FoldSem` over an encoded list: starting from accumulator `a`, threading `f` through
the elements of `l`, given that the (already depth-instantiated) `body` realises one step
`acc, el ↦ f acc el` under the environment extended by the two encoded bindings `[encode acc,
encode el]`. -/
lemma PB.foldSem_encode {α β : Type} [DataEncode α] [DataEncode β]
    {σ : List Data} {body : Prog} {f : α → β → α}
    (hbody : ∀ acc el, ∃ t s,
      ProgSem (σ ++ [DataEncode.encode acc, DataEncode.encode el]) body
        (DataEncode.encode (f acc el)) t s) :
    ∀ (a : α) (l : List β), ∃ t s,
      FoldSem σ (DataEncode.encode a) (l.map DataEncode.encode) body
        (DataEncode.encode (l.foldl f a)) t s := by
  intro a l
  induction l generalizing a with
  | nil => exact ⟨0, 0, FoldSem.nil⟩
  | cons x xs ih =>
    obtain ⟨tb, sb, hb⟩ := hbody a x
    obtain ⟨tr, sr, hr⟩ := ih (f a x)
    exact ⟨_, _, FoldSem.cons hb hr⟩

/-- Typed `fold`: with `init` computing the accumulator `a`, `list` computing the elements `l`, and
`body` realising one step of `f` over its two bindings, `PB.fold body init list` computes
`l.foldl f a`. -/
lemma PB.fold_computes_enc
    {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {init list : PB} {body : PB → PB → PB}
    {a : α} {l : List β} {f : α → β → α}
    (hi : init.computes_enc env a)
    (hl : list.computes_enc env l)
    (hbody : ∀ acc el, PB.computesFun₂ env (DataEncode.encode acc) (DataEncode.encode el) body
        (DataEncode.encode (f acc el))) :
    PB.computes_enc env (PB.fold body init list) (l.foldl f a) := by
  intro ext
  obtain ⟨ti, si, hinit⟩ := hi ext
  obtain ⟨tl, sl, hlist⟩ := hl ext
  have hlist' : ProgSem (env ++ ext) (list (env.length + ext.length))
      (Data.l (l.map DataEncode.encode)) tl sl := hlist
  obtain ⟨tf, sf, hf⟩ :=
    PB.foldSem_encode (σ := env ++ ext) (f := f)
      (body := body (PB.var (env.length + ext.length)) (PB.var (env.length + ext.length + 1))
        (env.length + ext.length + 2))
      (fun acc el => hbody acc el ext) a l
  simp only [PB.fold]
  exact ⟨_, _, ProgSem.fold hinit hlist' hf⟩


end RoseTreeMachine

end Turing
