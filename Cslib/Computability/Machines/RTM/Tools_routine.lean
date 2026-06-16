/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.List.ReduceOption
public import Cslib.Computability.Machines.RTM.Routine
public import Cslib.Computability.Machines.RTM.DataEncode


@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace Routine

variable {env : List Value}
variable {α : Type} [DataEncode α]
variable {β : Type} [DataEncode β]
variable {γ δ : Type} [DataEncode γ] [DataEncode δ]


def encode (x : Routine α) : Routine Data where
  impl := x.impl
  valid := x.valid
  sem env h := ⟨DataEncode.encode (x.sem env h).val, (x.sem env h).property⟩

def decode (x : Routine Data) : Routine α where
  impl := x.impl
  valid env := ∃ (h : x.valid env), ∃ a : α, (x.sem env h).val = DataEncode.encode a
  sem env h := -- TODO simplify
    ⟨(DataEncode.decode (x.sem env h.fst).val).get (by
        obtain ⟨a, ha⟩ := h.snd
        rw [ha, DataEncode.encodek]; rfl), by
      have hkey : DataEncode.encode (α := α)
          ((DataEncode.decode (x.sem env h.fst).val).get (by
            obtain ⟨a, ha⟩ := h.snd; rw [ha, DataEncode.encodek]; rfl))
          = (x.sem env h.fst).val := by
        obtain ⟨a, ha⟩ := h.snd
        have hdec : DataEncode.decode (α := α) (x.sem env h.fst).val = some a := by
          rw [ha, DataEncode.encodek]
        grind
      rw [hkey]
      exact (x.sem env h.fst).property⟩

def progConstantData (a : Data) : Prog := match a with
  | .l [] => Prog.empty
  | .l (hd :: tl) => Prog.cons (progConstantData hd) (progConstantData (.l tl))

def constantData (a : Data) : Routine Data where
  impl _ := progConstantData a
  sem env h := ⟨a, sorry⟩

def constant {α : Type} [DataEncode α] (a : α) : Routine α where
  impl := (constantData (DataEncode.encode a)).impl
  valid _ := True
  sem env h := ⟨a, by sorry⟩

def tail (x : Routine Data) : Routine Data where
  impl := (Routine.elim x .empty (fun _hd tl => tl)).impl
  valid := x.valid
  sem env h := ⟨Data.l (x.sem env h).val.asList.tail, by
    have hv : (Routine.elim x .empty (fun _hd tl => tl)).valid env := by
      refine ⟨h, ?_⟩
      split
      · trivial
      · simp [Routine.var, DataEncode.encode]
    have heq : ∀ hv', ((Routine.elim x .empty (fun _hd tl => tl)).sem env hv').val
        = Data.l (x.sem env hv'.1).val.asList.tail := by
      intro hv'
      unfold Routine.elim
      dsimp only
      split
      · rename_i h_v
        simp [Routine.empty, h_v]
      · rename_i hd tl h_v
        simp [Routine.var, DataEncode.encode, DataEncode.decode, h_v]
    have hc := ((Routine.elim x .empty (fun _hd tl => tl)).sem env hv).property
    rw [heq] at hc
    exact hc⟩


/-- Returns the tail of a list-valued Routine (`[]` when empty). -/
def listTail (x : Routine (List α)) : Routine (List α) where
  impl := x.encode.tail.impl
  valid := x.valid
  sem env h := ⟨(x.sem env h).val.tail, by
    have hv : x.encode.tail.valid env := h
    have hc := (x.encode.tail.sem env hv).property
    have heq : (x.encode.tail.sem env hv).val
        = DataEncode.encode ((x.sem env h).val.tail) := by
      simp [Routine.tail, Routine.encode, DataEncode.encode]
    rw [heq] at hc
    exact hc⟩

def head (x : Routine Data) : Routine Data where
  impl := (Routine.elim x .empty (fun hd _tl => hd)).impl
  valid := x.valid
  sem env h := ⟨(x.sem env h).val.asList.headD (Data.empty), by
    have hv : (Routine.elim x .empty (fun hd _tl => hd)).valid env := by
      refine ⟨h, ?_⟩
      split
      · trivial
      · simp [Routine.var, DataEncode.encode]
    have heq : ∀ hv', ((Routine.elim x .empty (fun hd _tl => hd)).sem env hv').val
        = (x.sem env hv'.1).val.asList.headD (Data.empty) := by
      intro hv'
      unfold Routine.elim
      dsimp only
      split
      · rename_i h_v
        simp [Routine.empty, h_v]
      · rename_i hd tl h_v
        simp [Routine.var, DataEncode.encode, DataEncode.decode, h_v]
    have hc := ((Routine.elim x .empty (fun hd _tl => hd)).sem env hv).property
    rw [heq] at hc
    exact hc⟩

def listElim
    (x : Routine (List α))
    (em : Routine β)
    (cs : Routine α → Routine (List α) → Routine β) :
    Routine β where
  impl n := .elim (x.impl n) (em.impl n)
    (.fn (.fn ((cs (var n) (var (n + 1))).impl (n + 2))))
  valid env := ∃ h : x.valid env, (match (x.sem env h).val with
    | [] => em.valid env
    | hd :: tl => (cs (Routine.var env.length) (Routine.var (env.length + 1))).valid
        (env ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)]))
  sem env h := match h_x : (x.sem env h.1).val with
    | [] =>
      have h_em_valid := by simp [h_x] at h; exact h.right
      ⟨em.sem env h_em_valid,
        by
        obtain ⟨_, _, h_x'⟩ := (x.sem env h.1).property
        rw [h_x] at h_x'
        simp only [DataEncode.encode, List.map_nil] at h_x'
        obtain ⟨_, _, h_em⟩ := (em.sem env h_em_valid).property
        exact ⟨_, _, ProgSem.elim_nil h_x' h_em⟩⟩
    | hd :: tl =>
      have h_cs_valid := by simp [h_x] at h; exact h.right
      ⟨(cs (Routine.var env.length) (Routine.var (env.length + 1))).sem
        (env ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)]) h_cs_valid,
        by
        obtain ⟨_, _, h_x'⟩ := (x.sem env h.1).property
        rw [h_x] at h_x'
        simp only [DataEncode.encode, List.map_cons] at h_x'
        obtain ⟨_, _, h_cs⟩ := ((cs _ _).sem _ _).property
        exact ⟨_, _, ProgSem.elim_cons h_x' ProgSem.fn ⟨ProgSem.fn⟩ ⟨by
          rw [List.append_assoc]
          rw [show env.length + 2 = (env ++ [_, _]).length from by simp]
          exact h_cs⟩⟩⟩

def listCons (hd : Routine α) (tl : Routine (List α)) : Routine (List α) where
  impl n := .cons (hd.impl n) (tl.impl n)
  valid env := hd.valid env ∧ tl.valid env
  sem env h :=
    ⟨(hd.sem env h.left).val :: (tl.sem env h.right).val, by
      obtain ⟨_, _, h_hd⟩ := (hd.sem env h.left).property
      obtain ⟨_, _, h_tl⟩ := (tl.sem env h.right).property
      exact ⟨_, _, ProgSem.cons h_hd h_tl⟩⟩

def toPair (x : Routine α) (y : Routine β) : Routine (α × β) where
  impl n := .cons (x.impl n) (.cons (y.impl n) .empty)
  valid env := x.valid env ∧ y.valid env
  sem env h :=
    ⟨((x.sem env h.left).val, (y.sem env h.right).val), by
      obtain ⟨_, _, h_x⟩ := (x.sem env h.left).property
      obtain ⟨_, _, h_y⟩ := (y.sem env h.right).property
      exact ⟨_, _, ProgSem.cons h_x (ProgSem.cons h_y ProgSem.empty)⟩⟩

def fst (x : Routine (α × β)) : Routine α where
  impl := x.encode.head.impl
  valid := x.valid
  sem env h := ⟨(x.sem env h).val.fst, by
    have hv : x.encode.head.valid env := h
    have hc := (x.encode.head.sem env hv).property
    have heq : (x.encode.head.sem env hv).val
        = DataEncode.encode ((x.sem env h).val.fst) := by
      simp [Routine.head, Routine.encode, DataEncode.encode]
    rw [heq] at hc
    exact hc⟩

def snd (x : Routine (α × β)) : Routine β where
  impl := x.encode.tail.head.impl
  valid := x.valid
  sem env h := ⟨(x.sem env h).val.snd, by
    have hc := (x.encode.tail.head.sem env h).property
    have heq : (x.encode.tail.head.sem env h).val
        = DataEncode.encode ((x.sem env h).val.snd) := by
      simp [Routine.head, Routine.tail, Routine.encode, DataEncode.encode]
    rw [heq] at hc
    exact hc⟩

def isEq (x y : Routine α) [DecidableEq α] : Routine Bool where
  impl n := (ifEq x y (constant true) (constant false)).impl n
  valid env := x.valid env ∧ y.valid env
  sem env h := ⟨(x.sem env h.left).val == (y.sem env h.right).val, by sorry ⟩

def not (x : Routine Bool) : Routine Bool where
  impl n := (isEq x (constant false)).impl n
  valid env := x.valid env
  sem env h := ⟨!(x.sem env h).val, by sorry⟩

/-- The value computed by `fst x` is the first projection of `x`'s value. -/
lemma fst_sem_val (x : Routine (α × β)) (h : (fst x).valid env) :
    ((fst x).sem env h).val = (x.sem env h).val.fst := rfl

/-- The value computed by `snd x` is the second projection of `x`'s value. -/
lemma snd_sem_val (x : Routine (α × β)) (h : (snd x).valid env) :
    ((snd x).sem env h).val = (x.sem env h).val.snd := rfl

/-- The value computed by `toPair x y` is the pair of the values of `x` and `y`. -/
lemma toPair_sem_val (x : Routine α) (y : Routine β) (h : (toPair x y).valid env) :
    ((toPair x y).sem env h).val = ((x.sem env h.1).val, (y.sem env h.2).val) := rfl

/-- The value computed by a routine is independent of the (propositionally equal) routine term,
environment and validity proof. -/
lemma sem_val_congr {r r' : Routine α} {E E' : List Value} (hr : r = r') (hE : E = E')
    (h : r.valid E) (h' : r'.valid E') :
    (r.sem E h).val = (r'.sem E' h').val := by
  subst hr; subst hE; rfl

/-- When `x` evaluates to a nonempty list `hd :: tl`, `listElim` is valid via its cons branch. -/
lemma listElim_valid_cons
    (x : Routine (List α)) (em : Routine β) (cs : Routine α → Routine (List α) → Routine β)
    (hx : x.valid env) {hd : α} {tl : List α}
    (h_x : (x.sem env hx).val = hd :: tl)
    (h_cs : (cs (var env.length) (var (env.length + 1))).valid
        (env ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)])) :
    (listElim x em cs).valid env := by
  refine ⟨hx, ?_⟩
  rw [h_x]
  exact h_cs

/-- When `x` evaluates to a nonempty list `hd :: tl`, `listElim` takes the cons branch. -/
lemma listElim_sem_val_cons
    (x : Routine (List α)) (em : Routine β) (cs : Routine α → Routine (List α) → Routine β)
    (h : (listElim x em cs).valid env) {hd : α} {tl : List α}
    (h_x : (x.sem env h.1).val = hd :: tl)
    (h_cs : (cs (var env.length) (var (env.length + 1))).valid
        (env ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)])) :
    ((listElim x em cs).sem env h).val
      = ((cs (var env.length) (var (env.length + 1))).sem
          (env ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)]) h_cs).val := by
  show ((listElim x em cs).sem env h).val = _
  unfold listElim
  dsimp only
  split
  · rename_i h_x'
    rw [h_x] at h_x'
    exact absurd h_x' (List.cons_ne_nil hd tl)
  · rename_i hd' tl' h_x'
    have heq := h_x'.symm.trans h_x
    obtain ⟨e1, e2⟩ := List.cons.inj heq
    subst e1; subst e2
    rfl

open Classical in
/-- The value-level step function induced by `f`, evaluated at the two freshly-bound variables
on top of `env`. It captures `env`, so closures over the outer environment are preserved, while
the loop's internal bookkeeping slots are walled off. -/
noncomputable def foldlStep
    (f : Routine α → Routine β → Routine α) (env : List Value) (acc : α) (el : β) : α :=
  let r := f (var env.length) (var (env.length + 1))
  let e := env ++ [.data (DataEncode.encode acc), .data (DataEncode.encode el)]
  if h : r.valid e then (r.sem e h).val else acc

/-- The loop body of `foldl`: peel off the head of the remaining list and combine it with the
accumulator using `f`. The accumulator pair is `(remaining list, accumulator)`. -/
noncomputable def foldlBody (f : Routine α → Routine β → Routine α) :
    Routine (List β × α) → Routine (List β × α) :=
  fun st => listElim st.fst st fun head tail => toPair tail (f st.snd head)

/-- `foldl f init list`: left fold of `f` (taking `acc` then `el`) over `list`. -/
noncomputable def foldl_routine
    (f : Routine α → Routine β → Routine α)
    (init : Routine α)
    (list : Routine (List β)) :
    Routine α :=
  snd (while_ (toPair list init) (foldlBody f))

/-- The value-correctness hypothesis carried by `foldl`'s validity: `f`'s output value depends
only on the values of its arguments (it may capture `env`, but not the loop bookkeeping). It is
exactly `ComputesFun₂ f (foldlStep f env) env`. -/
def FoldlValidStep (f : Routine α → Routine β → Routine α) (env : List Value) : Prop :=
  ComputesFun₂ f (foldlStep f env) env

/-- One step of the `foldl` loop: applying the body to a nonempty remaining list `hd :: tl` peels
off `hd`, leaving remaining list `tl` and updated accumulator `foldlStep f env acc hd`. -/
lemma foldlBody_step (f : Routine α → Routine β → Routine α)
    (hd : β) (tl : List β) (acc : α) (Hf : FoldlValidStep f env) :
    ∃ h_valid : (foldlBody f (var env.length)).valid
        (env ++ [.data (DataEncode.encode (hd :: tl, acc))]),
      ((foldlBody f (var env.length)).sem
          (env ++ [.data (DataEncode.encode (hd :: tl, acc))]) h_valid).val
        = (tl, foldlStep f env acc hd) := by
  simp only [foldlBody]
  -- The environment in which the loop body runs.
  set env₁ := env ++ [.data (DataEncode.encode (hd :: tl, acc))] with henv₁
  have hlen : env₁.length = env.length + 1 := by simp [henv₁]
  have hEnv : env₁ ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)]
      = env ++ [.data (DataEncode.encode (hd :: tl, acc)), .data (DataEncode.encode hd),
          .data (DataEncode.encode tl)] := by rw [henv₁]; exact List.append_assoc env _ _
  -- Validity and value of the list scrutinee `(var env.length).fst`.
  have hx : ((var env.length).fst : Routine (List β)).valid env₁ :=
    ⟨(hd :: tl, acc), getElem?_append_singleton env _⟩
  have h_x : (((var env.length).fst).sem env₁ hx).val = hd :: tl := by
    rw [fst_sem_val, var_sem_val hx (getElem?_append_singleton env _)]
  -- Validity of the two arguments to `f`, in the three-slot environment.
  have ha : (var env.length : Routine (List β × α)).valid
      (env ++ [.data (DataEncode.encode (hd :: tl, acc)), .data (DataEncode.encode hd),
        .data (DataEncode.encode tl)]) :=
    var_valid_add (x := (hd :: tl, acc)) _ 0 rfl
  have hb : (var (env.length + 1) : Routine β).valid
      (env ++ [.data (DataEncode.encode (hd :: tl, acc)), .data (DataEncode.encode hd),
        .data (DataEncode.encode tl)]) :=
    var_valid_add (x := hd) _ 1 rfl
  obtain ⟨hf, heq⟩ := Hf _ ((var env.length).snd) (var (env.length + 1)) ha hb
  -- The two argument values are `acc` and `hd`.
  have hacc : (((var env.length).snd).sem _ ha).val = acc := by
    rw [snd_sem_val]
    exact congrArg Prod.snd (var_sem_val_add (x := (hd :: tl, acc)) _ 0 rfl ha)
  have hhd : ((var (env.length + 1) : Routine β).sem _ hb).val = hd :=
    var_sem_val_add (x := hd) _ 1 rfl hb
  rw [hacc, hhd] at heq
  -- Validity of the cons branch (a `toPair`) in `env₁`.
  have h_cs : (toPair (α := List β) (β := α) (var (env₁.length + 1))
      (f ((var env.length : Routine (List β × α)).snd) (var env₁.length))).valid
      (env₁ ++ [.data (DataEncode.encode hd), .data (DataEncode.encode tl)]) := by
    refine ⟨var_valid_add (env := env₁) (x := tl) _ 1 rfl, ?_⟩
    have hf' := hf
    rw [← hlen, ← hEnv] at hf'
    exact hf'
  refine ⟨listElim_valid_cons _ _ _ hx h_x h_cs, ?_⟩
  rw [listElim_sem_val_cons _ _ _ (listElim_valid_cons _ _ _ hx h_x h_cs) h_x h_cs]
  rw [toPair_sem_val, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact var_sem_val h_cs.1 (by rw [getElem?_append_length_add]; rfl)
  · rw [sem_val_congr (r' := f ((var env.length : Routine (List β × α)).snd) (var (env.length + 1)))
      (E' := env ++ [.data (DataEncode.encode (hd :: tl, acc)), .data (DataEncode.encode hd),
        .data (DataEncode.encode tl)]) (by rw [hlen]) hEnv h_cs.2 hf]
    exact heq

/-- The `foldl` loop telescopes to `List.foldl (foldlStep f env)` over the list. -/
lemma foldlBody_whileSem (f : Routine α → Routine β → Routine α)
    (Hf : FoldlValidStep f env) (l : List β) (acc : α) :
    WhileSem env (foldlBody f) (l, acc) ([], l.foldl (foldlStep f env) acc) := by
  induction l generalizing acc with
  | nil =>
    simpa using WhileSem.halt (env := env) (body := foldlBody f) [] acc DataEncode_list_nil
  | cons hd tl ih =>
    have h_ne : DataEncode.encode (hd :: tl) ≠ Data.l [] := by
      rw [show DataEncode.encode (hd :: tl)
          = Data.l ((hd :: tl).map DataEncode.encode) from rfl]
      simp
    obtain ⟨h_valid, h_step⟩ := foldlBody_step f hd tl acc Hf
    refine WhileSem.step h_ne h_valid ?_
    rw [h_step, List.foldl_cons]
    exact ih (foldlStep f env acc hd)

noncomputable def foldl
    (f : Routine α → Routine β → Routine α)
    (init : Routine α)
    (list : Routine (List β)) :
    Routine α where
  impl := (foldl_routine f init list).impl
  valid env := init.valid env ∧ list.valid env ∧
        ∀ (extra : List Value) (a : Routine α) (b : Routine β)
          (ha : a.valid (env ++ extra)) (hb : b.valid (env ++ extra)),
          ∃ (hf : (f a b).valid (env ++ extra)),
            ((f a b).sem (env ++ extra) hf).val
              = foldlStep f env ((a.sem (env ++ extra) ha).val) ((b.sem (env ++ extra) hb).val)
  sem env h :=
    have hpair : (toPair list init).valid env := ⟨h.2.1, h.1⟩
    have hws : WhileSem env (foldlBody f) ((toPair list init).sem env hpair).val
        ([], (list.sem env h.2.1).val.foldl (foldlStep f env) (init.sem env h.1).val) := by
      rw [toPair_sem_val]
      exact foldlBody_whileSem f h.2.2 _ _
    have Hwhile : (while_ (toPair list init) (foldlBody f)).valid env := ⟨hpair, _, hws⟩
    have hval : ((while_ (toPair list init) (foldlBody f)).sem env Hwhile).val
        = ([], (list.sem env h.2.1).val.foldl (foldlStep f env) (init.sem env h.1).val) :=
      while_sem_val _ _ Hwhile hpair hws
    ⟨(list.sem env h.2.1).val.foldl (foldlStep f env) (init.sem env h.1).val, by
      have hsnd : ((foldl_routine f init list).sem env Hwhile).val
          = (list.sem env h.2.1).val.foldl (foldlStep f env) (init.sem env h.1).val := by
        change ((while_ (toPair list init) (foldlBody f)).sem env Hwhile).val.snd = _
        rw [hval]
      have hp := ((foldl_routine f init list).sem env Hwhile).property
      rw [hsnd] at hp
      exact hp⟩


/-- The value-level step of `reverse` prepends the current element to the accumulator. -/
lemma reverse_foldlStep (acc : List α) (el : α) :
    foldlStep (fun (a : Routine (List α)) (e : Routine α) => listCons e a) env acc el
      = el :: acc := by
  have hvalid : (listCons (var (env.length + 1)) (var env.length : Routine (List α))).valid
      (env ++ [.data (DataEncode.encode acc), .data (DataEncode.encode el)]) :=
    ⟨⟨el, by simp⟩, ⟨acc, by simp⟩⟩
  simp only [foldlStep, dif_pos hvalid]
  simp [listCons]

/-- Folding the `reverse` step over a list reverses it. -/
lemma reverse_foldl (l : List α) :
    l.foldl (foldlStep (fun a e => listCons e a) env) [] = l.reverse := by
  have hstep : foldlStep (fun a (e : Routine α) => listCons e a) env
      = fun acc el => el :: acc := by
    funext acc el
    exact reverse_foldlStep acc el
  rw [hstep]
  simp

/-- Models `List.reverse`. -/
noncomputable def reverse (x : Routine (List α)) : Routine (List α) where
  impl := (foldl (fun acc el => listCons el acc) (constant ([] : List α)) x).impl
  valid := x.valid
  sem env h := ⟨(x.sem env h).val.reverse, by
    let F := foldl (fun acc el => listCons el acc) (constant ([] : List α)) x
    have hF : F.valid env :=
      ⟨trivial, h, fun _ a b ha hb => ⟨⟨hb, ha⟩, by rw [reverse_foldlStep]; rfl⟩⟩
    have hc := (F.sem env hF).property
    have heq : (F.sem env hF).val = (x.sem env h).val.reverse := by
      change (x.sem env hF.2.1).val.foldl
        (foldlStep (fun (a : Routine (List α)) (e : Routine α) => listCons e a) env) [] = _
      rw [reverse_foldl]
    rw [heq] at hc
    exact hc⟩

/-- `reverse x` is valid exactly when `x` is. -/
lemma reverse_valid (x : Routine (List α)) (hx : x.valid env) : (reverse x).valid env := hx

/-- `reverse x` computes the reverse of `x`. -/
lemma reverse_sem (x : Routine (List α)) (h₁ : (reverse x).valid env) (h₂ : x.valid env) :
    ((reverse x).sem env h₁).val = (x.sem env h₂).val.reverse := rfl

/-- The value-level step of `listMap`: applying `f` to the current element and prepending it. -/
lemma listMap_foldlStep (f : Routine α → Routine β) (g : α → β)
    (hf : ComputesFun f g env) (acc : List β) (el : α) :
    foldlStep (fun (a : Routine (List β)) (e : Routine α) => listCons (f e) a) env acc el
      = g el :: acc := by
  obtain ⟨hfv, hfval⟩ :=
    hf [.data (DataEncode.encode acc), .data (DataEncode.encode el)] (var (env.length + 1))
      ⟨el, by simp⟩
  have hvalid : (listCons (f (var (env.length + 1))) (var env.length : Routine (List β))).valid
      (env ++ [.data (DataEncode.encode acc), .data (DataEncode.encode el)]) :=
    ⟨hfv, ⟨acc, by simp⟩⟩
  simp only [foldlStep, dif_pos hvalid]
  simp only [listCons]
  congr 1
  · rw [sem_val_congr rfl rfl hvalid.left hfv, hfval, var_sem_val_length_succ]
  · exact var_sem_val_length₂ hvalid.right

/-- Folding the `listMap` step over a list gives the reverse of the mapped list. -/
lemma listMap_foldl (f : Routine α → Routine β) (g : α → β) (hf : ComputesFun f g env)
    (l : List α) :
    l.foldl (foldlStep (fun (a : Routine (List β)) (e : Routine α) => listCons (f e) a) env) []
      = (l.map g).reverse := by
  have hstep : foldlStep (fun (a : Routine (List β)) (e : Routine α) => listCons (f e) a) env
      = fun acc el => g el :: acc := by
    funext acc el
    exact listMap_foldlStep f g hf acc el
  rw [hstep]
  have key : ∀ init, l.foldl (fun acc el => g el :: acc) init = (l.map g).reverse ++ init := by
    intro init
    induction l generalizing init with
    | nil => simp
    | cons hd tl ih => simp [ih]
  rw [key, List.append_nil]

/-- Models `List.map`. -/
noncomputable def listMap (f : Routine α → Routine β) (g : α → β) (x : Routine (List α)) :
    Routine (List β) where
  impl := (reverse (foldl (fun acc el => listCons (f el) acc) (constant ([] : List β)) x)).impl
  valid env := x.valid env ∧ ComputesFun f g env
  sem env h := ⟨(x.sem env h.1).val.map g, by
    let S := foldl (fun acc el => listCons (f el) acc) (constant ([] : List β)) x
    have hS : S.valid env :=
      ⟨trivial, h.1, fun extra a b ha hb =>
        let ⟨hfb, hfbval⟩ := h.2 extra b hb
        ⟨⟨hfb, ha⟩, by rw [listMap_foldlStep f g h.2]; simp only [listCons]; rw [hfbval]⟩⟩
    have hc := ((reverse S).sem env hS).property
    have heq : ((reverse S).sem env hS).val = (x.sem env h.1).val.map g := by
      change ((x.sem env h.1).val.foldl
        (foldlStep (fun (a : Routine (List β)) (e : Routine α) => listCons (f e) a)
          env) []).reverse = _
      rw [listMap_foldl f g h.2, List.reverse_reverse]
    rw [heq] at hc
    exact hc⟩

/-- `listMap f g x` is valid when `x` is and `f` computes `g`. -/
lemma listMap_valid (f : Routine α → Routine β) (g : α → β) (x : Routine (List α))
    (hx : x.valid env) (hf : ComputesFun f g env) : (listMap f g x).valid env := ⟨hx, hf⟩

/-- `listMap f g x` computes `(x.sem).map g`. -/
lemma listMap_sem (f : Routine α → Routine β) (g : α → β) (x : Routine (List α))
    (h : (listMap f g x).valid env) :
    ((listMap f g x).sem env h).val = (x.sem env h.1).val.map g := rfl

/-- The `g`-free counterpart of `listMap`: simply `reverse ∘ foldl`, mirroring how `foldl` extracts
its value-step from `f` rather than taking an explicit spec. It needs no spec parameter and no new
proofs — its validity and semantics are inherited from `foldl`/`reverse`. The computed value is
expressed through `foldlStep`; `listMapAuto_sem` characterises it as `l.map g` whenever `f`
computes `g`. -/
noncomputable def listMapAuto (f : Routine α → Routine β) (x : Routine (List α)) :
    Routine (List β) :=
  reverse (foldl (fun acc el => listCons (f el) acc) (constant ([] : List β)) x)

/-- `listMapAuto f x` is valid when `x` is and `f` computes some `g`. -/
lemma listMapAuto_valid (f : Routine α → Routine β) (g : α → β) (x : Routine (List α))
    (hx : x.valid env) (hf : ComputesFun f g env) : (listMapAuto f x).valid env :=
  ⟨trivial, hx, fun extra a b ha hb =>
    let ⟨hfb, hfbval⟩ := hf extra b hb
    ⟨⟨hfb, ha⟩, by rw [listMap_foldlStep f g hf]; simp only [listCons]; rw [hfbval]⟩⟩

/-- When `f` computes `g`, `listMapAuto f x` computes `(x.sem).map g`. -/
lemma listMapAuto_sem (f : Routine α → Routine β) (g : α → β) (x : Routine (List α))
    (hf : ComputesFun f g env) (h : (listMapAuto f x).valid env) (hx : x.valid env) :
    ((listMapAuto f x).sem env h).val = (x.sem env hx).val.map g := by
  change ((x.sem env hx).val.foldl
    (foldlStep (fun (a : Routine (List β)) (e : Routine α) => listCons (f e) a)
      env) []).reverse = _
  rw [listMap_foldl f g hf, List.reverse_reverse]


/-- Extracts the payload of an `Option α` routine (junk when the value is `none`). Implemented by
decoding the head of the underlying one-element list. -/
def optionPayload (e : Routine (Option α)) : Routine α :=
  decode (head (encode e))

/-- When `e` evaluates to `some y`, `optionPayload e` is valid. -/
lemma optionPayload_valid_some (e : Routine (Option α)) (he : e.valid env) {y : α}
    (h_e : (e.sem env he).val = some y) : (optionPayload e).valid env := by
  refine ⟨he, y, ?_⟩
  change (DataEncode.encode (e.sem env he).val).asList.headD Data.empty = DataEncode.encode y
  rw [h_e]
  simp [DataEncode.encode, Data.asList]

/-- When `e` evaluates to `some y`, `optionPayload e` computes `y`. -/
lemma optionPayload_sem_val_some (e : Routine (Option α)) (h : (optionPayload e).valid env)
    {y : α} (h_e : (e.sem env h.1).val = some y) :
    ((optionPayload e).sem env h).val = y := by
  have hhead : ((head (encode e)).sem env h.1).val = DataEncode.encode y := by
    change (DataEncode.encode (e.sem env h.1).val).asList.headD Data.empty = DataEncode.encode y
    rw [h_e]
    simp [DataEncode.encode, Data.asList]
  have hdec : DataEncode.decode (α := α) ((head (encode e)).sem env h.1).val = some y := by
    rw [hhead, DataEncode.encodek]
  exact Option.get_of_mem _ hdec

/-- A non-deepening eliminator on `Option α`: run `ifNone` when the value is `none`, or `ifSome`
when it is `some`. Built with `Prog.ifEq` (testing the encoding against the empty list), so both
branches run in the *same* environment — unlike `listElim`, no extra slots are bound. -/
def optionCond (e : Routine (Option α)) (ifNone ifSome : Routine β) : Routine β where
  impl n := .ifEq (e.impl n) Prog.empty (ifNone.impl n) (ifSome.impl n)
  valid env := ∃ h : e.valid env, (match (e.sem env h).val with
    | none => ifNone.valid env
    | some _ => ifSome.valid env)
  sem env h := match h_e : (e.sem env h.1).val with
    | none =>
      have hn : ifNone.valid env := by have h2 := h.2; rw [h_e] at h2; exact h2
      ⟨(ifNone.sem env hn).val, by
        obtain ⟨_, _, h_pe⟩ := (e.sem env h.1).property
        rw [h_e] at h_pe
        obtain ⟨_, _, h_pn⟩ := (ifNone.sem env hn).property
        exact ⟨_, _, ProgSem.ifEq_then h_pe ProgSem.empty h_pn⟩⟩
    | some y =>
      have hs : ifSome.valid env := by have h2 := h.2; rw [h_e] at h2; exact h2
      ⟨(ifSome.sem env hs).val, by
        obtain ⟨_, _, h_pe⟩ := (e.sem env h.1).property
        rw [h_e] at h_pe
        obtain ⟨_, _, h_ps⟩ := (ifSome.sem env hs).property
        refine ⟨_, _, ProgSem.ifEq_else h_pe ProgSem.empty ?_ h_ps⟩
        simp [DataEncode.encode]⟩

/-- When `e` evaluates to `none`, `optionCond` is valid via its `none` branch. -/
lemma optionCond_valid_none (e : Routine (Option α)) (ifNone ifSome : Routine β)
    (he : e.valid env) (h_e : (e.sem env he).val = none) (hn : ifNone.valid env) :
    (optionCond e ifNone ifSome).valid env := ⟨he, by rw [h_e]; exact hn⟩

/-- When `e` evaluates to `none`, `optionCond` takes its `none` branch. -/
lemma optionCond_sem_val_none (e : Routine (Option α)) (ifNone ifSome : Routine β)
    (h : (optionCond e ifNone ifSome).valid env) (h_e : (e.sem env h.1).val = none)
    (hn : ifNone.valid env) :
    ((optionCond e ifNone ifSome).sem env h).val = (ifNone.sem env hn).val := by
  unfold optionCond
  dsimp only
  split
  · rfl
  · rename_i y h_e'
    rw [h_e] at h_e'
    exact absurd h_e' (by simp)

/-- When `e` evaluates to `some y`, `optionCond` is valid via its `some` branch. -/
lemma optionCond_valid_some (e : Routine (Option α)) (ifNone ifSome : Routine β)
    (he : e.valid env) {y : α} (h_e : (e.sem env he).val = some y) (hs : ifSome.valid env) :
    (optionCond e ifNone ifSome).valid env := ⟨he, by rw [h_e]; exact hs⟩

/-- When `e` evaluates to `some y`, `optionCond` takes its `some` branch. -/
lemma optionCond_sem_val_some (e : Routine (Option α)) (ifNone ifSome : Routine β)
    (h : (optionCond e ifNone ifSome).valid env) {y : α} (h_e : (e.sem env h.1).val = some y)
    (hs : ifSome.valid env) :
    ((optionCond e ifNone ifSome).sem env h).val = (ifSome.sem env hs).val := by
  unfold optionCond
  dsimp only
  split
  · rename_i h_e'
    rw [h_e] at h_e'
    exact absurd h_e' (by simp)
  · rfl

/-- The value-correctness of one `listReduceOption` fold step, for arbitrary accumulator and
element routines. Because the step is *flat* (`optionCond` does not bind extra slots), it holds for
any valid `acc`/`el`, with no environment weakening required. -/
lemma reduceOptionStep_spec (acc : Routine (List α)) (el : Routine (Option α))
    (ha : acc.valid env) (hb : el.valid env) :
    ∃ h : (optionCond el acc (listCons (optionPayload el) acc)).valid env,
      ((optionCond el acc (listCons (optionPayload el) acc)).sem env h).val
        = (match (el.sem env hb).val with
            | none => (acc.sem env ha).val | some y => y :: (acc.sem env ha).val) := by
  cases h_e : (el.sem env hb).val with
  | none =>
    have hv : (optionCond el acc (listCons (optionPayload el) acc)).valid env :=
      optionCond_valid_none el acc _ hb h_e ha
    exact ⟨hv, by rw [optionCond_sem_val_none el acc _ hv h_e ha]⟩
  | some y =>
    have hpv : (optionPayload el).valid env := optionPayload_valid_some el hb h_e
    have hcons : (listCons (optionPayload el) acc).valid env := ⟨hpv, ha⟩
    have hv : (optionCond el acc (listCons (optionPayload el) acc)).valid env :=
      optionCond_valid_some el acc _ hb h_e hcons
    refine ⟨hv, ?_⟩
    rw [optionCond_sem_val_some el acc _ hv h_e hcons]
    simp only [listCons]
    rw [optionPayload_sem_val_some el hpv h_e]


/-- The value-level step of `listReduceOption`: keep `some` payloads, drop `none`. -/
lemma listReduceOption_foldlStep (acc : List α) (el : Option α) :
    foldlStep (fun (a : Routine (List α)) (e : Routine (Option α)) =>
        optionCond e a (listCons (optionPayload e) a)) env acc el
      = (match el with | none => acc | some y => y :: acc) := by
  have ha : (var env.length : Routine (List α)).valid
      (env ++ [.data (DataEncode.encode acc), .data (DataEncode.encode el)]) := ⟨acc, by simp⟩
  have hb : (var (env.length + 1) : Routine (Option α)).valid
      (env ++ [.data (DataEncode.encode acc), .data (DataEncode.encode el)]) := ⟨el, by simp⟩
  obtain ⟨hr, hrv⟩ := reduceOptionStep_spec (var env.length) (var (env.length + 1)) ha hb
  simp only [foldlStep, dif_pos hr]
  rw [hrv]
  simp only [var_sem_val_length₂, var_sem_val_length_succ]

/-- Folding the `listReduceOption` step over a list yields the reverse of `List.reduceOption`. -/
lemma listReduceOption_foldl (l : List (Option α)) :
    l.foldl (foldlStep (fun a e => optionCond e a (listCons (optionPayload e) a)) env) []
      = l.reduceOption.reverse := by
  have hstep : foldlStep (fun (a : Routine (List α)) (e : Routine (Option α)) =>
      optionCond e a (listCons (optionPayload e) a)) env
      = fun acc el => (match el with | none => acc | some y => y :: acc) := by
    funext acc el
    exact listReduceOption_foldlStep acc el
  rw [hstep]
  have key : ∀ init : List α,
      l.foldl (fun acc el => (match el with | none => acc | some y => y :: acc)) init
        = l.reduceOption.reverse ++ init := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro init
      cases hd with
      | none => simp [ih, List.reduceOption_cons_of_none]
      | some y => simp [ih, List.reduceOption_cons_of_some]
  rw [key, List.append_nil]

/-- Models `List.reduceOption`, i.e. discards `none` elements, keeping the `some` payloads. -/
noncomputable def listReduceOption (x : Routine (List (Option α))) : Routine (List α) where
  impl := (reverse (foldl (fun acc el => optionCond el acc (listCons (optionPayload el) acc))
    (constant ([] : List α)) x)).impl
  valid := x.valid
  sem env h := ⟨(x.sem env h).val.reduceOption, by
    let F := foldl (fun acc el => optionCond el acc (listCons (optionPayload el) acc))
      (constant ([] : List α)) x
    have hF : F.valid env :=
      ⟨trivial, h, fun _ a b ha hb =>
        let ⟨hf, hfv⟩ := reduceOptionStep_spec (env := env ++ _) a b ha hb
        ⟨hf, by rw [hfv, listReduceOption_foldlStep]⟩⟩
    have hc := ((reverse F).sem env hF).property
    have heq : ((reverse F).sem env hF).val = (x.sem env h).val.reduceOption := by
      change ((x.sem env hF.2.1).val.foldl
        (foldlStep (fun (a : Routine (List α)) (e : Routine (Option α)) =>
          optionCond e a (listCons (optionPayload e) a)) env) []).reverse = _
      rw [listReduceOption_foldl, List.reverse_reverse]
    rw [heq] at hc
    exact hc⟩

/-- `listReduceOption x` is valid exactly when `x` is. -/
lemma listReduceOption_valid (x : Routine (List (Option α))) (hx : x.valid env) :
    (listReduceOption x).valid env := hx

/-- `listReduceOption x` computes `List.reduceOption` of `x`. -/
lemma listReduceOption_sem (x : Routine (List (Option α))) (h : (listReduceOption x).valid env)
    (hx : x.valid env) :
    ((listReduceOption x).sem env h).val = (x.sem env hx).val.reduceOption := rfl


-- /-- Models `List.reduceOption`, i.e. discards `none` elements, keeping the `some` payloads. -/
-- def listReduceOption (x : PB) : PB :=
--   reverse (foldl
--     (fun acc el => optionElim el acc (fun y => PB.cons y acc))
--     empty x)

-- lemma listReduceOption_computes {p : PB} {l : List (Option α)} (h : p.ComputesEnc env l) :
--     (listReduceOption p).ComputesEnc env l.reduceOption := by
--   have h_reduceOption_via_fold (m : List (Option α)) : ∀ (a : List α),
--       (m.foldl (fun acc el => match el with | .none => acc | .some y => y :: acc) a).reverse
--         = a.reverse ++ m.reduceOption := by
--     induction m with
--     | nil => simp
--     | cons hd tl ih =>
--       cases hd with | none | some _ => simp [ih]
--   rw [show l.reduceOption = (l.foldl _ []).reverse
--       from by simpa using (h_reduceOption_via_fold l []).symm]
--   apply reverse_computes ((foldl_computes (empty_computesEnc α) h) ?_)
--   intro e p_acc p_el acc el h_acc h_el
--   cases el with
--   | none => exact optionElim_computesEnc_none h_el h_acc
--   | some y =>
--     apply optionElim_computesEnc_some h_el (computesFun₂_branch (fun ext => ?_))
--     exact cons_computesEnc (var_computes_fresh ext _) ((h_acc.extend ext).extend _)

-- /-- Models `List.head?` -/
-- def listHeadOption (input : PB) : PB :=
--   PB.elim input empty (fun hd _tl => some hd)

-- lemma listHeadOption_computes {p : PB} {l : List α} (h : p.ComputesEnc env l) :
--     (listHeadOption p).ComputesEnc env l.head? := by
--   cases l with
--   | nil =>
--     apply PB.elim_nil_computes h (empty_computes)
--   | cons hd tl =>
--     apply PB.elim_cons_computes h (PB.computesFun₂_branch2 (fun ext => ?_))
--     refine PB.cons_computes (var_computes_fresh ext _) empty_computes


-- -- Evaluate a function `f` at `arg` where the function is given as a graph (list of pairs).
-- -- Returns `some y` for the first `x` in the graph such that `f x = y` and `none` otherwise.
-- def evalFunGraph (graph : PB) (arg : PB) : PB :=
--   snd (PB.while_
--     (toPair graph .empty)
--     (fun acc => .elim acc.fst
--       .empty -- cannot happen
--       fun pair rest =>
--         ifEq pair.fst arg
--           (toPair .empty (PB.some pair.snd))
--           (toPair rest .empty)))

-- private def evalFunGraphInner : PB → PB → PB :=
--   fun arg acc => .elim acc.fst
--     .empty -- cannot happen
--     fun pair rest =>
--       ifEq pair.fst arg
--         (toPair .empty (PB.some pair.snd))
--         (toPair rest .empty)

-- private lemma evalFunGraphInner_computesFun₁ [DecidableEq α]
--   (arg : α)
--   {p_arg : PB}
--   (h_arg : p_arg.ComputesEnc env arg)
--   {graph : List (α × β)}
--   {x : α}
--   {y : β} :
--   computesFun₁ env
--     (.data (DataEncode.encode (((x, y) :: graph), (.none : Option β))))
--     (evalFunGraphInner p_arg)
--     (.data (DataEncode.encode (if x == arg then
--       ([], Option.some y)
--     else
--       (graph, Option.none)))) := by
--   apply PB.computesFun₁_branch
--   intro ext
--   unfold evalFunGraphInner
--   refine PB.elim_cons_computes (PB.fst_ComputesEnc (PB.var_computes_fresh ext [])) ?_
--   apply PB.computesFun₂_branch2
--   intro ext2
--   -- Names for the extended environment and its fresh bindings.
--   set acc := Value.data (DataEncode.encode (((x, y) :: graph), (.none : Option β)))
--   set pv := Value.data (DataEncode.encode (x, y)) with hpv
--   set rv := Value.data (Data.l (graph.map DataEncode.encode)) with hrv
--   -- `arg` (= `p_arg`) is still available after the environment grows.
--   have h_arg' := ((h_arg.extend ext).extend [acc]).extend ext2 |>.extend [pv, rv]
--   by_cases h : x = arg
--   · subst h
--     simp only [beq_self_eq_true, if_true]
--     exact ifeq_eq_computes
--       (fst_ComputesEnc (var_computes_fresh ext2 [rv]))
--       h_arg'
--       (toPair_computesEnc
--         (empty_computes) (some_ComputesEnc (snd_ComputesEnc (var_computes_fresh ext2 [rv]))))
--   · refine PB.ifeq_ne_computes (PB.fst_ComputesEnc (var_computes_fresh ext2 [rv])) h_arg'
--       (fun he => h (DataEncode.h_inj he)) ?_
--     rw [if_neg (by simpa using h)]
--     exact PB.toPair_computesEnc
--       (var_computes_fresh' ext2 [pv, rv] (j := 1) (by simp)) (empty_computes)


-- /-- Semantic spec of `eval_fun_graph`: given an encoded graph (list of
-- `(α × β)`-pairs) and an encoded argument `a : α`, returns
-- `(graph.find? (·.1 = a)).map (·.2)`, i.e. `some y` for the first pair `(a, y)`
-- in the graph, else `none`. -/
-- lemma evalFunGraph_computes
--     [DecidableEq α]
--     {p_graph p_arg : PB}
--     {graph : List (α × β)}
--     {a : α}
--     (h_graph : p_graph.ComputesEnc env graph)
--     (h_arg : p_arg.ComputesEnc env a) :
--     (evalFunGraph p_graph p_arg).ComputesEnc env
--       ((graph.find? (fun p => p.1 = a)).map (·.2)) := by
--   -- The loop iterates the body from `(g, none)` to `([], find-result)` for any remaining list `g`.
--   have h_loop : ∀ g : List (α × β),
--       WhileComputes env (evalFunGraphInner p_arg)
--         (DataEncode.encode (g, (none : Option β)))
--         (DataEncode.encode (([] : List (α × β)),
--           (g.find? (fun p => p.1 = a)).map (·.2))) := by
--     intro g
--     induction g with
--     | nil =>
--       -- Empty remaining list: the loop halts immediately on the empty head.
--       apply WhileComputes.halt
--       simp [DataEncode.encode]
--     | cons hd tl ih =>
--       obtain ⟨x, y⟩ := hd
--       by_cases h : x = a
--       · -- Match on the first element: body sets the result to `some y`, then the loop halts.
--         subst h
--         have hfind : (((x, y) :: tl).find? (fun p => p.1 = x)).map (·.2) = Option.some y := by
--           simp
--         rw [hfind]
--         have hb := evalFunGraphInner_computesFun₁ (env := env) x h_arg
--           (graph := tl) (x := x) (y := y)
--         simp only [beq_self_eq_true, if_true] at hb
--         refine WhileComputes.step ?_ hb ?_
--         · simp [DataEncode.encode]
--         · apply WhileComputes.halt
--           simp [DataEncode.encode]
--       · -- No match on the first element: body drops it, keeps `none`, and recurses.
--         have hfind : (((x, y) :: tl).find? (fun p => p.1 = a)).map (·.2)
--             = (tl.find? (fun p => p.1 = a)).map (·.2) := by
--           simp [h]
--         rw [hfind]
--         have hb := evalFunGraphInner_computesFun₁ (env := env) a h_arg
--           (graph := tl) (x := x) (y := y)
--         rw [if_neg (show ¬ ((x == a) = true) by simpa using h)] at hb
--         exact WhileComputes.step (by simp [DataEncode.encode]) hb ih
--   -- Initial accumulator: `(graph, none)`.
--   have h_init : (toPair p_graph .empty).ComputesEnc env (graph, (none : Option β)) :=
--     toPair_computesEnc h_graph (empty_computes)
--   exact snd_ComputesEnc (while_computes h_init (h_loop graph))


-- lemma evalFunGraph_Computes_of_fun
--     [Fintype α]
--     {p_graph p_arg : PB}
--     {a : α}
--     {f : α → β}
--     (h_graph : p_graph.ComputesEnc env (Fintype.elems.toList.map (fun a => (a, f a))))
--     (h_arg : p_arg.ComputesEnc env a) :
--     (PB.evalFunGraph p_graph p_arg).head.ComputesEnc env (f a) := by
--   classical
--   have heq : ∀ (L : List α), a ∈ L →
--       ((L.map (fun a' => (a', f a'))).find?
--         (fun p => p.1 = a)).map (·.2) = Option.some (f a) := by
--     intro L hmem
--     induction L with
--     | nil => exact absurd hmem (by simp)
--     | cons hd tl ih => grind
--   have h := PB.evalFunGraph_computes h_graph h_arg
--   rw [heq _ (Finset.mem_toList.mpr (Fintype.complete a))] at h
--   apply PB.head_computes h


-- -- def bitEq (x y : PB) : PB :=
-- --   ifEq x y (constantEnc true) (constantEnc false)

-- -- lemma bitEq_computes {p_x p_y : PB} {a b : Bool}
-- --     (h_x : p_x.ComputesEnc env a) (h_y : p_y.ComputesEnc env b) :
-- --     (bitEq p_x p_y).ComputesEnc env (a == b) := by
-- --   by_cases h : a = b
-- --   · subst h
-- --     apply PB.ifeq_eq_computesEnc h_x h_y
-- --     simp
-- --   · apply PB.ifeq_ne_computesEnc h_x h_y h
-- --     simp [beq_false_of_ne h]


-- structure Builder (α : Type) [DataEncode α] where
--   impl : PB
--   valid : List Value → Prop := fun _ => True
--   sem : (env : List Value) → (h: valid env) → α
--   h : ∀ env (h : valid env), impl.ComputesEnc env (sem env h)

-- /-- A *binary* program-builder combinator: a code transformer `impl`, its semantic action `sem`,
-- and a proof `h` that whenever the two argument programs compute `a` and `b` (in any environment),
-- the transformed program computes `sem a b`. This is the binary analogue of `Builder` for operations
-- that genuinely take two runtime inputs (e.g. a fold body), where the code must *not* be allowed to
-- depend on the semantic values. -/
-- structure Fun2 (α β γ : Type) [DataEncode α] [DataEncode β] [DataEncode γ] where
--   impl : PB → PB → PB
--   sem : α → β → γ
--   h : ∀ {env : List Value} {pa pb : PB} {a : α} {b : β},
--     pa.ComputesEnc env a → pb.ComputesEnc env b → (impl pa pb).ComputesEnc env (sem a b)

-- /-- Translation **to** `Builder → Builder → Builder`: apply a binary combinator to two builders.
-- The result is valid exactly when both inputs are, its semantics is `sem` of the inputs' semantics,
-- and its correctness proof is assembled from the combinator's `h`. -/
-- def Fun2.apply (f : Fun2 α β γ) (x : Builder α) (y : Builder β) : Builder γ where
--   impl := f.impl x.impl y.impl
--   valid env := x.valid env ∧ y.valid env
--   sem env h := f.sem (x.sem env h.left) (y.sem env h.right)
--   h env h := f.h (x.h env h.left) (y.h env h.right)

-- /-- A binary combinator can be used directly as a function on builders. -/
-- instance : CoeFun (Fun2 α β γ) (fun _ => Builder α → Builder β → Builder γ) := ⟨Fun2.apply⟩

-- /-- Left fold as a builder combinator: the body is a binary combinator `Fun2 α β α` (its code may
-- not depend on the runtime accumulator/element), folded over the list computed by `list` starting
-- from `init`. The result is valid when both `init` and `list` are, and its semantics is the ordinary
-- `List.foldl` of the body's semantics. -/
-- def foldlB (body : Fun2 α β α) (init : Builder α) (list : Builder (List β)) : Builder α where
--   impl := foldl body.impl init.impl list.impl
--   valid env := init.valid env ∧ list.valid env
--   sem env h := (list.sem env h.right).foldl body.sem (init.sem env h.left)
--   h env h := foldl_computes (init.h env h.left) (list.h env h.right) body.h

-- /-- Boolean equality as a bundled binary combinator (the primitive); the `Builder`-level `bitEq`
-- below is derived from it. -/
-- def bitEqF : Fun2 Bool Bool Bool where
--   impl x y := ifEq x y (constantEnc true) (constantEnc false)
--   sem a b := a == b
--   h := by
--     intro env pa pb a b h_x h_y
--     by_cases hab : a = b
--     · subst hab
--       apply PB.ifeq_eq_computesEnc h_x h_y
--       simp
--     · apply PB.ifeq_ne_computesEnc h_x h_y hab
--       simp [beq_false_of_ne hab]

-- /-- Boolean equality on builders, obtained from `bitEqF` via the `Fun2 → Builder → Builder → Builder`
-- translation. -/
-- def bitEq : Builder Bool → Builder Bool → Builder Bool := bitEqF.apply

-- def constantEncBuilder {α : Type} [DataEncode α] (a : α) : Builder α where
--   impl := constantEnc a
--   valid := fun _ => True
--   sem _ _ := a
--   h _ _ := constantEnc_computesEnc

-- def boolNot (p : Builder Bool) : Builder Bool where
--   impl := ifEq p.impl (constantEnc true) (constantEnc false) (constantEnc true)
--   valid := p.valid
--   sem env valid := Bool.not (p.sem env valid)
--   h env valid := by
--     cases h : (p.sem env valid)
--     · exact PB.ifeq_ne_computesEnc (p.h env valid) constantEnc_computesEnc (by simp [h])
--         constantEnc_computesEnc
--     · exact PB.ifeq_eq_computesEnc (p.h env valid)
--         (by simp [h, constantEnc_computesEnc]) constantEnc_computesEnc

-- def boolNot₂ (p : Builder Bool) : Builder Bool :=
--   let beq := bitEq p (constantEncBuilder false)
--   {
--     impl := beq.impl
--     valid := p.valid
--     sem env valid := Bool.not (p.sem env valid)
--     h env valid := by sorry
--       -- have h_v_eq : ∀ env, p.valid env = beq.valid env := by
--       --   simp [beq, bitEq, bitEqF, Fun2.apply, constantEncBuilder]
--       -- let r := beq.h env (h_v_eq env ▸ valid)
--       -- have h₂ : ∀ v₁ v₂, beq.sem env v₁ =
--       -- exact r
--       -- have h_beq := beq.h env valid (p.h env valid) (constantEncBuilder false).h env valid
--       -- sorry
--   }

-- example : ∀ (p : Builder Bool) env h₁ h₂ x (h2 : x = p.sem env h₁),
--     (boolNot₂ p).sem env h₂ = !x := by
--   unfold boolNot₂
--   simp
--   sorry

-- /-- Boolean exclusive-or as a bundled binary combinator. -/
-- def boolXorF : Fun2 Bool Bool Bool where
--   impl x y := ifEq x y (constantEnc false) (constantEnc true)
--   sem a b := Bool.xor a b
--   h := by
--     intro env pa pb a b h_x h_y
--     cases a <;> cases b <;>
--       first
--         | (apply PB.ifeq_eq_computesEnc h_x h_y; simp)
--         | (apply PB.ifeq_ne_computesEnc h_x h_y (by decide); simp)

-- def boolXor (x y : PB) : PB := boolXorF.impl x y

-- lemma boolXor.computes {p_x p_y : PB} {a b : Bool}
--     (h_x : p_x.ComputesEnc env a) (h_y : p_y.ComputesEnc env b) :
--     (boolXor p_x p_y).ComputesEnc env (Bool.xor a b) :=
--   boolXorF.h h_x h_y

-- def ifBool (cond then_ else_ : PB) : PB :=
--   ifEq cond (constantEnc true) then_ else_

-- lemma ifBool_computes {p_cond p_then p_else : PB} {cond : Bool} {then_ else_ : α}
--     (h_cond : p_cond.ComputesEnc env cond)
--     (h_then : p_then.ComputesEnc env then_)
--     (h_else : p_else.ComputesEnc env else_) :
--     (ifBool p_cond p_then p_else).ComputesEnc env (if cond then then_ else else_) := by
--   cases cond
--   · exact PB.ifeq_ne_computesEnc h_cond constantEnc_computesEnc Bool.false_ne_true h_else
--   · exact PB.ifeq_eq_computesEnc h_cond constantEnc_computesEnc h_then

-- def succ_fold_body : PB → PB → PB :=
--   fun acc bit =>
--     let carry := acc.fst
--     let new_carry := ifBool carry bit (constantEnc false)
--     let new_bit := boolXor bit carry
--     toPair new_carry (cons new_bit acc.snd)

-- /-- Successor function in binary encocding. -/
-- def succ (x : PB) : PB :=
--   let loop_result := foldl
--     succ_fold_body
--     (toPair (constantEnc true) empty)
--     x
--   let final_carry := loop_result.fst
--   let result_rev := loop_result.snd
--   -- If final carry, prepend 1; otherwise just reverse back
--   reverse (ifBool final_carry (cons (constantEnc true) result_rev) result_rev)

-- lemma succ_computes {p_x : PB} {n : ℕ} (h_x : p_x.ComputesEnc env n) :
--     (succ p_x).ComputesEnc env (n + 1) := by
--   let fold_body_sem := fun (acc : (Bool × List Bool)) (bit : Bool) =>
--     let carry := acc.fst
--     let new_carry := if carry then bit else false
--     let new_bit := Bool.xor bit carry
--     (new_carry, new_bit :: acc.snd)
--   have h_fold_body (e : List Value) (p_acc p_bit : PB) (acc : Bool × List Bool) (bit : Bool)
--         (h_acc : p_acc.ComputesEnc e acc) (h_bit : p_bit.ComputesEnc e bit) :
--       (succ_fold_body p_acc p_bit).ComputesEnc e (fold_body_sem acc bit) := by
--     apply PB.toPair_computesEnc
--     · exact ifBool_computes (PB.fst_ComputesEnc h_acc) h_bit constantEnc_computesEnc
--     · exact cons_computesEnc
--         (boolXor.computes h_bit (PB.fst_ComputesEnc h_acc)) (PB.snd_ComputesEnc h_acc)
--   have h_loop_result :
--       (foldl succ_fold_body (toPair (constantEnc true) empty) p_x).ComputesEnc env
--       (List.foldl fold_body_sem (true, []) (Nat.bits n)) := by
--     exact foldl_computes
--       (toPair_computesEnc constantEnc_computesEnc (empty_computesEnc Bool))
--       h_x
--       fun h_acc h_bit => h_fold_body _ _ _ _ _ h_acc h_bit
--   sorry

-- end PB

end Routine

end RoseTreeMachine

end Turing
