/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Tools
public import Cslib.Computability.Machines.RTM.Arith
public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.List.ReduceOption

/-! # Universal Turing-machine simulator as a rose tree machine

This file defines a rose tree machine that universally simulates all one-tape Turing machines
(for a fixed alphabet).

This means it constructs a `Prog` `p` such that for any Turing machine `tm`, and any input string
`input` when `p` is run on `DataEncode.encode (tm, input)`, in outputs the result of the execution
of the `tm` (if it halts), and does that with a linear overhead in space and a quadratic overhead
in time (conjectured).

TODO:

Extend this such that `p` receives a time bound `t` and then simulates the Turing machine
for exactly `t` steps, and also counts (and returns) the space usae of the Turing machine.
This should allow us to prove most of the diagonalization results.

Note that the proofs of semantic for loop-free programs directly model the computation. we should
write a tactic to automate this.

-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

-- TODO Working on the resource bounds now.
-- The proof outline should be:
-- each iteration of the loop causes the accumulator to grow by at most a constant.
-- this can actually be shown from the semantics and the proof that the tape size grows by at
-- most a constant.
-- then, we show that the time and space of each iteration is linear in its input.
-- so overall, t iterations are computed in O(t^2) time and O(t) space.

variable [DataEncode Symbol]

variable {env : List Value}

public instance : DataEncode (Turing.StackTape Symbol) where
  encode t := DataEncode.encode t.toList
  h_inj := by
    intro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
    grind [DataEncode.h_inj h]

public instance : DataEncode (Turing.BiTape Symbol) where
  encode t := DataEncode.encode (t.head, t.left, t.right)
  h_inj := by
    intro ⟨h₁, l₁, r₁⟩ ⟨h₂, l₂, r₂⟩ h
    grind [DataEncode.h_inj h]

lemma encode_biTape (t : Turing.BiTape Symbol) :
    DataEncode.encode t = DataEncode.encode (t.head, t.left, t.right) := by
    simp [DataEncode.encode]

def bitapeWrite (t v : PB) : PB := PB.cons v t.tail

lemma bitape_write_computes
    {p_tape p_sym : PB} {tape : BiTape Symbol} {sym : Option Symbol}
    (h_tape : p_tape.ComputesEnc env tape)
    (h_sym : p_sym.ComputesEnc env sym) :
    (bitapeWrite p_tape p_sym).ComputesEnc env (tape.write sym) := by
  apply PB.cons_computes h_sym (PB.tail_computes h_tape)

/-- Models `StackTape.cons` -/
def stackTapeCons (x st : PB) : PB :=
  PB.optionElim x
    (PB.elim st
      PB.empty
      (fun _ _ => PB.cons x st))
    (fun _ => PB.cons x st)

lemma stackTapeCons_computes
    {p_x p_st : PB} {x : Option Symbol} {st : StackTape Symbol}
    (h_x : p_x.ComputesEnc env x)
    (h_st : p_st.ComputesEnc env st) :
    (stackTapeCons p_x p_st).ComputesEnc env (st.cons x) := by
  cases x with
  | none =>
    apply PB.optionElim_computesEnc_none h_x
    obtain ⟨l, hl⟩ := st
    cases l with
    | nil => apply PB.elim_nil_computes h_st (PB.empty_computes)
    | cons hd tl =>
      apply PB.elim_cons_computes h_st
        (PB.computesFun₂_const (PB.cons_computes h_x h_st))
  | some a =>
    apply PB.optionElim_computesEnc_some h_x
      (PB.computesFun₂_const (PB.cons_computes h_x h_st))

--- The head component of the bitape
def bitapeHead (t : PB) : PB := t.fst
--- The left component of the bitape
def bitapeLeft (t : PB) : PB := t.snd.fst
--- The right component of the bitape
def bitapeRight (t : PB) : PB := t.snd.snd

lemma bitapeHead_computes {p_t : PB} {t : BiTape Symbol}
    (h_t : p_t.ComputesEnc env t) :
    (bitapeHead p_t).ComputesEnc env t.head := PB.head_computes h_t

lemma bitapeLeft_computes {p_t : PB} {t : BiTape Symbol}
    (h_t : p_t.ComputesEnc env t) :
    (bitapeLeft p_t).ComputesEnc env t.left :=
  PB.head_computes (PB.head_computes (PB.tail_computes h_t))

lemma bitapeRight_computes {p_t : PB} {t : BiTape Symbol}
    (h_t : p_t.ComputesEnc env t) :
    (bitapeRight p_t).ComputesEnc env t.right :=
  PB.head_computes (PB.tail_computes (PB.head_computes (PB.tail_computes h_t)))

lemma encode_stackTape_head (st : StackTape Symbol) :
    (DataEncode.encode st).asList.headD (Data.l []) = DataEncode.encode st.head := by
  obtain ⟨l, hl⟩ := st
  cases l <;> simp [DataEncode.encode, StackTape.head, Data.asList]

lemma encode_stackTape_tail (st : StackTape Symbol) :
    Data.l (DataEncode.encode st).asList.tail = DataEncode.encode st.tail := by
  obtain ⟨l, hl⟩ := st
  cases l <;> simp [DataEncode.encode, StackTape.tail, Data.asList]

lemma stackTapeHead_computes {p_st : PB} {st : StackTape Symbol}
    (h_st : p_st.ComputesEnc env st) :
    (p_st.head).ComputesEnc env st.head := by
  unfold PB.ComputesEnc
  simpa [← encode_stackTape_head] using PB.head_computes h_st

lemma stackTapeTail_computes {p_st : PB} {st : StackTape Symbol}
    (h_st : PB.ComputesEnc env p_st st) :
    (p_st.tail).ComputesEnc env st.tail := by
  unfold PB.ComputesEnc
  simpa [← encode_stackTape_tail] using PB.tail_computes h_st

/-- Models `BiTape.moveLeft` -/
def bitapeMoveLeft (t : PB) : PB :=
  PB.toPair (bitapeLeft t).head
    (PB.toPair
      (bitapeLeft t).tail
      (stackTapeCons (bitapeHead t) (bitapeRight t)))

lemma bitapeMoveLeft_computes {p_t : PB} {t : BiTape Symbol} (h_t : p_t.ComputesEnc env t) :
    PB.ComputesEnc env (bitapeMoveLeft p_t) t.moveLeft :=
  PB.toPair_computesEnc
    (stackTapeHead_computes (bitapeLeft_computes h_t))
    (PB.toPair_computesEnc
      (stackTapeTail_computes (bitapeLeft_computes h_t))
      (stackTapeCons_computes (bitapeHead_computes h_t) (bitapeRight_computes h_t)))

/-- Models `BiTape.moveRight` -/
def bitapeMoveRight (t : PB) : PB :=
  PB.toPair (bitapeRight t).head
    (PB.toPair
      (stackTapeCons (bitapeHead t) (bitapeLeft t))
      (bitapeRight t).tail)

lemma bitapeMoveRight_computes {p_t : PB} {t : BiTape Symbol} (h_t : p_t.ComputesEnc env t) :
    (bitapeMoveRight p_t).ComputesEnc env t.moveRight :=
  PB.toPair_computesEnc
    (stackTapeHead_computes (bitapeRight_computes h_t))
    (PB.toPair_computesEnc
      (stackTapeCons_computes (bitapeHead_computes h_t) (bitapeLeft_computes h_t))
      (stackTapeTail_computes (bitapeRight_computes h_t)))

instance : DataEncode Dir where
  encode := fun
    | Dir.left => DataEncode.encode true
    | Dir.right => DataEncode.encode false
  h_inj := by intro a b h; cases a <;> cases b <;> simp_all [DataEncode.encode]

/-- Models `BiTape.move` -/
def bitapeMove (tape dir : PB) : PB :=
  PB.ifEq dir (PB.constantEnc Dir.left)
    (bitapeMoveLeft tape)
    (bitapeMoveRight tape)

lemma bitapeMove_computes {p_t p_dir : PB} {t : BiTape Symbol} {d : Dir}
    (h_t : p_t.ComputesEnc env t)
    (h_dir : p_dir.ComputesEnc env d) :
    (bitapeMove p_t p_dir).ComputesEnc env (t.move d) :=
  match d with
  | .left =>
    PB.ifeq_eq_computes h_dir PB.constantEnc_computesEnc (bitapeMoveLeft_computes h_t)
  | .right =>
    PB.ifeq_ne_computes h_dir PB.constantEnc_computesEnc (by decide) (bitapeMoveRight_computes h_t)

/-- Models `BiTape.optionMove` -/
def bitapeOptionMove (t dir : PB) : PB :=
  dir.optionElim t (fun d => bitapeMove t d)

lemma bitapeOptionMove_computes {p_t p_dir : PB}
    {t : BiTape Symbol} {d : Option Dir}
    (h_t : p_t.ComputesEnc env t)
    (h_dir : p_dir.ComputesEnc env d) :
    (bitapeOptionMove p_t p_dir).ComputesEnc env (t.optionMove d) :=
  match d with
  | none => PB.optionElim_computesEnc_none h_dir h_t
  | some _ =>
    PB.optionElim_computesEnc_some h_dir (PB.computesFun₂_branch (fun ext =>
      bitapeMove_computes (h_t.extend ext |>.extend _) (PB.var_computes_fresh ext _)))

/-- Encoding of a `SingleTapeTM`, assuming the state set and alphabet are encodable. -/
instance [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol) [DataEncode tm.State] :
    DataEncode (Turing.SingleTapeTM.Cfg tm) where
  encode cfg := DataEncode.encode (cfg.state, cfg.BiTape)
  h_inj := by
    intro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ h
    have heq := DataEncode.h_inj h
    grind

def cfgState (cfg : PB) : PB := cfg.fst
def cfgBitape (cfg : PB) : PB := cfg.snd

lemma cfgState_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {p : PB} {cfg : Turing.SingleTapeTM.Cfg tm}
    (h : p.ComputesEnc env cfg) :
    (cfgState p).ComputesEnc env cfg.state :=
  PB.fst_ComputesEnc (a := (cfg.state, cfg.BiTape)) h

lemma cfgBitape_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {p : PB} {cfg : Turing.SingleTapeTM.Cfg tm}
    (h : p.ComputesEnc env cfg) :
    (cfgBitape p).ComputesEnc env cfg.BiTape :=
  PB.snd_ComputesEnc (a := (cfg.state, cfg.BiTape)) h

/-- Evaluate the transition function. Returns `((wr, dir), q')`.
 -- The return value is not wrapped inside an `Option` because the transition
 -- function is assumed to be total. -/
def evalTr (tr : PB) (q c : PB) : PB :=
  (PB.evalFunGraph (PB.evalFunGraph tr q).head c).head

instance : DataEncode (SingleTapeTM.Stmt Symbol) where
  encode stmt := DataEncode.encode (stmt.symbol, stmt.movement)
  h_inj := by
    intro ⟨s₁, m₁⟩ ⟨s₂, m₂⟩ h
    have heq := DataEncode.h_inj h
    grind

/-- `evalTr` evaluates the transition function if it is given a graph of it as input. -/
lemma evalTr_computes {State : Type} [DataEncode State]
    {p_tr p_q p_c : PB}
    {tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State}
    {stateEnum : List State}
    {symEnum : List (Option Symbol)}
    (h_stateEnum : ∀ q', q' ∈ stateEnum)
    (h_symEnum : ∀ c', c' ∈ symEnum)
    {q : State}
    {c : Option Symbol}
    (h_tr : p_tr.ComputesEnc env
      (stateEnum.map (fun q' : State =>
        (q', symEnum.map (fun c' : Option Symbol => (c', tr q' c'))))))
    (h_q : p_q.ComputesEnc env q)
    (h_c : p_c.ComputesEnc env c) :
    (evalTr p_tr p_q p_c).ComputesEnc env (tr q c) := by
  classical
  exact PB.evalFunGraph_Computes_of_fun (α := Option Symbol) (f := tr q)
    (PB.evalFunGraph_Computes_of_fun (α := State)
      (f := fun q' => symEnum.map (fun c' => (c', tr q' c')))
      h_tr (PB.IsGraphOf.of_complete h_stateEnum) h_q)
    (PB.IsGraphOf.of_complete h_symEnum) h_c

/-- The part of `SingleTapeTM.step` that applies the output of the transition function to the
configuration. -/
def applyTrVal (trVal cfg : PB) : PB :=
  .some (PB.toPair
      trVal.snd
      (bitapeOptionMove (bitapeWrite (cfgBitape cfg) trVal.fst.fst) trVal.fst.snd))

lemma applyTrVal_computes
    [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    [DataEncode tm.State]
    {p_trVal p_cfg : PB}
    {cfg : tm.Cfg}
    {trVal : SingleTapeTM.Stmt Symbol × Option tm.State}
    (h_tr : p_trVal.ComputesEnc env trVal)
    (h_cfg : p_cfg.ComputesEnc env cfg) :
    (applyTrVal p_trVal p_cfg).ComputesEnc env
      (Option.some
        (⟨trVal.snd, (cfg.BiTape.write trVal.fst.1).optionMove trVal.fst.2⟩ : tm.Cfg)) := by
  refine PB.some_ComputesEnc (PB.toPair_computesEnc (PB.snd_ComputesEnc h_tr) ?_)
  refine bitapeOptionMove_computes (bitape_write_computes (cfgBitape_computes h_cfg) ?_) ?_
  · exact PB.fst_ComputesEnc (a := (trVal.fst.1, trVal.fst.2)) (PB.fst_ComputesEnc h_tr)
  · exact PB.snd_ComputesEnc (a := (trVal.fst.1, trVal.fst.2)) (PB.fst_ComputesEnc h_tr)

/-- Models `SingleTapeTM.step`: Compute the step function given a transition function
(as its graph, a list of input-output pairs) and a configuration. Returns `Option Cfg`. -/
def singleTapeTMStep (tr : PB) (cfg : PB) : PB :=
  PB.optionElim (cfgState cfg)
    PB.empty
    (fun q' => applyTrVal (evalTr tr q' (cfgBitape cfg).head) cfg)

lemma singleTapeTMStep_computes
    [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    [DataEncode tm.State]
    {stateEnum : List tm.State}
    {symEnum : List (Option Symbol)}
    (h_stateEnum : ∀ q', q' ∈ stateEnum)
    (h_symEnum : ∀ c', c' ∈ symEnum)
    {p_tr p_cfg : PB}
    {cfg : tm.Cfg}
    (h_tr : p_tr.ComputesEnc env
      (stateEnum.map (fun q' =>
        (q', symEnum.map (fun c' : Option Symbol => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.ComputesEnc env cfg) :
    (singleTapeTMStep p_tr p_cfg).ComputesEnc env (tm.step cfg) := by
  obtain ⟨state, t⟩ := cfg
  cases h : state with
  | none =>
    exact PB.optionElim_computesEnc_none
      (by simpa [h] using (cfgState_computes h_cfg))
      PB.empty_computes
  | some cfg =>
    refine PB.optionElim_computesEnc_some (by simpa [h] using (cfgState_computes h_cfg)) ?_
    apply PB.computesFun₂_branch
    intro ext
    refine applyTrVal_computes ?_ (h_cfg.extend ext |>.extend _)
    refine evalTr_computes h_stateEnum h_symEnum
      (h_tr.extend ext |>.extend _) (PB.var_computes_fresh ext _) ?_
    exact PB.head_computes (cfgBitape_computes (h_cfg.extend ext |>.extend _))

/-- Run the step function for `steps` iterations, staying at a halting configuration. -/
def timeBoundedSimulatorMain (tr cfg steps : PB) : PB :=
  PB.forLoop steps cfg (fun _ cfg => (singleTapeTMStep tr cfg).optionElim cfg (fun next => next))

lemma timeBoundedSimulatorMain_computes
    [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    [DataEncode tm.State]
    {p_tr p_cfg p_steps : PB}
    {cfg : tm.Cfg}
    {steps : ℕ}
    {stateEnum : List tm.State}
    {symEnum : List (Option Symbol)}
    (h_stateEnum : ∀ q', q' ∈ stateEnum)
    (h_symEnum : ∀ c', c' ∈ symEnum)
    (h_tr : p_tr.ComputesEnc env
      (stateEnum.map (fun q' =>
        (q', symEnum.map (fun c' : Option Symbol => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.ComputesEnc env cfg)
    (h_steps : p_steps.ComputesEnc env steps) :
    (timeBoundedSimulatorMain p_tr p_cfg p_steps).ComputesEnc env
      ((fun c => (tm.step c).getD c)^[steps] cfg) := by
  have : ∀ g m (b : tm.Cfg), g^[m] b = (List.range m).foldl (fun c _ => g c) b := by
    intro g m
    induction m with
    | zero => simp
    | succ m ih =>
      intro b
      simp [Function.iterate_succ_apply', ih, List.range_succ]
  rw [this]
  apply PB.forLoop_computes (f := fun _ c => (tm.step c).getD c) h_steps h_cfg
  intro e pi pacc i c hpre h_pi h_acc
  obtain ⟨more, rfl⟩ := hpre
  have hstep := singleTapeTMStep_computes h_stateEnum h_symEnum (h_tr.extend more) h_acc
  cases hsc : tm.step c with
  | none => exact PB.optionElim_computesEnc_none (hsc ▸ hstep) h_acc
  | some next =>
    exact PB.optionElim_computesEnc_some (hsc ▸ hstep)
      (PB.computesFun₂_branch (fun ext => PB.var_computes_fresh ext _))

def stringToTape (input : PB) : PB :=
  PB.toPair input.listHeadOption (PB.toPair .empty (input.tail.listMap .some))

lemma stringToTape_computes
    {p_input : PB}
    {input : List Symbol}
    (h_input : p_input.ComputesEnc env input) :
    (stringToTape p_input).ComputesEnc env (BiTape.mk₁ input) := by
  cases input with
  | nil =>
    refine PB.toPair_computesEnc (PB.listHeadOption_computes h_input)
      (PB.toPair_computesEnc PB.empty_computes ?_)
    exact PB.listMap_computes (l := [])
      (PB.tail_computes h_input) (fun {e} px x hpx => PB.some_ComputesEnc hpx)
  | cons hd tl =>
    refine PB.toPair_computesEnc (PB.listHeadOption_computes h_input)
      (PB.toPair_computesEnc PB.empty_computes ?_)
    exact PB.listMap_computes
      (PB.tail_computes h_input) (fun {e} px x hpx => PB.some_ComputesEnc hpx)

def initialConfig (q₀ : PB) (input : PB) : PB :=
  PB.toPair (.some q₀) (stringToTape input)

lemma initialConfig_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {p_q₀ p_input : PB} {input : List Symbol}
    (h_q₀ : p_q₀.ComputesEnc env tm.q₀)
    (h_input : p_input.ComputesEnc env input) :
    (initialConfig p_q₀ p_input).ComputesEnc env (tm.initCfg input) :=
  PB.toPair_computesEnc (PB.some_ComputesEnc h_q₀) (stringToTape_computes h_input)

def tapeCellsToOutputF (l : List (Option Symbol)) : Option (List Symbol) :=
  l.foldl
    (fun res s =>
      match res with
      | none => none
      | some res => match s with
        | none => none
        | some s => some (res ++ [s]))
    (some [])

def tapeCellsToOutput (l : PB) : PB :=
  PB.foldl (fun res s =>
    res.optionElim
      .none
      (fun res => s.optionElim .none (fun s => .some (.listAppend res (.some s)))))
    (PB.some .empty)
    l

lemma tapeCellsToOutput_computes
    {p_l : PB}
    {l : List (Option Symbol)}
    (h_l : p_l.ComputesEnc env l) :
    (tapeCellsToOutput p_l).ComputesEnc env (tapeCellsToOutputF l) := by
  apply PB.foldl_computes (PB.some_ComputesEnc (PB.empty_computesEnc _)) h_l
  intro e p_res p_s res s h_res h_s
  cases res with
  | none => exact PB.optionElim_computesEnc_none h_res PB.none_computes
  | some res =>
    refine PB.optionElim_computesEnc_some h_res (PB.computesFun₂_branch (fun ext => ?_))
    cases s with
    | none =>
      exact PB.optionElim_computesEnc_none ((h_s.extend ext).extend _) PB.none_computes
    | some s =>
      refine PB.optionElim_computesEnc_some ((h_s.extend ext).extend _)
        (PB.computesFun₂_branch (fun ext2 => ?_))
      exact PB.some_ComputesEnc (PB.listAppend_computes
        (((PB.var_computes_fresh ext _).extend ext2).extend _)
        (PB.cons_computesEnc (PB.var_computes_fresh ext2 _) (PB.empty_computesEnc _)))


def tapeToOutputF
    (tape : BiTape Symbol) : Option (List Symbol) :=
  if !tape.left.toList.isEmpty then
    none
  else if tape.right.toList.isEmpty && tape.head.isNone then
    some []
  else
    tapeCellsToOutputF (tape.head :: tape.right.toList)

def tapeToOutput (tape : PB) : PB :=
  PB.boolIte (.boolNot (bitapeLeft tape).listIsEmpty)
    .none
  (.boolIte (.boolAnd (bitapeRight tape).listIsEmpty (bitapeHead tape).isNone)
      (PB.some .empty)
      (tapeCellsToOutput (PB.cons (bitapeHead tape) (bitapeRight tape))))

lemma tapeToOutput_computes
    {p_tape : PB}
    {tape : BiTape Symbol}
    (h_tape : p_tape.ComputesEnc env tape) :
    (tapeToOutput p_tape).ComputesEnc env (tapeToOutputF tape) := by
  refine PB.boolIte_computes
    (PB.boolNot_computes (PB.listIsEmpty_computes (bitapeLeft_computes h_tape)))
    (PB.empty_computes) ?_
  refine PB.boolIte_computes (α := Option (List Symbol)) ?_ ?_ ?_
  · refine PB.boolAnd_computes
      (PB.listIsEmpty_computes (bitapeRight_computes h_tape))
      (PB.isNone_computes (bitapeHead_computes h_tape))
  · exact PB.some_ComputesEnc (PB.empty_computesEnc (Option (List Symbol)))
  · exact tapeCellsToOutput_computes
      (PB.cons_computesEnc (bitapeHead_computes h_tape) (bitapeRight_computes h_tape))

omit [DataEncode Symbol] in
/-- `tapeCellsToOutputF` succeeds exactly when every cell is filled, returning the unwrapped
list. -/
lemma tapeCellsToOutputF_eq_some_iff (os : List (Option Symbol)) (r : List Symbol) :
    tapeCellsToOutputF os = some r ↔ os = r.map some := by
  rw [tapeCellsToOutputF]
  set F : Option (List Symbol) → Option Symbol → Option (List Symbol) :=
    fun res s => match res with
      | none => none
      | some res => match s with
        | none => none
        | some s => some (res ++ [s]) with hF
  have foldNone : ∀ os, List.foldl F none os = none := by
    intro os
    induction os with
    | nil => rfl
    | cons o os ih => rw [List.foldl_cons, show F none o = none from by rw [hF]]; exact ih
  have : ∀ (os : List (Option Symbol)) (acc r : List Symbol),
      List.foldl F (some acc) os = some r ↔ ∃ l, os = l.map some ∧ r = acc ++ l := by
    intro os
    induction os with
    | nil =>
      intro acc r
      simp only [List.foldl_nil, Option.some.injEq]
      constructor
      · exact fun h => ⟨[], by simp, by simp [h]⟩
      · rintro ⟨l, hl, hr⟩
        obtain rfl : l = [] := by simpa using hl.symm
        simpa using hr.symm
    | cons o os ih =>
      intro acc r
      cases o with
      | none =>
        rw [List.foldl_cons, show F (some acc) none = none from by rw [hF], foldNone]
        constructor
        · exact fun h => absurd h (by simp)
        · rintro ⟨l, hl, -⟩; cases l <;> simp at hl
      | some x =>
        rw [List.foldl_cons, show F (some acc) (some x) = some (acc ++ [x]) from by rw [hF], ih]
        constructor
        · rintro ⟨l, hl, hr⟩; exact ⟨x :: l, by simp [hl], by simp [hr]⟩
        · rintro ⟨l, hl, hr⟩
          cases l with
          | nil => simp at hl
          | cons y l =>
            simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact ⟨l, rfl, by simp [hr]⟩
  rw [this]
  simp only [List.nil_append]
  exact ⟨fun ⟨_, hos, hr⟩ => hr ▸ hos, fun hos => ⟨r, hos, rfl⟩⟩

omit [DataEncode Symbol] in
lemma tapeToOutput_iff_mk₁ [Inhabited Symbol]
    (tape : BiTape Symbol) (s : List Symbol) :
  (tape = .mk₁ s) ↔ tapeToOutputF tape = some s := by
  obtain ⟨hd, lft, rgt⟩ := tape
  simp only [tapeToOutputF]
  by_cases hl : lft.toList = []
  · rw [if_neg (by simp [hl])]
    obtain rfl : lft = ∅ := by cases lft; simp_all [StackTape.nil]
    by_cases hr : (rgt.toList.isEmpty && hd.isNone) = true
    · rw [if_pos hr]
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hr
      obtain ⟨hr1, hr2⟩ := hr
      subst hr2
      obtain rfl : rgt = ∅ := by cases rgt; simp_all [StackTape.nil]
      rw [Option.some.injEq]
      constructor
      · intro h; cases s with
        | nil => rfl
        | cons a t => simp [BiTape.mk₁, BiTape.mk.injEq] at h
      · rintro rfl; simp [BiTape.mk₁, BiTape.nil]
    · rw [if_neg hr, tapeCellsToOutputF_eq_some_iff]
      cases s with
      | nil =>
        simp only [BiTape.mk₁, List.map_nil]
        constructor
        · intro h
          simp only [BiTape.empty_eq_nil, BiTape.nil, BiTape.mk.injEq] at h
          obtain ⟨hhd, -, hrgt⟩ := h
          subst hhd; subst hrgt
          exact absurd (by simp [StackTape.nil]) hr
        · exact fun h => absurd h (by simp)
      | cons a t =>
        simp only [BiTape.mk₁, List.map_cons]
        constructor
        · intro h
          rw [BiTape.mk.injEq] at h
          obtain ⟨hhd, -, hrgt⟩ := h
          rw [hhd, hrgt]; simp [StackTape.mapSome]
        · intro h
          rw [List.cons.injEq] at h
          obtain ⟨hhd, hrgt⟩ := h
          rw [BiTape.mk.injEq]
          refine ⟨hhd, rfl, ?_⟩
          cases rgt with | mk R hR => simp_all [StackTape.mapSome]
  · rw [if_pos (by simp [hl])]
    simp only [reduceCtorEq, iff_false]
    intro hcontra
    apply hl
    have : lft = (BiTape.mk₁ s).left := by rw [← hcontra]
    rw [this]
    cases s <;> simp [BiTape.mk₁, BiTape.nil, StackTape.nil]


def timeBoundedSimulator (input : PB) :=
  let q₀ := input.fst.fst
  let tr := input.fst.snd
  let inputStr := input.snd.fst
  let steps := input.snd.snd
  let cfg := timeBoundedSimulatorMain tr (initialConfig q₀ inputStr) steps
  PB.boolIte cfg.fst.isNone .none (tapeToOutput cfg.snd)

def timeBoundedSimulatorF [Inhabited Symbol] [Fintype Symbol]
    (tm : SingleTapeTM Symbol) [DataEncode tm.State]
    (input : List Symbol)
    (steps : ℕ) : Option (List Symbol) :=
  let cfg := (fun c => (tm.step c).getD c)^[steps] (tm.initCfg input)
  if cfg.state.isNone then none else tapeToOutputF cfg.BiTape

lemma timeBoundedSimulator_computes [Inhabited Symbol] [Fintype Symbol]
    {p_input : PB}
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {input : List Symbol}
    {steps : ℕ}
    {stateEnum : List tm.State}
    {symEnum : List (Option Symbol)}
    (h_stateEnum : ∀ q', q' ∈ stateEnum)
    (h_symEnum : ∀ c', c' ∈ symEnum)
    (h_input : p_input.ComputesEnc env
      ((tm.q₀, (stateEnum.map (fun q' =>
        (q', symEnum.map (fun c' : Option Symbol => (c', tm.tr q' c')))))),
       input,
       steps)) :
    (timeBoundedSimulator p_input).ComputesEnc env (timeBoundedSimulatorF tm input steps) := by
  let h_main := timeBoundedSimulatorMain_computes
      h_stateEnum
      h_symEnum
      (PB.snd_ComputesEnc (PB.fst_ComputesEnc h_input))
      (initialConfig_computes
        (PB.fst_ComputesEnc (PB.fst_ComputesEnc h_input))
        (PB.fst_ComputesEnc (PB.snd_ComputesEnc h_input)))
      (PB.snd_ComputesEnc (PB.snd_ComputesEnc h_input))
  exact PB.boolIte_computes
    (PB.isNone_computes (cfgState_computes h_main))
    PB.none_computes
    (tapeToOutput_computes (cfgBitape_computes h_main))

/-- Encode `Bool` into an alphabet of size at least 2. -/
def boolIntoFink {k} : Bool → Fin (k + 2)
  | true => 0
  | false => 1

/-- The list of all elements of `Fin n`. -/
def finRange (n : ℕ) : List (Fin n) :=
  List.ofFn id

noncomputable def encodeTMTr {k₁ : ℕ} (tm : SingleTapeTM (Fin (k₁ + 2))) :=
  (Fintype.elems : Finset tm.State).toList.map fun q => (q,
    (Fintype.elems : Finset (Option (Fin (k₁ + 2)))).toList.map fun c => (c, tm.tr q c))

instance {k : ℕ} : DataEncode (Fin k) where
  encode x := DataEncode.encode x.val
  h_inj := by grind [DataEncode.h_inj, Function.Injective]

lemma universal_time_bounded_simulator_inner :
  ∃ overhead : ℕ, ∀
  {k₁ : ℕ}
  (tm : SingleTapeTM (Fin (k₁ + 2)))
  [DataEncode tm.State]
  (input output : List Bool)
  (steps : ℕ),
  tm.OutputsWithinTime (input.map boolIntoFink) (output.map boolIntoFink) steps ↔
    ∃ s,
    PB.ComputesInTimeAndSpace
      timeBoundedSimulator
      ((tm.q₀, encodeTMTr tm), input, steps)
      (Option.some output)
      -- The simulation has quadratic overhead (`steps * steps`), but it is independent
      -- of the input size.
      (overhead * (DataEncode.encode (encodeTMTr tm)).size * steps * steps +
        overhead * (DataEncode.encode (encodeTMTr tm)).size)
      s
   := by
  sorry

--------------------------------------------------------
-- The rest is the while-loop based simulator
---------------------------------------------------------


/-- The main loop of the Turing machine simulation: Execute a step until we reach a halting
configuration, then return it. -/
def tmWhileLoop (tr : PB) (cfg : PB) : PB :=
  -- The accumulator is the current `Cfg`. The body applies `singleTapeTM_step`
  -- (an `Option Cfg`); on `some next` we continue with `next`, on `none` we keep
  -- the current `acc` (which has `state = none`, signalling halt to `while_`).
  PB.while_ cfg
    (fun acc => (singleTapeTMStep tr acc).optionElim acc (fun next => next))

lemma tmWhileLoop_computes
    [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    [DataEncode tm.State]
    {p_tr p_cfg : PB}
    {cfg : tm.Cfg}
    {stateEnum : List tm.State}
    {symEnum : List (Option Symbol)}
    (h_stateEnum : ∀ q', q' ∈ stateEnum)
    (h_symEnum : ∀ c', c' ∈ symEnum)
    (h_tr : p_tr.ComputesEnc env
      (stateEnum.map (fun q' : tm.State =>
        (q', symEnum.map (fun c' : Option Symbol => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.ComputesEnc env cfg)
    (h_halts : ∃ n, (((fun c => (tm.step c).getD c)^[n] cfg)).state = none) :
    (tmWhileLoop p_tr p_cfg).ComputesEnc env
      ((fun c => (tm.step c).getD c)^[Nat.find h_halts] cfg) := by
  -- Totalise `tm.step`; halting states become fixed points.
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with step_def
  have halt_fix : ∀ c : tm.Cfg, c.state = none → step c = c := by
    intro c hc
    obtain ⟨s, t⟩ := c
    cases s with
    | none => simp [step_def]
    | some q => simp at hc
  -- The head of an encoded `Cfg` is empty iff its state is `none` (the loop's halt condition).
  have headEmpty_iff : ∀ c : tm.Cfg,
      (DataEncode.encode c).asList.head?.getD (Data.l []) = Data.l [] ↔ c.state = none := by
    rintro ⟨s, t⟩; cases s <;> simp [DataEncode.encode]
  -- One iteration of the loop body computes `step c`.
  have body_computes : ∀ c : tm.Cfg,
      PB.computesFun₁ env (.data (DataEncode.encode c))
        (fun acc => PB.optionElim (singleTapeTMStep p_tr acc) acc (fun next => next))
        (.data (DataEncode.encode (step c))) := by
    intro c
    apply PB.computesFun₁_branch
    intro ext
    have h_acc : (PB.var (env.length + ext.length)).ComputesEnc _ c := PB.var_computes_fresh ext []
    have h_step := singleTapeTMStep_computes h_stateEnum h_symEnum
        (h_tr.extend ext |>.extend _) h_acc
    cases hsc : tm.step c with
    | none =>
      rw [show step c = c from by simp only [step_def, hsc, Option.getD_none]]
      exact PB.optionElim_computesEnc_none (hsc ▸ h_step) h_acc
    | some next =>
      rw [show step c = next from by simp only [step_def, hsc, Option.getD_some]]
      refine PB.optionElim_computesEnc_some (hsc ▸ h_step)
        (PB.computesFun₂_branch (fun ext2 => PB.var_computes_fresh ext2 _))
  -- Iterate the body from `c` to its halting configuration after `n` steps.
  have loop : ∀ (n : ℕ) (c : tm.Cfg), (step^[n] c).state = none →
      PB.WhileComputes env
        (fun acc => PB.optionElim (singleTapeTMStep p_tr acc) acc (fun next => next))
        (DataEncode.encode c) (DataEncode.encode (step^[n] c)) := by
    intro n
    induction n with
    | zero => exact fun c hc => PB.WhileComputes.halt ((headEmpty_iff c).mpr hc)
    | succ n ih =>
      intro c hc
      by_cases hstate : c.state = none
      · rw [Function.iterate_fixed (halt_fix c hstate) (n + 1)]
        exact PB.WhileComputes.halt ((headEmpty_iff c).mpr hstate)
      · rw [Function.iterate_succ, Function.comp_apply] at hc ⊢
        exact PB.WhileComputes.step
          (fun h => hstate ((headEmpty_iff c).mp h)) (body_computes c) (ih (step c) hc)
  exact PB.while_computes h_cfg (loop (Nat.find h_halts) cfg (Nat.find_spec h_halts))


/-- Compute the final output from the tape contents: the symbol under the head followed by the
contents to its right, with blank (`none`) cells removed.

This is only meaningful for halting configurations whose tape is in canonical (`mk₁`) form, i.e.
with an empty left part — which is exactly the shape of the `haltCfg`s produced by `Outputs`. -/
def finalConfigToOutput (cfg : PB) : PB :=
  (PB.cons (bitapeHead (cfgBitape cfg)) (bitapeRight (cfgBitape cfg))).listReduceOption

lemma finalConfigToOutput_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {p_cfg : PB} {cfg : tm.Cfg}
    (h_cfg : p_cfg.ComputesEnc env cfg) :
    (finalConfigToOutput p_cfg).ComputesEnc env
      (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption :=
  PB.listReduceOption_computes
    (PB.cons_computesEnc
      (bitapeHead_computes (cfgBitape_computes h_cfg))
      (bitapeRight_computes (cfgBitape_computes h_cfg)))

def tmSimulator (input : PB) :=
  finalConfigToOutput (tmWhileLoop input.fst.snd (initialConfig input.fst.fst input.snd))

/-- Translate Relation.ReflTransGen, the construct underlying `SingleTapeTM.Outputs`, into
iteration of the step function. -/
private lemma reflTransGen_iff_exists_iter {α : Type} (step : α → Option α) {x y : α} :
    Relation.ReflTransGen (fun a b => step a = some b) x y ↔
      ∃ n, (fun a => ((step a).getD a))^[n] x = y := by
  constructor
  · intro h
    obtain ⟨n, h_relates⟩ := Relation.ReflTransGen.relatesInSteps h
    clear h
    refine ⟨n, ?_⟩
    induction n generalizing x with
    | zero => simpa using h_relates
    | succ n ih =>
      obtain ⟨c, h_step, h_rel⟩ := Relation.RelatesInSteps.succ' h_relates
      rw [Function.iterate_succ_apply]
      have hc : (step x).getD x = c := by simp [h_step]
      simpa [hc] using ih h_rel
  · intro h
    obtain ⟨n, h⟩ := h
    induction n generalizing x with
    | zero =>
      simp only [Function.iterate_zero, id_eq] at h
      subst h
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      refine Relation.ReflTransGen.trans ?_ (ih h)
      cases hs : step x with
      | none => simpa using Relation.ReflTransGen.refl
      | some c =>
        simp only [Option.getD_some]
        exact Relation.ReflTransGen.single hs

omit env [DataEncode Symbol] in
/-- If the totalised step function reaches a halting configuration `y` after `N` iterations,
then it also reaches `y` at the *first* halting index `Nat.find h_halts` (halting configurations
are fixpoints of the totalised step, so the orbit stabilises). This bridges
`reflTransGen_iff_exists_iter` (which gives *some* witness `N`) and `tmWhileLoop_computes` (whose
result is indexed by `Nat.find h_halts`). -/
private lemma iterate_find_state_eq [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    {x y : tm.Cfg}
    {N : ℕ}
    (hN : (fun c => (tm.step c).getD c)^[N] x = y)
    (hy : y.state = none)
    (h_halts : ∃ n, ((fun c => (tm.step c).getD c)^[n] x).state = none) :
    (fun c => (tm.step c).getD c)^[Nat.find h_halts] x = y := by
  set g : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with hg
  have halt_fix : ∀ c : tm.Cfg, c.state = none → g c = c := by
    intro c hc
    obtain ⟨s, t⟩ := c
    cases s with
    | none => simp [hg]
    | some q => simp at hc
  have hNw : (g^[N] x).state = none := by rw [hN]; exact hy
  have hkN : Nat.find h_halts ≤ N := Nat.find_le hNw
  have hfix : g (g^[Nat.find h_halts] x) = g^[Nat.find h_halts] x :=
    halt_fix _ (Nat.find_spec h_halts)
  have heq : g^[N] x = g^[Nat.find h_halts] x := by
    conv_lhs => rw [show N = (N - Nat.find h_halts) + Nat.find h_halts by omega,
      Function.iterate_add_apply]
    exact Function.iterate_fixed hfix (N - Nat.find h_halts)
  rw [← heq]
  exact hN

omit env [DataEncode Symbol] in
/-- The output list is recovered from the `BiTape` built by `mk₁`:
its head followed by the right-hand contents, with the padding `none`s removed. -/
private lemma mk₁_reduceOption (l : List Symbol) :
    ((BiTape.mk₁ l).head :: (BiTape.mk₁ l).right.toList).reduceOption = l := by
  cases l with
  | nil => rfl
  | cons h t =>
    change h :: (t.map Option.some).reduceOption = h :: t
    simp only [List.cons.injEq, true_and]
    induction t with
    | nil => rfl
    | cons a s ih => simp [ih]

lemma tmSimulatorComputes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {p_input : PB}
    {input output : List Symbol}
    {stateEnum : List tm.State}
    {symEnum : List (Option Symbol)}
    (h_stateEnum : ∀ q', q' ∈ stateEnum)
    (h_symEnum : ∀ c', c' ∈ symEnum)
    (h_input : p_input.ComputesEnc env
      ((tm.q₀, (stateEnum.map (fun q' =>
        (q', symEnum.map (fun c' : Option Symbol => (c', tm.tr q' c')))))),
       input)) :
    tm.Outputs input output → (tmSimulator p_input).ComputesEnc env output := by
  intro h_outputs
  -- Build the initial-configuration computation from the encoded input `((q₀, table), input)`.
  have h_cfg := initialConfig_computes (tm := tm)
    (PB.fst_ComputesEnc (PB.fst_ComputesEnc h_input)) (PB.snd_ComputesEnc h_input)
  -- From `Outputs`, the totalised step reaches `haltCfg output` after some `N` iterations.
  obtain ⟨N, hN⟩ := (reflTransGen_iff_exists_iter
    tm.step (x := tm.initCfg input) (y := tm.haltCfg output)).mp h_outputs
  -- Hence it eventually reaches a halting state, and `tmWhileLoop` computes that config.
  have h_halts : ∃ n, ((fun c => (tm.step c).getD c)^[n] (tm.initCfg input)).state = none :=
    ⟨N, by rw [hN]; rfl⟩
  have h_main :
      (tmWhileLoop p_input.fst.snd (initialConfig p_input.fst.fst p_input.snd)).ComputesEnc
        env (tm.haltCfg output) := by
    have := tmWhileLoop_computes h_stateEnum h_symEnum
      (PB.snd_ComputesEnc (PB.fst_ComputesEnc h_input)) h_cfg h_halts
    rwa [iterate_find_state_eq hN rfl h_halts] at this
  -- The simulator extracts the output from the halting configuration's canonical tape.
  have hval : ((tm.haltCfg output).BiTape.head ::
      (tm.haltCfg output).BiTape.right.toList).reduceOption = output := mk₁_reduceOption output
  simpa only [hval, tmSimulator] using finalConfigToOutput_computes h_main


end RoseTreeMachine

end Turing
