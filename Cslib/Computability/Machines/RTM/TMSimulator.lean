/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Tools
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
  PB.optionElim dir
    t
    (fun d => bitapeMove t d)

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

lemma evalTr_computes {State : Type} [Fintype State] [DataEncode State]
    [Fintype Symbol]
    {p_tr p_q p_c : PB}
    {tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State}
    {q : State}
    {c : Option Symbol}
    (h_tr : p_tr.ComputesEnc env
      ((Fintype.elems : Finset State).toList.map (fun q' : State =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' : Option Symbol => (c', tr q' c'))))))
    (h_q : p_q.ComputesEnc env q)
    (h_c : p_c.ComputesEnc env c) :
    (evalTr p_tr p_q p_c).ComputesEnc env (tr q c) := by
  exact PB.evalFunGraph_Computes_of_fun (α := Option Symbol) (f := tr q)
    (PB.evalFunGraph_Computes_of_fun (α := State) (f := fun q' =>
      (Fintype.elems : Finset (Option Symbol)).toList.map (fun c' => (c', tr q' c')))
      h_tr h_q) h_c

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
    {p_tr p_cfg : PB}
    {cfg : tm.Cfg}
    (h_tr : p_tr.ComputesEnc env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
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
    refine evalTr_computes (h_tr.extend ext |>.extend _) (PB.var_computes_fresh ext _) ?_
    exact PB.head_computes (cfgBitape_computes (h_cfg.extend ext |>.extend _))

/-- The main loop of the Turing machine simulation: Execute a step until we reach a halting
configuration, then return it. -/
def tmMainLoop (tr : PB) (cfg : PB) : PB :=
  -- The accumulator is the current `Cfg`. The body applies `singleTapeTM_step`
  -- (an `Option Cfg`); on `some next` we continue with `next`, on `none` we keep
  -- the current `acc` (which has `state = none`, signalling halt to `while_`).
  PB.while_ cfg
    (fun acc => PB.optionElim (singleTapeTMStep tr acc) acc (fun next => next))

lemma tmMainLoop_computes
    [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    [DataEncode tm.State]
    {p_tr p_cfg : PB}
    {cfg : tm.Cfg}
    (h_tr : p_tr.ComputesEnc env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.ComputesEnc env cfg)
    (h_halts : ∃ n, (((fun c => (tm.step c).getD c)^[n] cfg)).state = none) :
    (tmMainLoop p_tr p_cfg).ComputesEnc env
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
    have h_step := singleTapeTMStep_computes (h_tr.extend ext |>.extend _) h_acc
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

/-- Compute the final output from the tape contents.
Note that since the single tape Turing machine requires the "left" part of the tape to be empty,
we need to produce "no output" if the left part of the tape is non-empty. The only way
for us to achieve that is to go into an infinite loop. This makes the semantics theorems a bit
more awkward. -/
def finalConfigToOutput (cfg : PB) : PB :=
  PB.ifEq (bitapeLeft (cfgBitape cfg)) PB.empty
    (PB.cons (bitapeHead (cfgBitape cfg)) (bitapeRight (cfgBitape cfg))).listReduceOption
    PB.diverge

lemma finalConfigToOutput_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {p_cfg : PB} {cfg : tm.Cfg}
    (h_cfg : p_cfg.ComputesEnc env cfg) :
    (finalConfigToOutput p_cfg).ComputesEnc env
      (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption ↔
        cfg.BiTape.left.toList = [] := by
  constructor
  · intro h_comp
    by_contra h_left
    obtain ⟨t, s, hps⟩ := h_comp []
    simp only [List.append_nil, List.length_nil, Nat.add_zero,
      finalConfigToOutput, PB.ifEq, PB.empty] at hps
    cases hps with
    | ifEq_then h_x h_y h_then =>
      cases h_y
      obtain ⟨tbl, sbl, hbl⟩ := (bitapeLeft_computes (cfgBitape_computes h_cfg)) []
      simp only [List.append_nil, List.length_nil, Nat.add_zero] at hbl
      injection (ProgSem.det h_x hbl) with e1
      apply h_left
      exact (DataEncode_list_eq_nil_iff_nil _).mp (e1.symm)
    | ifEq_else h_x h_y hne h_else => exact PB.diverge_not_progSem h_else
  · intro h_left
    have h_bitape_left : cfg.BiTape.left = StackTape.nil :=
      DataEncode.h_inj (by
        change DataEncode.encode (cfg.BiTape.left.toList)
           = DataEncode.encode ((StackTape.nil : StackTape Symbol).toList)
        rw [h_left, StackTape.nil_toList])
    apply PB.ifeq_eq_computes
      (bitapeLeft_computes (cfgBitape_computes h_cfg))
      (by rw [h_bitape_left];  exact PB.empty_computesEnc (Option Symbol))
      (PB.listReduceOption_computes
        (PB.cons_computesEnc
          (bitapeHead_computes (cfgBitape_computes h_cfg))
          (bitapeRight_computes (cfgBitape_computes h_cfg))))

def tmSimulator (input : PB) :=
  finalConfigToOutput (tmMainLoop input.fst.snd (initialConfig input.fst.fst input.snd))

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
`reflTransGen_iff_exists_iter` (which gives *some* witness `N`) and `tmMainLoop_computes` (whose
result is indexed by `Nat.find h_halts`). -/
private lemma iterate_find_state_eq [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} {x y : tm.Cfg} {N : ℕ}
    (hN : (fun c => (tm.step c).getD c)^[N] x = y) (hy : y.state = none)
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
  rw [← heq]; exact hN

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
    (h_input : p_input.ComputesEnc env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       input)) :
    tm.Outputs input output ↔ (tmSimulator p_input).ComputesEnc env output := by
  constructor
  · intro h_outputs
    -- Build the initial-configuration computation from the encoded input `((q₀, table), input)`.
    have h_cfg := initialConfig_computes (tm := tm)
      (PB.fst_ComputesEnc (PB.fst_ComputesEnc h_input)) (PB.snd_ComputesEnc h_input)
    -- From `Outputs`, the totalised step reaches `haltCfg output` after some `N` iterations.
    obtain ⟨N, hN⟩ := (reflTransGen_iff_exists_iter
      tm.step (x := tm.initCfg input) (y := tm.haltCfg output)).mp h_outputs
    -- Hence it eventually reaches a halting state, and `tmMainLoop` computes that config.
    have h_halts : ∃ n, ((fun c => (tm.step c).getD c)^[n] (tm.initCfg input)).state = none :=
      ⟨N, by rw [hN]; rfl⟩
    have h_main :
        (tmMainLoop p_input.fst.snd (initialConfig p_input.fst.fst p_input.snd)).ComputesEnc
          env (tm.haltCfg output) := by
      have := tmMainLoop_computes (PB.snd_ComputesEnc (PB.fst_ComputesEnc h_input)) h_cfg h_halts
      rwa [iterate_find_state_eq hN rfl h_halts] at this
    -- The simulator extracts the output from the halting configuration's tape.
    have h_left : (tm.haltCfg output).BiTape.left.toList = [] := by
      cases output <;> rfl
    have hval : ((tm.haltCfg output).BiTape.head ::
        (tm.haltCfg output).BiTape.right.toList).reduceOption = output := mk₁_reduceOption output
    simpa only [hval, tmSimulator] using (finalConfigToOutput_computes h_main).mpr h_left
  · intro h_comp
    sorry



/- TODO: What is left to do here is
 - construct the initial configuration from the input string
 - extract the output string from the final configuration.
 - and of course prove the resource bounds
-/
end RoseTreeMachine

end Turing
