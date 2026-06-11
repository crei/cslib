/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Tools
public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.List.ReduceOption

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

-- /-- Prepend an `Option` to the `StackTape` -/
-- @[scoped grind]
-- def cons (x : Option Symbol) (xs : StackTape Symbol) : StackTape Symbol :=
--   match x, xs with
--   | none, ⟨[], _⟩ => ⟨[], by grind⟩
--   | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
--   | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩

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

-- def move_left (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

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

-- def move_right (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

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

-- /--
-- Move the head to the left or right, shifting the tape underneath it.
-- -/
-- def move (t : BiTape Symbol) : Dir → BiTape Symbol
--   | .left => t.move_left
--   | .right => t.move_right

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

-- /--
-- Optionally perform a `move`, or do nothing if `none`.
-- -/
-- def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
--   | t, none => t
--   | t, some d => t.move d

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

lemma cfg_bitape_computes [Inhabited Symbol] [Fintype Symbol]
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

-- /-- The step function corresponding to a `SingleTapeTM`. -/
-- @[simp]
-- def step : tm.Cfg → Option tm.Cfg
--   | ⟨none, _⟩ =>
--     -- If in the halting state, there is no next configuration
--     none
--   | ⟨some q', t⟩ =>
--     -- If in state q', perform look up in the transition function
--     match tm.tr q' t.head with
--     -- and enter a new configuration with state q'' (or none for halting)
--     -- and tape updated according to the Stmt
--     | ⟨⟨wr, dir⟩, q''⟩ => some ⟨q'', (t.write wr).optionMove dir⟩

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
  refine bitapeOptionMove_computes (bitape_write_computes (cfg_bitape_computes h_cfg) ?_) ?_
  · exact PB.fst_ComputesEnc (a := (trVal.fst.1, trVal.fst.2)) (PB.fst_ComputesEnc h_tr)
  · exact PB.snd_ComputesEnc (a := (trVal.fst.1, trVal.fst.2)) (PB.fst_ComputesEnc h_tr)

-- Compute the step function given a transition function (as its graph) and a configuration.
-- Returns `Option Cfg`
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
    exact PB.head_computes (cfg_bitape_computes (h_cfg.extend ext |>.extend _))

def tmMainLoop (tr : PB) (cfg : PB) : PB :=
  -- The accumulator is the current `Cfg`. The body applies `singleTapeTM_step`
  -- (an `Option Cfg`); on `some next` we continue with `next`, on `none` we keep
  -- the current `acc` (which has `state = none`, signalling halt to `while_`).
  PB.while_ cfg
    (fun acc => PB.optionElim (singleTapeTMStep tr acc) acc (fun next => next))

partial def simulateTM
    [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol}
    (cfg : tm.Cfg) :=
  match tm.step cfg with
  | none => cfg
  | some cfg' => simulateTM cfg'

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
      refine PB.optionElim_computesEnc_some (hsc ▸ h_step) ?_
      apply PB.computesFun₂_branch
      intro ext2
      exact PB.var_computes_fresh ext2 [.data (Data.l [])]
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
  apply PB.while_computes h_cfg
  exact loop (Nat.find h_halts) cfg (Nat.find_spec h_halts)

end RoseTreeMachine

end Turing
