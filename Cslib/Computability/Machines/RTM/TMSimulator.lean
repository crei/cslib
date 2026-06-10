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
    {p_tr p_cfg : PB} {cfg : tm.Cfg}
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

def tm_main_loop (tr : PB) (cfg : PB) : PB :=
  -- The accumulator is the current `Cfg`. The body applies `singleTapeTM_step`
  -- (an `Option Cfg`); on `some next` we continue with `next`, on `none` we keep
  -- the current `acc` (which has `state = none`, signalling halt to `while_`).
  PB.while_ cfg
    (fun acc => PB.optionElim (singleTapeTMStep tr acc) acc (fun next => next))

/-- The body of `tm_main_loop` computes one TM step (with `none` halt as fixed point). -/
private lemma tm_main_loop_body_computes [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_tr : PB}
    (h_tr : p_tr.ComputesEnc env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (c : tm.Cfg) :
    PB.computes_at_body₁ env (DataEncode.encode c)
      (fun acc => PB.optionElim (singleTapeTM_step p_tr acc) acc (fun next => next))
      (DataEncode.encode ((tm.step c).getD c)) := by
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with step_def
  intro ext
  set E := env ++ ext with E_def
  have hE_len : E.length = env.length + ext.length := by simp [E_def]
  have h_acc : PB.ComputesEnc (E ++ [DataEncode.encode c])
      (PB.atSlot E.length) c := by
    simpa using PB.atSlot_last_computes_enc (env := E) (ext := []) (a := c)
  have h_step_eval :
      (singleTapeTM_step p_tr (PB.atSlot E.length)).ComputesEnc
        (E ++ [DataEncode.encode c]) (tm.step c) := by
    have h_tr_ext : PB.ComputesEnc (E ++ [DataEncode.encode c]) p_tr
        ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))) := by
      have := h_tr.extend (ext := ext ++ [DataEncode.encode c])
      simpa [E_def, List.append_assoc] using this
    exact singleTapeTM_step_computes h_tr_ext h_acc
  change PB.computes_at (E ++ [DataEncode.encode c])
    (PB.optionElim (singleTapeTM_step p_tr (PB.atSlot (env.length + ext.length)))
      (PB.atSlot (env.length + ext.length))
      (fun next => next)) (DataEncode.encode (step c))
  rw [← hE_len]
  cases hstep_c : tm.step c with
  | none =>
    rw [show step c = c from by simp only [step_def]; rw [hstep_c]; rfl]
    exact PB.optionElim_computes_none (hstep_c ▸ h_step_eval) h_acc
  | some next =>
    rw [show step c = next from by simp only [step_def]; rw [hstep_c]; rfl]
    refine PB.optionElim_computes_some (hstep_c ▸ h_step_eval) ?_
    intro ext'
    simpa using PB.atSlot_last_computes_enc
      (env := E ++ [DataEncode.encode c]) (ext := ext') (a := next)

/-- Spec for `tm_main_loop`: assuming the TM eventually halts when started from
`cfg` (witnessed by some `n` after which iterating `tm.step` reaches a `none`
state), the loop computes the configuration obtained after the *minimal* such
number of steps. Here `tm.step` is lifted to `tm.Cfg → tm.Cfg` by treating the
halt result `none` as a fixed point via `Option.getD`. -/
lemma tm_main_loop_computes [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_tr p_cfg : PB} {cfg : tm.Cfg}
    (h_tr : p_tr.ComputesEnc env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.ComputesEnc env cfg)
    (h_halts : ∃ n, (((fun c => (tm.step c).getD c)^[n] cfg)).state = none) :
    (tm_main_loop p_tr p_cfg).ComputesEnc env
      ((fun c => (tm.step c).getD c)^[Nat.find h_halts] cfg) := by
  -- Lift `tm.step` to a total `tm.Cfg → tm.Cfg` map.
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with step_def
  -- `headD` of an encoded `Cfg` is empty iff the state is `none`.
  have headD_iff : ∀ c : tm.Cfg,
      (DataEncode.encode c).asList.headD (Data.l []) = Data.l [] ↔ c.state = none := by
    rintro ⟨s, t⟩; cases s <;> simp [DataEncode.encode, DataEncode_pair, Data.asList]
  -- Translate the halting hypothesis through the iff.
  have h_halts' : ∃ n, (DataEncode.encode (step^[n] cfg)).asList.headD (Data.l []) = Data.l [] :=
    h_halts.imp fun _ h => (headD_iff _).mpr h
  have find_eq : Nat.find h_halts' = Nat.find h_halts :=
    le_antisymm
      (Nat.find_le ((headD_iff _).mpr (Nat.find_spec h_halts)))
      (Nat.find_le ((headD_iff _).mp (Nat.find_spec h_halts')))
  -- Reduce to a `while_` spec call.
  change PB.computes_at env (tm_main_loop p_tr p_cfg)
    (DataEncode.encode (step^[Nat.find h_halts] cfg))
  rw [← find_eq]
  unfold tm_main_loop
  exact PB.while_computes_iter (env := env) (p_init := p_cfg)
    (body := fun acc => PB.optionElim (singleTapeTM_step p_tr acc) acc (fun next => next))
    step cfg h_cfg (tm_main_loop_body_computes h_tr) h_halts'

def reverse (x : PB) : PB :=
  PB.fold (fun acc el => PB.cons el acc) PB.empty x

lemma reverse_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List α}
    (h : p.ComputesEnc env l) :
    (reverse p).ComputesEnc env l.reverse := by
  unfold reverse
  have h_fold : l.reverse = l.foldl (fun acc el => el :: acc) [] := by simp
  rw [h_fold]
  apply PB.fold_computes_enc (by simp [PB.ComputesEnc]) h
  -- TODO at this point, we should actually be able to just apply a combinator on the semantics
  -- of PB.cons
  intro acc el ext
  have h_el : PB.computes_at
      (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el])
      (PB.atSlot (env.length + ext.length + 1)) (DataEncode.encode el) := by
    simpa using (PB.atSlot_last_computes (ext := ext ++ [DataEncode.encode acc])).extend
  simpa [DataEncode.encode, Data.asList] using
    PB.cons_computes h_el (by simpa using PB.atSlot_last_computes.extend)

def list_map (x : PB) (f : PB → PB) : PB :=
  reverse (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty x)

lemma list_map_computes {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {p : PB} {l : List α}
    {f : PB → PB} {g : α → β}
    (h : p.ComputesEnc env l)
    (hf : ∀ x : α, PB.computes_at_body₁_encoded env x f (g x)) :
    (list_map p f).ComputesEnc env (l.map g) := by
  unfold list_map
  -- TODO simplify proof
  have h_fold : (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty p).ComputesEnc
      env (l.foldl (fun acc el => g el :: acc) []) := by
    apply PB.fold_computes_enc (a := ([] : List β)) (f := fun acc el => g el :: acc)
      (by simp [PB.ComputesEnc, DataEncode.encode]) h
    intro acc el ext
    have h_acc : PB.computes_at
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el])
        (PB.atSlot (env.length + ext.length)) (DataEncode.encode acc) := by
      simpa using (PB.atSlot_last_computes (env := env) (ext := ext)
        (d := DataEncode.encode acc)).extend (ext := [DataEncode.encode el])
    have h_fel : (f (PB.atSlot (env.length + ext.length + 1))).ComputesEnc
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) (g el) := by
      simpa [List.append_assoc] using hf el (ext ++ [DataEncode.encode acc])
    simpa [DataEncode.encode, Data.asList] using PB.cons_computes h_fel h_acc
  have h_rev := reverse_computes h_fold
  have h_eq : (l.foldl (fun acc el => g el :: acc) []).reverse = l.map g := by
    rw [show l.foldl (fun acc el => g el :: acc) []
          = (l.map g).foldl (fun acc el => el :: acc) [] from
        (List.foldl_map (f := g) (g := fun acc el => el :: acc) (l := l) (init := [])).symm]
    simp
  rwa [h_eq] at h_rev

/-- Discards the `none` elements of a list of options, keeping the `some` payloads. -/
def list_reduceOption (x : PB) : PB :=
  reverse (PB.fold
    (fun acc el => PB.optionElim el acc (fun y => PB.cons y acc))
    PB.empty x)

lemma list_reduceOption_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List (Option α)}
    (h : p.ComputesEnc env l) :
    (list_reduceOption p).ComputesEnc env l.reduceOption := by
  unfold list_reduceOption
  set step : List α → Option α → List α :=
    fun acc el => match el with | none => acc | some y => y :: acc with step_def
  -- Convert `reduceOption` to the foldl form of `step` (with reversed accumulator). We need
  -- this generalized over the initial accumulator so the induction goes through.
  have h_eq : ∀ (xs : List (Option α)) (init : List α),
      (xs.foldl step init).reverse = init.reverse ++ xs.reduceOption := by
    intro xs
    induction xs with
    | nil => intro init; simp [List.reduceOption]
    | cons hd tl ih =>
      intro init
      cases hd with
      | none => simpa [step_def] using ih init
      | some y =>
        have h1 : List.foldl step init (some y :: tl) = List.foldl step (y :: init) tl := by
          simp [step_def]
        rw [h1, ih (y :: init)]
        simp [List.reduceOption]
  have h_fold : (PB.fold
        (fun acc el => PB.optionElim el acc (fun y => PB.cons y acc)) PB.empty p
      ).ComputesEnc env (l.foldl step []) := by
    apply PB.fold_computes_enc
      (a := ([] : List α)) (f := step)
      (by simp [PB.ComputesEnc, DataEncode.encode]) h
    intro acc el ext
    have h_el : (PB.atSlot (env.length + ext.length + 1)).ComputesEnc
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) el := by
      simpa [PB.ComputesEnc] using
        (PB.atSlot_last_computes (ext := ext ++ [DataEncode.encode acc])).extend
    have h_acc : (PB.atSlot (env.length + ext.length)).ComputesEnc
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) acc := by
      simpa [PB.ComputesEnc] using
        (PB.atSlot_last_computes (env := env) (ext := ext)
          (d := DataEncode.encode acc)).extend (ext := [DataEncode.encode el])
    cases el with
    | none =>
      simpa [step_def] using
        PB.optionElim_computes_none (α := α) h_el h_acc
    | some y =>
      refine PB.optionElim_computes_some (α := α) h_el ?_
      intro ext'
      -- Inside someCase, the bound `y` lives at slot
      -- `env.length + ext.length + 2 + ext'.length`; `acc` is still at `env.length + ext.length`.
      set ext_inner :=
        ext ++ [DataEncode.encode acc, DataEncode.encode (some y)] ++ ext' with ext_inner_def
      have hlen : ext_inner.length = ext.length + 2 + ext'.length := by
        simp [ext_inner_def, Nat.add_comm, Nat.add_left_comm]
      have h_y :
          PB.computes_at (env ++ ext_inner ++ [DataEncode.encode y])
            (PB.atSlot (env.length + ext.length + 2 + ext'.length))
            (DataEncode.encode y) := by
        have h := PB.atSlot_last_computes
          (env := env) (ext := ext_inner) (d := DataEncode.encode y)
        rw [hlen] at h
        convert h using 2
        omega
      have h_acc' :
          PB.computes_at (env ++ ext_inner ++ [DataEncode.encode y])
            (PB.atSlot (env.length + ext.length)) (DataEncode.encode acc) := by
        have h := (h_acc :
          PB.computes_at (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode (some y)])
            _ (DataEncode.encode acc)).extend (ext := ext' ++ [DataEncode.encode y])
        simpa [ext_inner_def, List.append_assoc] using h
      have h_cons := PB.cons_computes h_y h_acc'
      simp only [ext_inner_def] at h_cons
      simpa [step_def, DataEncode.encode, Data.asList, List.append_assoc] using h_cons
  have h_rev := reverse_computes h_fold
  have h_eq₀ : (l.foldl step []).reverse = l.reduceOption := by simpa using h_eq l []
  rwa [h_eq₀] at h_rev

def list_head_option (input : PB) : PB :=
  PB.elim input PB.empty (fun hd _tl => PB.some hd)

lemma list_head_option_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List α}
    (h : p.ComputesEnc env l) :
    (list_head_option p).ComputesEnc env l.head? := by
  cases l with
  | nil =>
    apply PB.elim_nil_computes (em := PB.empty)
    · simpa [DataEncode.encode] using h
    · simp [DataEncode.encode]
  | cons hd tl =>
    apply PB.elim_cons_computes (head := DataEncode.encode hd)
      (tail := tl.map DataEncode.encode)
    · simpa [DataEncode.encode] using h
    · intro ext
      simpa [DataEncode.encode] using
        PB.cons_computes PB.elim_cons_head_var_computes PB.empty_computes

def string_to_tape (input : PB) : PB :=
  to_pair (list_head_option input) (to_pair .empty (list_map input.tail PB.some))

lemma string_to_tape_computes {env : List Data} {p_input : PB} {input : List Symbol}
    (h_input : p_input.ComputesEnc env input) :
    (string_to_tape p_input).ComputesEnc env (BiTape.mk₁ input) := by
  have h_tail : (PB.tail p_input).ComputesEnc env input.tail := by
    simpa [PB.ComputesEnc, DataEncode.encode] using PB.tail_computes h_input
  have h_map : (list_map (PB.tail p_input) PB.some).ComputesEnc env
      (StackTape.map_some input.tail : Turing.StackTape Symbol) := by
    simpa [PB.ComputesEnc, DataEncode.encode]
      using list_map_computes h_tail (fun _ _ => by
        simpa [DataEncode.encode] using
          PB.cons_computes PB.atSlot_last_computes PB.empty_computes)
  have h_empty : (PB.empty : PB).ComputesEnc env (∅ : Turing.StackTape Symbol) := by
    simp [PB.ComputesEnc, DataEncode.encode]
  simpa [PB.ComputesEnc, encode_biTape, BiTape.mk₁, DataEncode_pair, string_to_tape]
    using to_pair_computes (list_head_option_computes h_input)
      (to_pair_computes h_empty h_map)


def initial_config (q₀ : PB) (input : PB) : PB :=
  to_pair (PB.some q₀) (string_to_tape input)

/-- Turn the final config to an output, by taking the head and the right part of the tape
    and discarding the blank (`none`) cells. -/
def final_config_to_output (cfg : PB) : PB :=
  list_reduceOption (PB.cons (bitapeHead cfg.snd) (bitapeRight cfg.snd))

/-- Implements a universal Single-Tape TM, assuming that the input contains the following:
((initialState, transitionFunction), input).
If it terminates, the output is the tape contents under the head and to its right. -/
def universal_tm (input : PB) :=
  final_config_to_output
    (tm_main_loop input.fst.snd (initial_config input.fst.fst input.snd))

lemma initial_config_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p_q₀ p_input : PB} {input : List Symbol}
    (h_q₀ : p_q₀.ComputesEnc env tm.q₀)
    (h_input : p_input.ComputesEnc env input) :
    (initial_config p_q₀ p_input).ComputesEnc env (tm.initCfg input) := by
  -- `tm.initCfg input = ⟨some tm.q₀, BiTape.mk₁ input⟩`, and `encode` on `Cfg` goes
  -- through the `(state, BiTape)` pair, so this matches `to_pair`.
  exact to_pair_computes (PB.some_computes_enc h_q₀) (string_to_tape_computes h_input)

lemma final_config_to_output_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p_cfg : PB} {cfg : tm.Cfg}
    (h_cfg : p_cfg.ComputesEnc env cfg) :
    (final_config_to_output p_cfg).ComputesEnc env
      (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption := by
  unfold final_config_to_output
  have h_BiTape : (p_cfg.snd).ComputesEnc env cfg.BiTape :=
    PB.snd_computes_enc (a := (cfg.state, cfg.BiTape)) h_cfg
  have h_head := bitape_head_computes h_BiTape
  have h_right := bitape_right_computes h_BiTape
  -- The inner `cons` builds the encoding of `head :: right.toList` (a `List (Option Symbol)`),
  -- then `list_reduceOption` discards the blanks.
  have h_list : (PB.cons (bitape_head p_cfg.snd) (bitape_right p_cfg.snd)).ComputesEnc env
      (cfg.BiTape.head :: cfg.BiTape.right.toList) := by
    change PB.computes_at env _ (DataEncode.encode (cfg.BiTape.head :: cfg.BiTape.right.toList))
    simpa [DataEncode.encode, Data.asList] using PB.cons_computes h_head h_right
  exact list_reduceOption_computes h_list

lemma universal_tm_computes [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {input : List Symbol}
    (h_input : p_input.ComputesEnc env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       input))
    (h_halts : ∃ n,
        ((fun c => (tm.step c).getD c)^[n] (tm.initCfg input)).state = none) :
    (universal_tm p_input).ComputesEnc env
      (let cfg := (fun c => (tm.step c).getD c)^[Nat.find h_halts] (tm.initCfg input)
       (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption) := by
  unfold universal_tm
  have h_fst := PB.fst_computes_enc h_input
  have h_q₀ := PB.fst_computes_enc h_fst
  have h_tr := PB.snd_computes_enc h_fst
  have h_inp := PB.snd_computes_enc h_input
  exact final_config_to_output_computes
    (tm_main_loop_computes h_tr (initial_config_computes h_q₀ h_inp) h_halts)

/-- The output of reading the tape from `BiTape.mk₁ l` (head + right, then discarding
blanks) recovers `l`. -/
private lemma reduceOption_mk₁_tape {Symbol : Type} (l : List Symbol) :
    ((BiTape.mk₁ l).head :: (BiTape.mk₁ l).right.toList).reduceOption = l := by
  have h : ∀ xs : List Symbol, (xs.map Option.some).reduceOption = xs := fun xs => by
    induction xs with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  cases l <;> simp [BiTape.mk₁, Turing.StackTape.map_some_toList, h]

/-- For a `SingleTapeTM` `tm` and any input `w`, if `tm` outputs `w'` on input `w`,
then the universal Turing machine `universal_tm`, when given an encoding of `tm`
together with `w`, computes `w'`.

The encoded input has the shape `((tm.q₀, transitionTable), w)`, where
`transitionTable` enumerates `tm.tr` over all `(state, head symbol)` pairs. -/
theorem universal_tm_simulates [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {w w' : List Symbol}
    (h_input : p_input.ComputesEnc env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w))
    (h_out : tm.Outputs w w') :
    (universal_tm p_input).ComputesEnc env w' := by
  -- Lift `tm.step` to a total step function; halting states are fixed points.
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with hstep
  have halt_fix : ∀ {c : tm.Cfg}, c.state = none → step c = c := by
    rintro ⟨_, _⟩ rfl; rfl
  have halt_fix_iter : ∀ (k : ℕ) {c : tm.Cfg}, c.state = none → step^[k] c = c := by
    intro k _ hc
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, halt_fix hc]
  -- Convert `ReflTransGen` into an explicit step count via tail-induction.
  obtain ⟨n, hn⟩ : ∃ n, step^[n] (tm.initCfg w) = tm.haltCfg w' := by
    suffices h : ∀ {c c' : tm.Cfg}, Relation.ReflTransGen tm.TransitionRelation c c' →
        ∃ n, step^[n] c = c' from h h_out
    intro c c' hrel
    induction hrel with
    | refl => exact ⟨0, rfl⟩
    | tail _ h' ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply', hn]
      change (tm.step _).getD _ = _
      rw [h']
      rfl
  -- The halting hypothesis required by `universal_tm_computes`.
  have h_halts : ∃ k, (step^[k] (tm.initCfg w)).state = none := ⟨n, by rw [hn]; rfl⟩
  -- Determinism + stationarity: `Nat.find` of the halt index also reaches `haltCfg w'`.
  have h_find : step^[Nat.find h_halts] (tm.initCfg w) = tm.haltCfg w' := by
    have h_le : Nat.find h_halts ≤ n := Nat.find_le (by rw [hn]; rfl)
    have h_iter := halt_fix_iter (n - Nat.find h_halts) (Nat.find_spec h_halts)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h_le, hn] at h_iter
    exact h_iter.symm
  -- Conclude via `universal_tm_computes`.
  have h := universal_tm_computes (tm := tm) h_input h_halts
  rw [show ((fun c => (tm.step c).getD c)^[Nat.find h_halts] (tm.initCfg w)) =
    tm.haltCfg w' from h_find] at h
  simpa [SingleTapeTM.haltCfg, reduceOption_mk₁_tape] using h

/-- Bubble-down for `universal_tm`: if `universal_tm p_input` produces some encoded
output at `env`, then the inner `tm_main_loop` also produces some value at `env`. -/
private lemma universal_tm_eval_some_imp_loop_eval_some
    {p_input : PB} {env : List Data} {d : Data}
    (h : (universal_tm p_input env.length).eval env = .some d) :
    ∃ d', (tm_main_loop p_input.fst.snd
      (initial_config p_input.fst.fst p_input.snd) env.length).eval env = .some d' := by
  -- We chase `.some` through every `Part.bind` in the call chain. Each `bind` is
  -- introduced by a `Prog` constructor in `meteredEval`; if the outer eval is
  -- `.some`, the bound subexpression must be `.some` too.
  set n := env.length with hn
  set mloop : Prog := tm_main_loop p_input.fst.snd
    (initial_config p_input.fst.fst p_input.snd) n with mloop_def
  -- Bubble through `cons`: if `Prog.cons a b` evals to some, both subterms do.
  have bd_cons : ∀ {a b : Prog} {env d},
      (Prog.cons a b).eval env = .some d →
      (∃ da, a.eval env = .some da) ∧ (∃ db, b.eval env = .some db) := by
    intro a b env d h
    rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff] at h
    obtain ⟨⟨d', _, _⟩, hm, _⟩ := h
    unfold Prog.meteredEval at hm
    simp only [bind, Part.mem_bind_iff] at hm
    obtain ⟨⟨ah, _, _⟩, ha, hrest⟩ := hm
    obtain ⟨⟨bh, _, _⟩, hb, _⟩ := hrest
    refine ⟨⟨ah, ?_⟩, ⟨bh, ?_⟩⟩
    · rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff]; exact ⟨_, ha, rfl⟩
    · rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff]; exact ⟨_, hb, rfl⟩
  -- Bubble through `elim`: if `Prog.elim v em cs` evals to some, then `v` does.
  have bd_elim : ∀ {v em cs : Prog} {env d},
      (Prog.elim v em cs).eval env = .some d → ∃ dv, v.eval env = .some dv := by
    intro v em cs env d h
    rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff] at h
    obtain ⟨⟨d', _, _⟩, hm, _⟩ := h
    unfold Prog.meteredEval at hm
    simp only [bind, Part.mem_bind_iff] at hm
    obtain ⟨⟨ah, _, _⟩, ha, _⟩ := hm
    refine ⟨ah, ?_⟩
    rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff]; exact ⟨_, ha, rfl⟩
  -- Bubble through `fold`: if `Prog.fold body init list` evals to some, then `init`
  -- and `list` do.
  have bd_fold : ∀ {body init list : Prog} {env d},
      (Prog.fold body init list).eval env = .some d →
      (∃ di, init.eval env = .some di) ∧ (∃ dl, list.eval env = .some dl) := by
    intro body init list env d h
    rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff] at h
    obtain ⟨⟨d', _, _⟩, hm, _⟩ := h
    unfold Prog.meteredEval at hm
    simp only [bind, Part.mem_bind_iff] at hm
    obtain ⟨⟨ah, _, _⟩, ha, hrest⟩ := hm
    obtain ⟨⟨bh, _, _⟩, hb, _⟩ := hrest
    refine ⟨⟨ah, ?_⟩, ⟨bh, ?_⟩⟩
    · rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff]; exact ⟨_, ha, rfl⟩
    · rw [Prog.eval, Part.eq_some_iff, Part.mem_map_iff]; exact ⟨_, hb, rfl⟩
  -- Now unfold `universal_tm = final_config_to_output (...)`,
  -- `final_config_to_output cfg = list_reduceOption (PB.cons (bitape_head cfg.snd) (bitape_right cfg.snd))`,
  -- `list_reduceOption = reverse (PB.fold ...)`, `reverse = PB.fold ...`.
  -- At each step we bubble down through the relevant `Prog` constructor.
  -- `universal_tm p_input` reduces to a `list_reduceOption (...)` whose innermost
  -- list expression depends on `mloop`. Bubble through two `PB.fold`s, then through
  -- `PB.cons`, then through `bitape_head/right` (which are `head`/`tail` chains, i.e. `elim`s)
  -- to extract a `some` evaluation for `mloop`.
  change (final_config_to_output (tm_main_loop p_input.fst.snd
    (initial_config p_input.fst.fst p_input.snd)) n).eval env = .some d at h
  unfold final_config_to_output list_reduceOption reverse at h
  -- Two folds → cons → bitape_head/right (each `head`/`tail`/`fst`/`snd` is `elim` chain)
  obtain ⟨_, ⟨d1, h1⟩⟩ := bd_fold h
  obtain ⟨_, ⟨d2, h2⟩⟩ := bd_fold h1
  -- h2 : (PB.cons (bitape_head mloop'.snd) (bitape_right mloop'.snd)) n .eval env = some d2
  -- where mloop' = tm_main_loop ...
  change (Prog.cons _ _).eval env = .some d2 at h2
  obtain ⟨⟨d3, h3⟩, _⟩ := bd_cons h2
  -- h3 : bitape_head (...).snd evaluates to some
  -- bitape_head t = t.fst = head t = elim t empty (fun ...)
  -- bitape_head (mloop').snd = head (head (tail mloop'))
  change (Prog.elim _ _ _).eval env = .some d3 at h3
  obtain ⟨d4, h4⟩ := bd_elim h3
  -- h4 : (mloop').snd n .eval env = some d4. .snd = head (tail _).
  change (Prog.elim _ _ _).eval env = .some d4 at h4
  obtain ⟨d5, h5⟩ := bd_elim h4
  -- h5 : (tail mloop') n .eval env = some d5. tail = elim _ empty (fun _ tl => tl).
  change (Prog.elim _ _ _).eval env = .some d5 at h5
  obtain ⟨d6, h6⟩ := bd_elim h5
  -- h6 : mloop' n .eval env = some d6. Done.
  exact ⟨d6, h6⟩

/-- Converse of `universal_tm_simulates` (loose form). If `universal_tm`, applied to
a correctly-encoded `((q₀, transitionTable), w)`, evaluates to `w'` under env `env`,
then there exists an iteration index `n` such that the TM is in a halt state and
the tape contents under the head (with blanks discarded) equal `w'`. -/
theorem universal_tm_simulates_converse [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {w w' : List Symbol}
    (h_input : p_input.ComputesEnc env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w))
    (h_out : (universal_tm p_input).ComputesEnc env w') :
    ∃ n : ℕ,
      let cfg := (fun c => (tm.step c).getD c)^[n] (tm.initCfg w)
      cfg.state = none ∧
      (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption = w' := by
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with hstep
  by_cases h_halts : ∃ n, (step^[n] (tm.initCfg w)).state = none
  · -- Halts: use forward direction to identify the output.
    refine ⟨Nat.find h_halts, Nat.find_spec h_halts, ?_⟩
    have h_fwd := universal_tm_computes (tm := tm) h_input h_halts
    -- Both `h_fwd` and `h_out` give an evaluation of `universal_tm p_input` at `env`;
    -- since `Part.eval` is functional, the encoded values must agree, then apply
    -- injectivity of `DataEncode.encode`.
    have h1 := h_fwd []
    have h2 := h_out []
    simp only [List.length_nil, Nat.add_zero, List.append_nil] at h1 h2
    rw [h1] at h2
    have h_eq := Part.some_inj.mp (by exact_mod_cast h2)
    exact DataEncode.h_inj h_eq
  · -- Does not halt: derive a contradiction from `h_out` via `whileFrom_eval_some`.
    exfalso
    have h_eval := h_out []
    simp only [List.length_nil, Nat.add_zero, List.append_nil] at h_eval
    obtain ⟨d, h_loop⟩ := universal_tm_eval_some_imp_loop_eval_some h_eval
    -- Project `h_input` to get individual components.
    have h_q₀ := PB.fst_computes_enc (PB.fst_computes_enc h_input)
    have h_tr := PB.snd_computes_enc (PB.fst_computes_enc h_input)
    have h_inp := PB.snd_computes_enc h_input
    -- Initial config evaluates to `encode (tm.initCfg w)`.
    have h_init_eval : (initial_config p_input.fst.fst p_input.snd env.length).eval env
        = .some (DataEncode.encode (tm.initCfg w)) := by
      have := (initial_config_computes h_q₀ h_inp) []
      simpa using this
    -- Unfold tm_main_loop = PB.while_ init body.
    set body_pb : PB → PB :=
      fun acc => PB.optionElim (singleTapeTM_step p_input.fst.snd acc) acc
        (fun next => next) with body_pb_def
    change (PB.while_ (initial_config p_input.fst.fst p_input.snd) body_pb env.length).eval env
      = .some d at h_loop
    set bd : Prog := body_pb (fun _ => .var env.length) (env.length + 1) with bd_def
    change (Prog.while_ (initial_config p_input.fst.fst p_input.snd env.length) bd).eval env
      = .some d at h_loop
    rw [Prog.while_eval, h_init_eval, Part.bind_some] at h_loop
    -- Extract the trajectory.
    obtain ⟨m, traj, h_traj0, h_trajm, h_halt_at_m, h_steps⟩ :=
      Prog.whileFrom_eval_some h_loop
    -- The body computes `step` at every config.
    have h_body_eval : ∀ c : tm.Cfg,
        bd.eval (env ++ [DataEncode.encode c]) = .some (DataEncode.encode (step c)) := by
      intro c
      have h := (tm_main_loop_body_computes h_tr c (ext := [])).here
      simpa [bd_def, body_pb_def, PB.atSlot, hstep] using h
    -- Induction: `traj k = encode (step^[k] (tm.initCfg w))` for `k ≤ m`.
    have h_traj_eq : ∀ k, k ≤ m → traj k = DataEncode.encode (step^[k] (tm.initCfg w)) := by
      intro k hk
      induction k with
      | zero => simpa using h_traj0
      | succ k ih =>
        have hkm : k < m := hk
        have ih' := ih (Nat.le_of_lt hkm)
        have h_step_k := (h_steps k hkm).2
        rw [ih', h_body_eval] at h_step_k
        have h_eq : traj (k + 1) = DataEncode.encode (step (step^[k] (tm.initCfg w))) :=
          (Part.some_inj.mp h_step_k).symm
        rw [h_eq, show step (step^[k] (tm.initCfg w)) = step^[k+1] (tm.initCfg w) from
          (Function.iterate_succ_apply' step k _).symm]
    -- Halt condition at `m` gives `state = none`.
    have h_at_m : traj m = DataEncode.encode (step^[m] (tm.initCfg w)) := h_traj_eq m le_rfl
    rw [← h_trajm, h_at_m] at h_halt_at_m
    have headD_iff : ∀ c : tm.Cfg,
        (DataEncode.encode c).asList.headD (Data.l []) = Data.l [] ↔ c.state = none := by
      rintro ⟨s, t⟩; cases s <;> simp [DataEncode.encode, DataEncode_pair, Data.asList]
    exact h_halts ⟨m, (headD_iff _).mp h_halt_at_m⟩

/-- Local alternative output predicate: `tm` (lifted to a total step function) reaches
a halted configuration whose tape content (head followed by the right stack, with
blanks discarded) equals `w'`. Used to phrase the combined `iff` characterization
of `universal_tm`. -/
private def Outputs' {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : SingleTapeTM Symbol) (w w' : List Symbol) : Prop :=
  ∃ n : ℕ,
    let cfg := (fun c => (tm.step c).getD c)^[n] (tm.initCfg w)
    cfg.state = none ∧
    (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption = w'

private theorem universal_tm_simulates_iff [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {w w' : List Symbol}
    (h_input : p_input.ComputesEnc env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w)) :
    Outputs' tm w w' ↔ (universal_tm p_input).ComputesEnc env w' := by
  set step : tm.Cfg → tm.Cfg := fun c => (tm.step c).getD c with hstep_def
  have halt_fix : ∀ {c : tm.Cfg}, c.state = none → step c = c := by
    rintro ⟨_, _⟩ rfl; rfl
  have halt_fix_iter : ∀ (k : ℕ) {c : tm.Cfg}, c.state = none → step^[k] c = c := by
    intro k _ hc
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, halt_fix hc]
  refine ⟨?_, ?_⟩
  · -- Forward: `Outputs' tm w w' → universal_tm computes w'`.
    rintro ⟨n, h_halt_n, h_eq⟩
    have h_halts : ∃ k, (step^[k] (tm.initCfg w)).state = none := ⟨n, h_halt_n⟩
    have h := universal_tm_computes (tm := tm) h_input h_halts
    -- Stationarity: any later iterate of a halted config equals it.
    have h_le : Nat.find h_halts ≤ n := Nat.find_le h_halt_n
    have h_iter := halt_fix_iter (n - Nat.find h_halts) (Nat.find_spec h_halts)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h_le] at h_iter
    rw [show ((fun c => (tm.step c).getD c)^[Nat.find h_halts] (tm.initCfg w)) =
      (fun c => (tm.step c).getD c)^[n] (tm.initCfg w) from h_iter.symm, h_eq] at h
    exact h
  · -- Converse: directly from `universal_tm_simulates_converse`.
    intro h_out
    exact universal_tm_simulates_converse h_input h_out


end RoseTreeMachine

end Turing
