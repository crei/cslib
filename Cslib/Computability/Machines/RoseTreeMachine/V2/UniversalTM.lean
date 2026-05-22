/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V2.Tools
public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.List.ReduceOption

/-! # RoseTreeMachine V2 — UniversalTM

Part of the RoseTreeMachine V2 development; see
`Cslib/Computability/Machines/RoseTreeMachine/V2.lean` for an overview.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

variable [Inhabited Symbol] [Fintype Symbol] [DataEncode Symbol]

public instance : DataEncode (Turing.StackTape Symbol) where
  encode t := DataEncode.encode t.toList
  h_inj := by
    intro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h
    have : l₁ = l₂ := DataEncode.h_inj h
    cases this; rfl

public instance : DataEncode (Turing.BiTape Symbol) where
  encode t := DataEncode.encode (t.head, t.left, t.right)
  h_inj := by
    intro ⟨h₁, l₁, r₁⟩ ⟨h₂, l₂, r₂⟩ h
    have heq := DataEncode.h_inj h
    simp at heq
    obtain ⟨hh, hl, hr⟩ := heq
    cases hh; cases hl; cases hr; rfl

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encode_biTape (t : Turing.BiTape Symbol) :
    DataEncode.encode t = DataEncode.encode (t.head, t.left, t.right) := by
    simp [DataEncode.encode]

def bitape_write (t v : PB) : PB := PB.cons v t.tail

lemma bitape_write_computes
    {env : List Data} {p_t p_v : PB} {t : BiTape Symbol} {v : Option Symbol}
    (h_t : PB.computes_at_encoded env p_t t)
    (h_v : PB.computes_at_encoded env p_v v) :
    PB.computes_at_encoded env (bitape_write p_t p_v) (t.write v) := by
  simp only [PB.computes_at_encoded, encode_biTape, DataEncode_pair] at h_t h_v ⊢
  apply PB.cons_computes_at h_v (PB.tail_computes_at h_t)

-- /-- Prepend an `Option` to the `StackTape` -/
-- @[scoped grind]
-- def cons (x : Option Symbol) (xs : StackTape Symbol) : StackTape Symbol :=
--   match x, xs with
--   | none, ⟨[], _⟩ => ⟨[], by grind⟩
--   | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
--   | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩

def stackTape_cons (x st : PB) : PB :=
  PB.optionElim x
    (PB.elim st
      PB.empty
      (fun _ _ => PB.cons x st))
    (fun _ => PB.cons x st)

omit [Inhabited Symbol] [Fintype Symbol] in
lemma stackTape_cons_computes
    {env : List Data} {p_x p_st : PB} {x : Option Symbol} {st : StackTape Symbol}
    (h_x : PB.computes_at_encoded env p_x x)
    (h_st : PB.computes_at_encoded env p_st st) :
    (stackTape_cons p_x p_st).computes_at_encoded env (st.cons x) := by
  cases x with
  | none =>
    apply PB.optionElim_computes_none h_x
    obtain ⟨l, hl⟩ := st
    cases l with
    | nil =>
      simpa [DataEncode.encode] using
        PB.elim_nil_computes_at (by simpa using h_st) (PB.empty_computes_at)
    | cons hd tl =>
      apply PB.elim_cons_computes_at (by simpa [DataEncode.encode] using h_st)
      intro ext
      simpa using (PB.cons_computes_at h_x h_st).extend
  | some a =>
    apply PB.optionElim_computes_some h_x
    intro ext
    simpa using (PB.cons_computes_at (by simpa [DataEncode.encode] using h_x) h_st).extend

def to_pair (a b : PB) : PB := PB.cons a (PB.cons b PB.empty)

lemma to_pair_computes {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {p_a p_b : PB}
    {a : α} {b : β}
    (h_a : p_a.computes_at_encoded env a)
    (h_b : p_b.computes_at_encoded env b) :
    (to_pair p_a p_b).computes_at_encoded env (a, b) := by
  simpa [DataEncode.encode, to_pair] using
    PB.cons_computes_at h_a (PB.cons_computes_at h_b PB.empty_computes_at)

--- The head component of the bitape
def bitape_head (t : PB) : PB := t.fst
--- The left component of the bitape
def bitape_left (t : PB) : PB := t.snd.fst
--- The right component of the bitape
def bitape_right (t : PB) : PB := t.snd.snd

omit [Inhabited Symbol] [Fintype Symbol]
lemma bitape_head_computes {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    (bitape_head p_t).computes_at_encoded env t.head := PB.head_computes_at h_t

omit [Inhabited Symbol] [Fintype Symbol]
lemma bitape_left_computes {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    (bitape_left p_t).computes_at_encoded env t.left :=
  PB.head_computes_at (PB.head_computes_at (PB.tail_computes_at h_t))

omit [Inhabited Symbol] [Fintype Symbol]
lemma bitape_right_computes {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    (bitape_right p_t).computes_at_encoded env t.right :=
  PB.head_computes_at (PB.tail_computes_at (PB.head_computes_at (PB.tail_computes_at h_t)))

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encode_stackTape_head (st : StackTape Symbol) :
    (DataEncode.encode st).asList.headD (Data.l []) = DataEncode.encode st.head := by
  obtain ⟨l, hl⟩ := st
  cases l <;> simp [DataEncode.encode, StackTape.head, Data.asList]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma encode_stackTape_tail (st : StackTape Symbol) :
    Data.l (DataEncode.encode st).asList.tail = DataEncode.encode st.tail := by
  obtain ⟨l, hl⟩ := st
  cases l <;> simp [DataEncode.encode, StackTape.tail, Data.asList]

omit [Inhabited Symbol] [Fintype Symbol] in
lemma stackTape_head_computes_at_encoded {env : List Data} {p_st : PB} {st : StackTape Symbol}
    (h_st : PB.computes_at_encoded env p_st st) :
    (p_st.head).computes_at_encoded env st.head := by
  unfold PB.computes_at_encoded
  simpa [← encode_stackTape_head] using PB.head_computes_at h_st

omit [Inhabited Symbol] [Fintype Symbol] in
lemma stackTape_tail_computes_at_encoded {env : List Data} {p_st : PB} {st : StackTape Symbol}
    (h_st : PB.computes_at_encoded env p_st st) :
    (p_st.tail).computes_at_encoded env st.tail := by
  unfold PB.computes_at_encoded
  simpa [← encode_stackTape_tail] using PB.tail_computes_at h_st

-- def move_left (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

def bitape_move_left (t : PB) : PB :=
  to_pair (bitape_left t).head
    (to_pair
      (bitape_left t).tail
      (stackTape_cons (bitape_head t) (bitape_right t)))

lemma bitape_move_left_computes
    {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    PB.computes_at_encoded env (bitape_move_left p_t) t.move_left := by
  unfold PB.computes_at_encoded
  rw [encode_biTape]
  exact to_pair_computes
    (stackTape_head_computes_at_encoded (bitape_left_computes h_t))
    (to_pair_computes
      (stackTape_tail_computes_at_encoded (bitape_left_computes h_t))
      (stackTape_cons_computes (bitape_head_computes h_t) (bitape_right_computes h_t)))

-- def move_right (t : BiTape Symbol) : BiTape Symbol :=
--   ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

def bitape_move_right (t : PB) : PB :=
  to_pair (bitape_right t).head
    (to_pair
      (stackTape_cons (bitape_head t) (bitape_left t))
      (bitape_right t).tail)

lemma bitape_move_right_computes
    {env : List Data} {p_t : PB} {t : BiTape Symbol}
    (h_t : PB.computes_at_encoded env p_t t) :
    PB.computes_at_encoded env (bitape_move_right p_t) t.move_right := by
  unfold PB.computes_at_encoded
  rw [encode_biTape]
  exact to_pair_computes
    (stackTape_head_computes_at_encoded (bitape_right_computes h_t))
    (to_pair_computes
      (stackTape_cons_computes (bitape_head_computes h_t) (bitape_left_computes h_t))
      (stackTape_tail_computes_at_encoded (bitape_right_computes h_t)))

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

def bitape_move (tape dir : PB) : PB :=
  PB.ifEq dir (constant (DataEncode.encode Dir.left))
    (bitape_move_left tape)
    (bitape_move_right tape)

lemma bitape_move_computes {env : List Data} {p_t p_dir : PB} {t : BiTape Symbol} {d : Dir}
    (h_t : PB.computes_at_encoded env p_t t)
    (h_dir : PB.computes_at_encoded env p_dir d) :
    (bitape_move p_t p_dir).computes_at_encoded env (t.move d) := by
  unfold PB.computes_at_encoded bitape_move
  refine PB.ifEq_computes_at h_dir constant_computes ?_ ?_
  · intro hd_eq
    -- TODO could use injectivity here once we have it.
    cases d with
    | left => exact bitape_move_left_computes h_t
    | right =>
      exfalso
      exact absurd hd_eq (by decide)
  · intro hne
    cases d with
    | left => exact absurd rfl hne
    | right => exact bitape_move_right_computes h_t

-- /--
-- Optionally perform a `move`, or do nothing if `none`.
-- -/
-- def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
--   | t, none => t
--   | t, some d => t.move d

def bitape_optionMove (t dir : PB) : PB :=
  PB.optionElim dir
    t
    (fun d => bitape_move t d)

lemma bitape_optionMove_computes {env : List Data} {p_t p_dir : PB}
    {t : BiTape Symbol} {d : Option Dir}
    (h_t : PB.computes_at_encoded env p_t t)
    (h_dir : PB.computes_at_encoded env p_dir d) :
    (bitape_optionMove p_t p_dir).computes_at_encoded env (t.optionMove d) := by
  unfold PB.computes_at_encoded bitape_optionMove BiTape.optionMove
  match d with
  | none => simpa using PB.optionElim_computes_none h_dir h_t
  | some d =>
    apply PB.optionElim_computes_some h_dir
    intro ext
    exact bitape_move_computes (by simpa using h_t.extend) (by simp)

instance (tm : SingleTapeTM Symbol) [DataEncode tm.State] :
    DataEncode (Turing.SingleTapeTM.Cfg tm) where
  encode cfg := DataEncode.encode (cfg.state, cfg.BiTape)
  h_inj := by
    intro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ h
    have heq := DataEncode.h_inj h
    simp at heq
    obtain ⟨hs, ht⟩ := heq
    cases hs; cases ht; rfl

-- Evaluate a function `f` at `arg` where the function is given as a graph.
-- Returns `some y` for the first `x` in the graph such that `f x = y` and `none` otherwise.
def eval_fun_graph (graph : PB) (arg : PB) : PB :=
  PB.fold
    (fun acc x =>
      PB.optionElim acc
        (PB.ifEq x.fst arg (PB.some x.snd) PB.empty)
        fun _ => acc)
    PB.empty graph

/-- Semantic spec of `eval_fun_graph`: given an encoded graph (list of
`(α × β)`-pairs) and an encoded argument `a : α`, returns
`(graph.find? (·.1 = a)).map (·.2)`, i.e. `some y` for the first pair `(a, y)`
in the graph, else `none`. -/
lemma eval_fun_graph_computes
    {α β : Type} [DataEncode α] [DataEncode β] [DecidableEq α]
    {env : List Data} {p_graph p_arg : PB}
    {graph : List (α × β)} {a : α}
    (h_graph : p_graph.computes_at_encoded env graph)
    (h_arg : p_arg.computes_at_encoded env a) :
    (eval_fun_graph p_graph p_arg).computes_at_encoded env
      ((graph.find? (fun p => p.1 = a)).map (·.2)) := by
  -- The Lean-level step function for the fold.
  let step : Option β → α × β → Option β :=
    fun acc x => acc.elim (if x.1 = a then some x.2 else none) (fun _ => acc)
  -- Once the accumulator is `some _`, it stays `some _`.
  have stays : ∀ (l : List (α × β)) (b : β), l.foldl step (some b) = some b := by
    intro l b
    induction l with
    | nil => simp
    | cons hd tl ih => simp [step, ih]
  -- `foldl step none` matches `find?`-then-`map snd`.
  have key : ∀ l : List (α × β),
      l.foldl step none = (l.find? (fun p => p.1 = a)).map (·.2) := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldl_cons, List.find?_cons]
      by_cases h : hd.1 = a
      · simp [step, h, stays]
      · simp [step, h, ih]
  rw [show (graph.find? (fun p => p.1 = a)).map (·.2)
        = graph.foldl step none from (key graph).symm]
  unfold eval_fun_graph
  refine PB.fold_computes_at_encoded (a := (none : Option β)) (f := step)
    (by simp [PB.computes_at_encoded, DataEncode.encode]) h_graph ?_
  intro acc x ext
  rcases acc with _ | v
  · -- acc = none: step none x = if x.1 = a then some x.2 else none
    refine PB.optionElim_computes_none (α := β)
      PB.elim_cons_head_var_computes_at ?_
    refine PB.ifEq_computes_at
      (PB.fst_computes_at_encoded PB.elim_cons_tail_var_computes_at)
      (by simpa using h_arg.extend) ?_ ?_
    · intro h_enc
      have h_eq : x.1 = a := DataEncode.h_inj h_enc
      change PB.computes_at_encoded _ _ (step none x)
      simp only [step, Option.elim_none, if_pos h_eq]
      exact PB.some_computes_at_encoded
        (PB.snd_computes_at_encoded PB.elim_cons_tail_var_computes_at)
    · intro h_enc
      have h_ne : x.1 ≠ a := fun h => h_enc (by rw [h])
      simp [DataEncode.encode, step, h_ne]
  · -- acc = some v: step (some v) x = some v
    refine PB.optionElim_computes_some (α := β)
      (PB.elim_cons_head_var_computes_at
        (head := DataEncode.encode (some v : Option β))) ?_
    intro ext'
    simpa [List.append_assoc, step] using PB.elim_cons_head_var_computes_at.extend

-- def graphOf {α β : Type} [Fintype α] (f : α → β) : List (α × β) :=
--   Fintype.elems.toList.map (fun a => (a, f a))

lemma eval_fun_graph_computes_of_fun
    {α β : Type} [DataEncode α] [DataEncode β] [Fintype α]
    {env : List Data} {p_graph p_arg : PB}
    {a : α}
    {f : α → β}
    (h_graph : p_graph.computes_at_encoded env (Fintype.elems.toList.map (fun a => (a, f a))))
    (h_arg : p_arg.computes_at_encoded env a) :
    (eval_fun_graph p_graph p_arg).head.computes_at_encoded env (f a) := by
  classical
  have heq : ∀ (L : List α), a ∈ L →
      ((L.map (fun a' => (a', f a'))).find?
        (fun p => p.1 = a)).map (·.2) = some (f a) := by
    intro L hmem
    induction L with
    | nil => exact absurd hmem (by simp)
    | cons hd tl ih => grind
  have h := eval_fun_graph_computes h_graph h_arg
  rw [heq _ (Finset.mem_toList.mpr (Fintype.complete a))] at h
  simpa [DataEncode.encode, Data.asList] using PB.head_computes_at h

def cfg_state (cfg : PB) : PB := cfg.fst
def cfg_bitape (cfg : PB) : PB := cfg.snd

lemma cfg_state_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p : PB} {cfg : Turing.SingleTapeTM.Cfg tm}
    (h : p.computes_at_encoded env cfg) :
    (cfg_state p).computes_at_encoded env cfg.state :=
  PB.fst_computes_at_encoded (a := (cfg.state, cfg.BiTape)) h

lemma cfg_bitape_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p : PB} {cfg : Turing.SingleTapeTM.Cfg tm}
    (h : p.computes_at_encoded env cfg) :
    (cfg_bitape p).computes_at_encoded env cfg.BiTape :=
  PB.snd_computes_at_encoded (a := (cfg.state, cfg.BiTape)) h

/-- Evaluate the transition function. Returns `((wr, dir), q')`.
 -- The return value is not wrapped inside an `Option` because the transition
 -- function is assumed to be total. -/
def eval_tr (tr : PB) (q c : PB) : PB :=
  (eval_fun_graph (eval_fun_graph tr q).head c).head

instance : DataEncode (SingleTapeTM.Stmt Symbol) where
  encode stmt := DataEncode.encode (stmt.symbol, stmt.movement)
  h_inj := by
    intro ⟨s₁, m₁⟩ ⟨s₂, m₂⟩ h
    have heq := DataEncode.h_inj h
    simp at heq
    obtain ⟨hs, hm⟩ := heq
    cases hs; cases hm; rfl

lemma eval_tr_computes {State : Type} [Fintype State] [DataEncode State]
    [DecidableEq State] [Fintype Symbol]
    {env : List Data} {p_tr p_q p_c : PB}
    {tr : State → Option Symbol → SingleTapeTM.Stmt Symbol × Option State}
    {q : State}
    {c : Option Symbol}
    (h_tr : p_tr.computes_at_encoded env
      ((Fintype.elems : Finset State).toList.map (fun q' : State =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' : Option Symbol => (c', tr q' c'))))))
    (h_q : p_q.computes_at_encoded env q)
    (h_c : p_c.computes_at_encoded env c) :
    (eval_tr p_tr p_q p_c).computes_at_encoded env (tr q c) := by
  unfold eval_tr
  exact eval_fun_graph_computes_of_fun (α := Option Symbol) (f := tr q)
    (eval_fun_graph_computes_of_fun (α := State) (f := fun q' =>
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

-- Compute the step function given a transition function (as its graph) and a configuration.
-- Returns `Option Cfg`
def singleTapeTM_step (tr : PB) (cfg : PB) : PB :=
  PB.optionElim (cfg_state cfg)
    PB.empty
    (fun q' => PB.letIn (cfg_bitape cfg) (fun tape =>
      PB.letIn (eval_tr tr q' tape.head) (fun tr_val =>
        .some (to_pair
          tr_val.snd
          (bitape_optionMove (bitape_write tape tr_val.fst.fst) tr_val.fst.snd)))))

lemma singleTapeTM_step_computes [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_tr p_cfg : PB} {cfg : tm.Cfg}
    (h_tr : p_tr.computes_at_encoded env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.computes_at_encoded env cfg) :
    (singleTapeTM_step p_tr p_cfg).computes_at_encoded env (tm.step cfg) := by
  unfold singleTapeTM_step
  obtain ⟨state, t⟩ := cfg
  match hst : state with
  | none =>
    refine PB.optionElim_computes_none (cfg_state_computes h_cfg) ?_
    change PB.empty.computes_at_encoded env (none : Option tm.Cfg)
    simp [PB.computes_at_encoded, DataEncode.encode]
  | some q' =>
    refine PB.optionElim_computes_some (cfg_state_computes h_cfg) ?_
    intro ext1
    -- TODO letin makes this proof complicated.
    -- Outer letIn: bind `tape := cfg_bitape p_cfg`, value `t`.
    apply PB.letIn_computes_at_encoded (v := t)
      (by simpa [List.append_assoc] using cfg_bitape_computes h_cfg.extend)
    intro ext2
    set env2 := env ++ ext1 ++ [DataEncode.encode q'] with env2_def
    -- The slot for `q'` at depth `env.length + ext1.length`.
    have h_q'_slot : PB.computes_at_encoded
        (env2 ++ ext2 ++ [DataEncode.encode t])
        (PB.atSlot (env.length + ext1.length)) q' := by
      simpa [env2_def] using PB.atSlot_last_computes_at_encoded.extend
    -- The slot for `tape` at depth `env2.length + ext2.length`.
    have h_tape_slot : PB.computes_at_encoded
        (env2 ++ ext2 ++ [DataEncode.encode t])
        (PB.atSlot (env2.length + ext2.length)) t :=
      PB.atSlot_last_computes_at_encoded
    apply PB.letIn_computes_at_encoded
      (eval_tr_computes
        (by simpa [env2_def, List.append_assoc] using h_tr.extend)
        h_q'_slot (bitape_head_computes h_tape_slot))
    intro ext3
    set env3 := env2 ++ ext2 ++ [DataEncode.encode t] with env3_def
    set envS := env3 ++ ext3 ++ [DataEncode.encode (tm.tr q' t.head)] with envS_def
    -- Re-derive tape slot at envS.
    have h_tape_slot' : PB.computes_at_encoded envS
        (PB.atSlot (env2.length + ext2.length)) t := by
      simpa [envS_def, env3_def, List.append_assoc] using
        h_tape_slot.extend (ext := ext3 ++ [DataEncode.encode (tm.tr q' t.head)])
    -- Destructure the transition result.
    rcases htr_eq : tm.tr q' t.head with ⟨⟨wr, dir⟩, q''⟩
    have h_trval : PB.computes_at_encoded envS
        (PB.atSlot (env3.length + ext3.length))
        (SingleTapeTM.Stmt.mk (Symbol := Symbol) wr dir, q'') := by
      simp [envS_def, htr_eq]
    unfold SingleTapeTM.step
    simp only [htr_eq]
    exact PB.some_computes_at_encoded
      (to_pair_computes
        (PB.snd_computes_at_encoded h_trval)
        (bitape_optionMove_computes
          (bitape_write_computes h_tape_slot'
            (PB.fst_computes_at_encoded (a := (wr, dir))
              (PB.fst_computes_at_encoded h_trval)))
          (PB.snd_computes_at_encoded (a := (wr, dir))
            (PB.fst_computes_at_encoded h_trval))))

def tm_main_loop (tr : PB) (cfg : PB) : PB :=
  -- The accumulator is the current `Cfg`. The body applies `singleTapeTM_step`
  -- (an `Option Cfg`); on `some next` we continue with `next`, on `none` we keep
  -- the current `acc` (which has `state = none`, signalling halt to `while_`).
  PB.while_ cfg
    (fun acc => PB.optionElim (singleTapeTM_step tr acc) acc (fun next => next))

/-- The body of `tm_main_loop` computes one TM step (with `none` halt as fixed point). -/
private lemma tm_main_loop_body_computes [Inhabited Symbol] [Fintype Symbol]
    [DecidableEq Symbol] {tm : SingleTapeTM Symbol}
    [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_tr : PB}
    (h_tr : p_tr.computes_at_encoded env
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
  have h_acc : PB.computes_at_encoded (E ++ [DataEncode.encode c])
      (PB.atSlot E.length) c := by
    simpa using PB.atSlot_last_computes_at_encoded (env := E) (ext := []) (a := c)
  have h_step_eval :
      (singleTapeTM_step p_tr (PB.atSlot E.length)).computes_at_encoded
        (E ++ [DataEncode.encode c]) (tm.step c) := by
    have h_tr_ext : PB.computes_at_encoded (E ++ [DataEncode.encode c]) p_tr
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
    simpa using PB.atSlot_last_computes_at_encoded
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
    (h_tr : p_tr.computes_at_encoded env
      ((Fintype.elems : Finset tm.State).toList.map (fun q' =>
        (q', (Fintype.elems : Finset (Option Symbol)).toList.map
          (fun c' => (c', tm.tr q' c'))))))
    (h_cfg : p_cfg.computes_at_encoded env cfg)
    (h_halts : ∃ n, (((fun c => (tm.step c).getD c)^[n] cfg)).state = none) :
    (tm_main_loop p_tr p_cfg).computes_at_encoded env
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
    (h : p.computes_at_encoded env l) :
    (reverse p).computes_at_encoded env l.reverse := by
  unfold reverse
  have h_fold : l.reverse = l.foldl (fun acc el => el :: acc) [] := by simp
  rw [h_fold]
  apply PB.fold_computes_at_encoded (by simp [PB.computes_at_encoded]) h
  -- TODO at this point, we should actually be able to just apply a combinator on the semantics
  -- of PB.cons
  intro acc el ext
  have h_el : PB.computes_at
      (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el])
      (PB.atSlot (env.length + ext.length + 1)) (DataEncode.encode el) := by
    simpa using (PB.atSlot_last_computes_at (ext := ext ++ [DataEncode.encode acc])).extend
  simpa [DataEncode.encode, Data.asList] using
    PB.cons_computes_at h_el (by simpa using PB.atSlot_last_computes_at.extend)

def list_map (x : PB) (f : PB → PB) : PB :=
  reverse (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty x)

lemma list_map_computes {α β : Type} [DataEncode α] [DataEncode β]
    {env : List Data} {p : PB} {l : List α}
    {f : PB → PB} {g : α → β}
    (h : p.computes_at_encoded env l)
    (hf : ∀ x : α, PB.computes_at_body₁_encoded env x f (g x)) :
    (list_map p f).computes_at_encoded env (l.map g) := by
  unfold list_map
  -- TODO simplify proof
  have h_fold : (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty p).computes_at_encoded
      env (l.foldl (fun acc el => g el :: acc) []) := by
    apply PB.fold_computes_at_encoded (a := ([] : List β)) (f := fun acc el => g el :: acc)
      (by simp [PB.computes_at_encoded, DataEncode.encode]) h
    intro acc el ext
    have h_acc : PB.computes_at
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el])
        (PB.atSlot (env.length + ext.length)) (DataEncode.encode acc) := by
      simpa using (PB.atSlot_last_computes_at (env := env) (ext := ext)
        (d := DataEncode.encode acc)).extend (ext := [DataEncode.encode el])
    have h_fel : (f (PB.atSlot (env.length + ext.length + 1))).computes_at_encoded
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) (g el) := by
      simpa [List.append_assoc] using hf el (ext ++ [DataEncode.encode acc])
    simpa [DataEncode.encode, Data.asList] using PB.cons_computes_at h_fel h_acc
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
    (h : p.computes_at_encoded env l) :
    (list_reduceOption p).computes_at_encoded env l.reduceOption := by
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
      ).computes_at_encoded env (l.foldl step []) := by
    apply PB.fold_computes_at_encoded
      (a := ([] : List α)) (f := step)
      (by simp [PB.computes_at_encoded, DataEncode.encode]) h
    intro acc el ext
    have h_el : (PB.atSlot (env.length + ext.length + 1)).computes_at_encoded
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) el := by
      simpa [PB.computes_at_encoded] using
        (PB.atSlot_last_computes_at (ext := ext ++ [DataEncode.encode acc])).extend
    have h_acc : (PB.atSlot (env.length + ext.length)).computes_at_encoded
        (env ++ ext ++ [DataEncode.encode acc, DataEncode.encode el]) acc := by
      simpa [PB.computes_at_encoded] using
        (PB.atSlot_last_computes_at (env := env) (ext := ext)
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
        have h := PB.atSlot_last_computes_at
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
      have h_cons := PB.cons_computes_at h_y h_acc'
      simp only [ext_inner_def] at h_cons
      simpa [step_def, DataEncode.encode, Data.asList, List.append_assoc] using h_cons
  have h_rev := reverse_computes h_fold
  have h_eq₀ : (l.foldl step []).reverse = l.reduceOption := by simpa using h_eq l []
  rwa [h_eq₀] at h_rev

def list_head_option (input : PB) : PB :=
  PB.elim input PB.empty (fun hd _tl => PB.some hd)

lemma list_head_option_computes {α : Type} [DataEncode α]
    {env : List Data} {p : PB} {l : List α}
    (h : p.computes_at_encoded env l) :
    (list_head_option p).computes_at_encoded env l.head? := by
  cases l with
  | nil =>
    apply PB.elim_nil_computes_at (em := PB.empty)
    · simpa [DataEncode.encode] using h
    · simp [DataEncode.encode]
  | cons hd tl =>
    apply PB.elim_cons_computes_at (head := DataEncode.encode hd)
      (tail := tl.map DataEncode.encode)
    · simpa [DataEncode.encode] using h
    · intro ext
      simpa [DataEncode.encode] using
        PB.cons_computes_at PB.elim_cons_head_var_computes_at PB.empty_computes_at

def string_to_tape (input : PB) : PB :=
  to_pair (list_head_option input) (to_pair .empty (list_map input.tail PB.some))

lemma string_to_tape_computes {env : List Data} {p_input : PB} {input : List Symbol}
    (h_input : p_input.computes_at_encoded env input) :
    (string_to_tape p_input).computes_at_encoded env (BiTape.mk₁ input) := by
  have h_tail : (PB.tail p_input).computes_at_encoded env input.tail := by
    simpa [PB.computes_at_encoded, DataEncode.encode] using PB.tail_computes_at h_input
  have h_map : (list_map (PB.tail p_input) PB.some).computes_at_encoded env
      (StackTape.map_some input.tail : Turing.StackTape Symbol) := by
    simpa [PB.computes_at_encoded, DataEncode.encode]
      using list_map_computes h_tail (fun _ _ => by
        simpa [DataEncode.encode] using
          PB.cons_computes_at PB.atSlot_last_computes_at PB.empty_computes_at)
  have h_empty : (PB.empty : PB).computes_at_encoded env (∅ : Turing.StackTape Symbol) := by
    simp [PB.computes_at_encoded, DataEncode.encode]
  simpa [PB.computes_at_encoded, encode_biTape, BiTape.mk₁, DataEncode_pair, string_to_tape]
    using to_pair_computes (list_head_option_computes h_input)
      (to_pair_computes h_empty h_map)


def initial_config (q₀ : PB) (input : PB) : PB :=
  to_pair (PB.some q₀) (string_to_tape input)

/-- Turn the final config to an output, by taking the head and the right part of the tape
    and discarding the blank (`none`) cells. -/
def final_config_to_output (cfg : PB) : PB :=
  list_reduceOption (PB.cons (bitape_head cfg.snd) (bitape_right cfg.snd))

/-- Implements a universal Single-Tape TM, assuming that the input contains the following:
((initialState, transitionFunction), input).
If it terminates, the output is the tape contents under the head and to its right. -/
def universal_tm (input : PB) :=
  final_config_to_output
    (tm_main_loop input.fst.snd (initial_config input.fst.fst input.snd))

lemma initial_config_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p_q₀ p_input : PB} {input : List Symbol}
    (h_q₀ : p_q₀.computes_at_encoded env tm.q₀)
    (h_input : p_input.computes_at_encoded env input) :
    (initial_config p_q₀ p_input).computes_at_encoded env (tm.initCfg input) := by
  -- `tm.initCfg input = ⟨some tm.q₀, BiTape.mk₁ input⟩`, and `encode` on `Cfg` goes
  -- through the `(state, BiTape)` pair, so this matches `to_pair`.
  exact to_pair_computes (PB.some_computes_at_encoded h_q₀) (string_to_tape_computes h_input)

lemma final_config_to_output_computes [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State]
    {env : List Data} {p_cfg : PB} {cfg : tm.Cfg}
    (h_cfg : p_cfg.computes_at_encoded env cfg) :
    (final_config_to_output p_cfg).computes_at_encoded env
      (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption := by
  unfold final_config_to_output
  have h_BiTape : (p_cfg.snd).computes_at_encoded env cfg.BiTape :=
    PB.snd_computes_at_encoded (a := (cfg.state, cfg.BiTape)) h_cfg
  have h_head := bitape_head_computes h_BiTape
  have h_right := bitape_right_computes h_BiTape
  -- The inner `cons` builds the encoding of `head :: right.toList` (a `List (Option Symbol)`),
  -- then `list_reduceOption` discards the blanks.
  have h_list : (PB.cons (bitape_head p_cfg.snd) (bitape_right p_cfg.snd)).computes_at_encoded env
      (cfg.BiTape.head :: cfg.BiTape.right.toList) := by
    change PB.computes_at env _ (DataEncode.encode (cfg.BiTape.head :: cfg.BiTape.right.toList))
    simpa [DataEncode.encode, Data.asList] using PB.cons_computes_at h_head h_right
  exact list_reduceOption_computes h_list

lemma universal_tm_computes [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    {tm : SingleTapeTM Symbol} [DataEncode tm.State] [DecidableEq tm.State]
    {env : List Data} {p_input : PB} {input : List Symbol}
    (h_input : p_input.computes_at_encoded env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       input))
    (h_halts : ∃ n,
        ((fun c => (tm.step c).getD c)^[n] (tm.initCfg input)).state = none) :
    (universal_tm p_input).computes_at_encoded env
      (let cfg := (fun c => (tm.step c).getD c)^[Nat.find h_halts] (tm.initCfg input)
       (cfg.BiTape.head :: cfg.BiTape.right.toList).reduceOption) := by
  unfold universal_tm
  have h_fst := PB.fst_computes_at_encoded h_input
  have h_q₀ := PB.fst_computes_at_encoded h_fst
  have h_tr := PB.snd_computes_at_encoded h_fst
  have h_inp := PB.snd_computes_at_encoded h_input
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
    (h_input : p_input.computes_at_encoded env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w))
    (h_out : tm.Outputs w w') :
    (universal_tm p_input).computes_at_encoded env w' := by
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
    (h_input : p_input.computes_at_encoded env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w))
    (h_out : (universal_tm p_input).computes_at_encoded env w') :
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
    have h_q₀ := PB.fst_computes_at_encoded (PB.fst_computes_at_encoded h_input)
    have h_tr := PB.snd_computes_at_encoded (PB.fst_computes_at_encoded h_input)
    have h_inp := PB.snd_computes_at_encoded h_input
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
    (h_input : p_input.computes_at_encoded env
      ((tm.q₀,
        (Fintype.elems : Finset tm.State).toList.map (fun q' =>
          (q', (Fintype.elems : Finset (Option Symbol)).toList.map
            (fun c' => (c', tm.tr q' c'))))),
       w)) :
    Outputs' tm w w' ↔ (universal_tm p_input).computes_at_encoded env w' := by
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
