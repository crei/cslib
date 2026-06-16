/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Prog
public import Cslib.Computability.Machines.RTM.DataEncode


@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- Code that computes a value of type `α` (given the current variable depth), bundled with its
semantics.
TODO also bundle resource usage. -/
structure Routine (α : Type) [DataEncode α] where
  /-- The code -/
  impl (depth : ℕ) : Prog
  /-- A condition on the input under which we make a statement about the semantics. -/
  valid : List Value → Prop := fun _ => True
  /-- The computed value together with a proof that the code computes it. -/
  sem (env : List Value) (h : valid env) :
    -- { v : α // ∀ ext : List Value, -- TODO do we need `ext`?
    --   ∃ t s, ProgSem (env ++ ext) (impl (env.length + ext.length))
    --     (.data (DataEncode.encode v)) t s }
    { v : α // ∃ t s, ProgSem env (impl env.length) (.data (DataEncode.encode v)) t s }


namespace Routine

variable {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]

-- TODO If we want `var` to support `Value` as well, we should not require
-- `DataEncode`.

def var (i : ℕ) : Routine α where
  impl _ := Prog.var i
  valid env := ∃ x : α, env[i]? = some (.data (DataEncode.encode x))
  sem env h :=
    let d : Data := match env[i]? with | some (.data d) => d | _ => Data.l []
    have key : ∀ x : α, env[i]? = some (.data (DataEncode.encode x)) → d = DataEncode.encode x :=
      fun x hx => by simp only [d, hx]
    have hsome : (DataEncode.decode d).isSome := by
      obtain ⟨x, hx⟩ := h; rw [key x hx, DataEncode.encodek]; rfl
    ⟨(DataEncode.decode d).get hsome, by
      obtain ⟨x, hx⟩ := h
      have hget : (DataEncode.decode d).get hsome = x :=
        Option.some.inj (by rw [Option.some_get, key x hx, DataEncode.encodek])
      have hv : env[i]?.getD Value.empty = .data (DataEncode.encode x) := by rw [hx]; rfl
      exact ⟨_, _, hget ▸ hv ▸ ProgSem.var⟩⟩

/-- The value computed by `var i` is `x` whenever slot `i` holds the encoding of `x`. -/
lemma var_sem_val {env : List Value} {i : ℕ} {x : α} (h : (var i : Routine α).valid env)
    (hx : env[i]? = some (.data (DataEncode.encode x))) :
    ((var i : Routine α).sem env h).val = x := by
  have hsome : DataEncode.decode (α := α)
      (match env[i]? with | some (.data d) => d | _ => Data.l []) = some x := by
    rw [hx, DataEncode.encodek]
  exact Option.get_of_mem _ hsome

/-- Reading slot `env.length` (the first captured slot) of `env ++ [.data (encode x), y]`
yields `x`. Stated structurally so that `simp` can recover `x` from the environment. -/
@[simp]
lemma var_sem_val_length₂ {env : List Value} {x : α} {y : Value}
    (h : (var env.length : Routine α).valid (env ++ [.data (DataEncode.encode x), y])) :
    ((var env.length : Routine α).sem (env ++ [.data (DataEncode.encode x), y]) h).val = x := by
  apply var_sem_val
  simp

/-- Reading slot `env.length + 1` (the second captured slot) of `env ++ [y, .data (encode x)]`
yields `x`. Stated structurally so that `simp` can recover `x` from the environment. -/
@[simp]
lemma var_sem_val_length_succ {env : List Value} {x : α} {y : Value}
    (h : (var (env.length + 1) : Routine α).valid (env ++ [y, .data (DataEncode.encode x)])) :
    ((var (env.length + 1) : Routine α).sem
      (env ++ [y, .data (DataEncode.encode x)]) h).val = x := by
  apply var_sem_val
  simp


/-- Indexing into the appended part of an environment. -/
lemma getElem?_append_length_add (e xs : List Value) (k : ℕ) :
    (e ++ xs)[e.length + k]? = xs[k]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The element appended at the end of an environment sits at index `e.length`. -/
lemma getElem?_append_singleton (e : List Value) (v : Value) :
    (e ++ [v])[e.length]? = some v := by
  rw [List.getElem?_append_right (le_refl _)]; simp

/-- `var (env.length + k)` is valid in `env ++ xs` when slot `k` of `xs` holds `encode x`. -/
lemma var_valid_add {env : List Value} {x : α} (xs : List Value) (k : ℕ)
    (hk : xs[k]? = some (.data (DataEncode.encode x))) :
    (var (env.length + k) : Routine α).valid (env ++ xs) :=
  ⟨x, by rw [getElem?_append_length_add]; exact hk⟩

/-- The value of `var (env.length + k)` in `env ++ xs` is `x` when slot `k` of `xs` holds
`encode x`. -/
lemma var_sem_val_add {env : List Value} {x : α} (xs : List Value) (k : ℕ)
    (hk : xs[k]? = some (.data (DataEncode.encode x)))
    (h : (var (env.length + k) : Routine α).valid (env ++ xs)) :
    ((var (env.length + k) : Routine α).sem (env ++ xs) h).val = x := by
  apply var_sem_val
  rw [getElem?_append_length_add]
  exact hk

/-- `ComputesFun f g env`: the unary routine-transformer `f` computes the value-function `g`, in
every extension `env ++ extra` of `env` (so `f` may capture `env`). This is the correctness spec a
caller supplies for a `Routine`-valued function argument. -/
def ComputesFun (f : Routine α → Routine β) (g : α → β) (env : List Value) : Prop :=
  ∀ (extra : List Value) (a : Routine α) (ha : a.valid (env ++ extra)),
    ∃ (hf : (f a).valid (env ++ extra)),
      ((f a).sem (env ++ extra) hf).val = g ((a.sem (env ++ extra) ha).val)

/-- `ComputesFun₂ f g env`: the binary routine-transformer `f` computes the value-function `g`, in
every extension `env ++ extra` of `env` (so `f` may capture `env`). -/
def ComputesFun₂ (f : Routine α → Routine β → Routine γ) (g : α → β → γ) (env : List Value) :
    Prop :=
  ∀ (extra : List Value) (a : Routine α) (b : Routine β)
    (ha : a.valid (env ++ extra)) (hb : b.valid (env ++ extra)),
    ∃ (hf : (f a b).valid (env ++ extra)),
      ((f a b).sem (env ++ extra) hf).val
        = g ((a.sem (env ++ extra) ha).val) ((b.sem (env ++ extra) hb).val)

def empty : Routine Data where
  impl _ := Prog.empty
  sem _ _ := ⟨.l [], ⟨_, _, ProgSem.empty⟩⟩

def cons (hd : Routine Data) (tl : Routine Data) : Routine Data where
  impl n := .cons (hd.impl n) (tl.impl n)
  valid env := hd.valid env ∧ tl.valid env
  sem env h :=
    ⟨(.l ((hd.sem env h.left).val :: (tl.sem env h.right).val.asList)), by
      obtain ⟨_, _, h_hd⟩ := (hd.sem env h.left).property
      obtain ⟨_, _, h_tl⟩ := (tl.sem env h.right).property
      exact ⟨_, _, ProgSem.cons h_hd h_tl⟩⟩

def elim (v : Routine Data) (em : Routine Data)
    (cs : Routine Data → Routine Data → Routine Data) : Routine Data where
  impl n := .elim (v.impl n) (em.impl n) (.fn (.fn ((cs (var n) (var (n + 1))).impl (n + 2))))
  valid env := ∃ h : v.valid env, (match (v.sem env h).val with
    | .l [] => em.valid env
    | .l (hd :: tl) => (cs (Routine.var env.length) (Routine.var (env.length + 1))).valid
        (env ++ [.data hd, .data (Data.l tl)]))
  sem env h := match h_v : (v.sem env h.1).val with
    | .l [] =>
      have h_em_valid := by simp [h_v] at h; exact h.right
      ⟨em.sem env h_em_valid,
        by
        obtain ⟨_, _, h_v'⟩ := (v.sem env h.1).property
        rw [h_v] at h_v'
        obtain ⟨_, _, h_em⟩ := (em.sem env h_em_valid).property
        exact ⟨_, _, ProgSem.elim_nil h_v' h_em⟩⟩
    | .l (hd :: tl) =>
      have h_cs_valid := by simp [h_v] at h; exact h.right
      ⟨(cs (Routine.var env.length) (Routine.var (env.length + 1))).sem
        (env ++ [.data hd, .data (Data.l tl)]) h_cs_valid,
        by
        obtain ⟨_, _, h_v'⟩ := (v.sem env h.1).property
        rw [h_v] at h_v'
        obtain ⟨t_cs, s_cs, h_cs⟩ :=
          ((cs (Routine.var env.length) (Routine.var (env.length + 1))).sem
            (env ++ [.data hd, .data (Data.l tl)]) h_cs_valid).property
        exact ⟨_, _, ProgSem.elim_cons h_v' ProgSem.fn ⟨ProgSem.fn⟩ ⟨by
          rw [List.append_assoc]
          rw [show env.length + 2 = (env ++ [_, _]).length from by simp]
          exact h_cs⟩⟩⟩


def ifEq {α β : Type} [DataEncode α] [DecidableEq α] [DataEncode β]
    (x y : Routine α) (then_ else_ : Routine β) : Routine β where
  impl n := .ifEq (x.impl n) (y.impl n) (then_.impl n) (else_.impl n)
  valid env := ∃ (h_x : x.valid env) (h_y : y.valid env),
    (if (x.sem env h_x).val = (y.sem env h_y).val then then_.valid env else else_.valid env)
  sem env h :=
    have h_x : x.valid env := h.elim fun hx _ => hx
    have h_y : y.valid env := h.elim fun _ h' => h'.elim fun hy _ => hy
    have hc : (if (x.sem env h_x).val = (y.sem env h_y).val then then_.valid env
        else else_.valid env) := h.elim fun _ h' => h'.elim fun _ hcond => hcond
    if h_eq : (x.sem env h_x).val = (y.sem env h_y).val then
      have h_then : then_.valid env := by rw [if_pos h_eq] at hc; exact hc
      ⟨(then_.sem env h_then).val, by
        obtain ⟨_, _, h_x'⟩ := (x.sem env h_x).property
        obtain ⟨_, _, h_y'⟩ := (y.sem env h_y).property
        obtain ⟨_, _, h_then'⟩ := (then_.sem env h_then).property
        rw [h_eq] at h_x'
        exact ⟨_, _, ProgSem.ifEq_then h_x' h_y' h_then'⟩⟩
    else
      have h_else : else_.valid env := by rw [if_neg h_eq] at hc; exact hc
      ⟨(else_.sem env h_else).val, by
        obtain ⟨_, _, h_x'⟩ := (x.sem env h_x).property
        obtain ⟨_, _, h_y'⟩ := (y.sem env h_y).property
        obtain ⟨_, _, h_else'⟩ := (else_.sem env h_else).property
        exact ⟨_, _, ProgSem.ifEq_else h_x' h_y'
          (fun hcontra => h_eq (DataEncode.h_inj hcontra)) h_else'⟩⟩

inductive WhileSem (env : List Value) (body : Routine (α × β) → Routine (α × β)) :
    α × β → α × β → Prop
  | halt (a : α) (b : β) (h_encode_empty : DataEncode.encode a = Data.l []) :
    WhileSem env body (a, b) (a, b)
  | step {a : α} {b : β} {r : α × β}
      (h_not_empty : DataEncode.encode a ≠ Data.l [])
      (h_valid : (body (Routine.var env.length)).valid
        (env ++ [.data (DataEncode.encode (a, b))]))
      (h_rest : WhileSem env body
        ((body (Routine.var env.length)).sem
          (env ++ [.data (DataEncode.encode (a, b))]) h_valid).val r) :
      WhileSem env body (a, b) r

lemma WhileSem.toMachine {env : List Value} {body : Routine (α × β) → Routine (α × β)}
    {acc r : α × β} (h : WhileSem env body acc r) :
    ∃ t s, _root_.Turing.RoseTreeMachine.WhileSem
      (.closure ((body (Routine.var env.length)).impl (env.length + 1)) env)
      (DataEncode.encode acc) (DataEncode.encode r) t s := by
  induction h with
  | halt a b h_encode_empty =>
    exact ⟨_, _, .halt (by simp [DataEncode_pair, Data.l_asList, h_encode_empty])⟩
  | @step a b r h_not_empty h_valid h_rest ih =>
    obtain ⟨_, _, h_while⟩ := ih
    obtain ⟨_, _, h_body⟩ := ((body (Routine.var env.length)).sem
      (env ++ [.data (DataEncode.encode (a, b))]) h_valid).property
    exact ⟨_, _, .step (by simpa [DataEncode_pair, Data.l_asList] using h_not_empty)
            (.mk (by simpa using h_body)) h_while⟩

noncomputable def while_ (init : Routine (α × β))
    (body : Routine (α × β) → Routine (α × β)) : Routine (α × β) where
  impl n := .while_ (init.impl n) (.fn ((body (var n)).impl (n + 1)))
  valid env := ∃ (h_init : init.valid env) (r : α × β),
    WhileSem env body (init.sem env h_init).val r
  sem env h :=
    have h_init : init.valid env := h.elim fun hi _ => hi
    have hr : ∃ r : α × β, WhileSem env body (init.sem env h_init).val r :=
      h.elim fun _ h' => h'
    ⟨Classical.choose hr, by
      obtain ⟨_, _, h_init'⟩ := (init.sem env h_init).property
      obtain ⟨_, _, h_while⟩ := (Classical.choose_spec hr).toMachine
      exact ⟨_, _, ProgSem.while_ h_init' ProgSem.fn h_while⟩⟩

/-- `WhileSem` is deterministic: a starting state reaches at most one final state. -/
lemma WhileSem.det {env : List Value} {body : Routine (α × β) → Routine (α × β)}
    {p r r' : α × β} (h : WhileSem env body p r) (h' : WhileSem env body p r') : r = r' := by
  induction h generalizing r' with
  | halt a b h_enc =>
    cases h' with
    | halt => rfl
    | step h_ne _ _ => exact absurd h_enc h_ne
  | step h_ne h_valid h_rest ih =>
    cases h' with
    | halt _ _ h_enc => exact absurd h_enc h_ne
    | step h_ne' h_valid' h_rest' => exact ih h_rest'

/-- The value of `while_` is the unique `WhileSem`-reachable final state. -/
lemma while_sem_val {env : List Value} (i : Routine (α × β))
    (body : Routine (α × β) → Routine (α × β))
    (h : (while_ i body).valid env) (h_init : i.valid env) {r : α × β}
    (hr : WhileSem env body (i.sem env h_init).val r) :
    ((while_ i body).sem env h).val = r := by
  have key : WhileSem env body (i.sem env h_init).val ((while_ i body).sem env h).val :=
    Classical.choose_spec (h.elim (fun _ h'' => h'') :
      ∃ r', WhileSem env body (i.sem env h_init).val r')
  exact WhileSem.det key hr

-- ------------------- Resource Consumption -------------------------

-- def OutputsOSize (impl : PB) (s : List Value → ℕ) : Prop :=
--   ∃ a b, ∀ env, ∃ out,
--     impl.Computes env out ∧ out.size ≤ a * (s env) + b

-- def UsesOTime (impl : PB) (t : List Value → ℕ) : Prop :=
--   ∃ a b, ∀ env, ∃ out s, ∃ t' ≤ a * (t env) + b,
--     ProgSem env (impl env.length) out t' s

-- def UsesOSpace (impl : PB) (s : List Value → ℕ) : Prop :=
--   ∃ a b, ∀ env, ∃ out t, ∃ s' ≤ a * (s env) + b,
--     ProgSem env (impl env.length) out t s'

-- def UsesLinearTimeAndSpace (impl : PB) : Prop :=
--   PB.UsesOTime impl (fun env => (env.map fun x => x.size).sum) ∧
--   PB.UsesOSpace impl (fun env => (env.map fun x => x.size).sum)

end Routine

end RoseTreeMachine

end Turing
