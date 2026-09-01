/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.While

/-!
# Depth-bounded recursion

`Bounds.depthRec` is the companion of `Bounds.fold` and `Bounds.while` for algorithms defined by
*recursion whose depth depends on the input*, of which the archetype is the double recursion in
Savitch's theorem.

## Why this needs its own combinator

`fold` and `while` share one accounting fact: iterations reuse each other's tapes, so their space
cost is the *maximum* over iterations. Recursion inverts half of that. Sibling calls do reuse each
other's tapes, but a call at depth `k+1` must keep its own frame live *while* the call at depth `k`
runs underneath it. So space is a **sum down the depth** and a max across the breadth:

| | time | space |
| --- | --- | --- |
| `fold`, `while` | × trip count | max over iterations |
| `depthRec` | × branching ^ depth | **depth × frame** |

That asymmetry is the whole content of Savitch's theorem.

Note that the recursion cannot simply be unrolled into a fixed composition of primitives: its
depth depends on the input size, so unrolling would give a *family* of machines indexed by the
depth — a circuit family — rather than the single uniform machine that is wanted.

## No new assumed machine

Despite that, this file adds **no `sorry`**. The recursion is compiled to a `while` loop over an
explicit stack, and `Bounds.while`'s `A` argument — its bound on intermediate values — charges
that stack exactly. The stack is the algorithmic content of Savitch's theorem, so it is proved
here rather than assumed.

## The schema

A recursive algorithm is presented not as a Lean recursive function but as a *resumable state
machine*: each activation either returns, or asks one sub-question and waits to be resumed with
the answer. This shape is what makes the combinator general enough for Savitch. In particular the
midpoint search is a plain counter living in `σ`, so no exponentially large list of midpoints is
ever materialised, and the two recursive calls per midpoint are simply two states.

Every field is a first-order function, which is what lets each be certified separately with the
ordinary combinators; there is deliberately no `Q ⊕ β` and no `Option`, since branching on `Bool`
is what `Bounds.ite` supports.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

variable {Q β σ : Type}

/-- **A depth-recursive algorithm, defunctionalised.**

An activation is a state `σ`. It either `isDone`, in which case its `answer` is the result, or it
`ask`s a sub-question, and is later `resume`d with that sub-question's answer.

`level` is the recursion level, and the two laws say it strictly decreases when a sub-question is
entered and never increases on resumption. This is what bounds the stack depth — and, being a
well-founded measure, it is also what makes the recursion terminate. -/
structure RecSchema (Q β σ : Type) where
  /-- Begin an activation for a question. -/
  enter : Q → σ
  /-- Has this activation finished? -/
  isDone : σ → Bool
  /-- The result of a finished activation. -/
  answer : σ → β
  /-- The sub-question an unfinished activation asks. -/
  ask : σ → Q
  /-- Absorb a sub-answer and advance. -/
  resume : σ → β → σ
  /-- The recursion level, bounding the stack depth. -/
  level : σ → ℕ
  /-- Entering a sub-question strictly decreases the level. -/
  level_ask : ∀ s, isDone s = false → level (enter (ask s)) < level s
  /-- Resuming never increases the level. -/
  level_resume : ∀ s b, level (resume s b) ≤ level s

namespace RecSchema

variable [Inhabited β] [Inhabited σ] (S : RecSchema Q β σ)

/-- **What the algorithm computes.** `EvalFrom S s b` says the activation `s`, run to completion
with all its sub-questions answered recursively, returns `b`. -/
inductive EvalFrom (S : RecSchema Q β σ) : σ → β → Prop where
  /-- A finished activation returns its answer. -/
  | ret {s : σ} : S.isDone s = true → EvalFrom S s (S.answer s)
  /-- An unfinished activation evaluates its sub-question, then continues. -/
  | ask {s : σ} {b' b : β} : S.isDone s = false → EvalFrom S (S.enter (S.ask s)) b' →
      EvalFrom S (S.resume s b') b → EvalFrom S s b

/-- The value of a question: run the activation it opens. -/
def Eval (S : RecSchema Q β σ) (q : Q) (b : β) : Prop := EvalFrom S (S.enter q) b

/-! ### The stack machine

The state is a one-slot value register paired with a stack of activations. The register is a
`List β` rather than an `Option β` so that `List.isEmpty`, `List.head?` and `List.cons` — all of
which are already primitives — can take it apart. -/

/-- One step: deliver a pending answer to the caller, or advance the top activation.

Written with `cond`, `List.head?.getD` and `List.tail` rather than by pattern matching, because
those are exactly the shapes the primitives in `Primitives.lean` certify — `mstepBounds` below
mirrors this definition constructor for constructor. -/
def mstep (c : List β × List σ) : List β × List σ :=
  cond c.2.isEmpty c
    (cond c.1.isEmpty
      (cond (S.isDone (c.2.head?.getD default))
        ([S.answer (c.2.head?.getD default)], c.2.tail)
        ([], S.enter (S.ask (c.2.head?.getD default)) :: c.2))
      ([], S.resume (c.2.head?.getD default) (c.1.head?.getD default) :: c.2.tail))

/-- The loop is finished when the stack is empty; the register then holds the answer. -/
def mhalt (c : List β × List σ) : Bool := c.2.isEmpty

/-- The starting state for a question. -/
def minit (q : Q) : List β × List σ := ([], [S.enter q])

variable {S}

@[simp] lemma mstep_deliver (b : β) (r : List β) (s : σ) (st : List σ) :
    S.mstep (b :: r, s :: st) = ([], S.resume s b :: st) := by simp [mstep]

/-- Once the stack is empty the machine is a fixed point, which is what lets the first halting
time be read off with `Nat.find`. -/
@[simp] lemma mstep_halted {c : List β × List σ} (h : c.2 = []) : S.mstep c = c := by
  simp [mstep, h]

lemma mstep_iterate_halted {c : List β × List σ} (h : c.2 = []) (t : ℕ) :
    S.mstep^[t] c = c := Function.iterate_fixed (mstep_halted h) t

@[simp] lemma mstep_done {s : σ} (hs : S.isDone s = true) (st : List σ) :
    S.mstep ([], s :: st) = ([S.answer s], st) := by simp [mstep, hs]

@[simp] lemma mstep_ask {s : σ} (hs : S.isDone s = false) (st : List σ) :
    S.mstep ([], s :: st) = ([], S.enter (S.ask s) :: s :: st) := by simp [mstep, hs]

/-- **The stack machine implements the recursion.** Running it on an activation pushed onto any
stack `st` returns that activation's value in the register and leaves `st` exactly as it was.

This is the correspondence that lets `depthRec` be derived rather than assumed. -/
theorem complete {s : σ} {b : β} (h : EvalFrom S s b) (st : List σ) :
    ∃ t, (S.mstep)^[t] ([], s :: st) = ([b], st) := by
  induction h generalizing st with
  | ret hs => exact ⟨1, by simp [mstep, hs]⟩
  | @ask s b' b hs _ _ ih1 ih2 =>
    obtain ⟨t1, ht1⟩ := ih1 (s :: st)
    obtain ⟨t2, ht2⟩ := ih2 st
    refine ⟨t2 + 1 + t1 + 1, ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_one]
    have e0 : S.mstep ([], s :: st) = ([], S.enter (S.ask s) :: s :: st) := by simp [mstep, hs]
    have e1 : S.mstep ([b'], s :: st) = ([], S.resume s b' :: st) := by simp [mstep]
    rw [e0, Function.iterate_add_apply, ht1, Function.iterate_add_apply, Function.iterate_one,
      e1, ht2]

/-- **The completion lemma with a step count.**

`complete` alone says the machine halts, but `depthRec`'s `N` obligation needs a *bound* on when.
`M` is a step-count measure on activations, supplied by the caller in the same spirit as `D`, `F`
and `B`: it must cover one step for a finished activation, and for an unfinished one must cover
its sub-question, its continuation, and the two steps that push and deliver. -/
theorem complete_le {s : σ} {b : β} (h : EvalFrom S s b) (M : σ → ℕ)
    (hret : ∀ s', S.isDone s' = true → 1 ≤ M s')
    (hask : ∀ s' b'', S.isDone s' = false →
      M (S.enter (S.ask s')) + M (S.resume s' b'') + 2 ≤ M s')
    (st : List σ) : ∃ t ≤ M s, (S.mstep)^[t] ([], s :: st) = ([b], st) := by
  induction h generalizing st with
  | ret hs => exact ⟨1, hret _ hs, by simp [mstep, hs]⟩
  | @ask s b' b hs _ _ ih1 ih2 =>
    obtain ⟨t1, ht1le, ht1⟩ := ih1 (s :: st)
    obtain ⟨t2, ht2le, ht2⟩ := ih2 st
    have hbound := hask s b' hs
    refine ⟨t2 + 1 + t1 + 1, by omega, ?_⟩
    have e0 : S.mstep ([], s :: st) = ([], S.enter (S.ask s) :: s :: st) := by simp [mstep, hs]
    have e1 : S.mstep ([b'], s :: st) = ([], S.resume s b' :: st) := by simp [mstep]
    rw [Function.iterate_add_apply, Function.iterate_one, e0, Function.iterate_add_apply, ht1,
      Function.iterate_add_apply, Function.iterate_one, e1, ht2]

/-! ### The depth invariant

The stack is strictly increasing in level from the top down, because `level_ask` makes every push
strictly decrease the level and `level_resume` never raises it. Levels are naturals, so a strictly
increasing chain bounded by `L` has at most `L + 1` entries — which is exactly the statement that
the recursion depth bounds the stack height. -/

variable (S)

/-- The stack is strictly increasing in level from the top down. -/
def Ordered : List σ → Prop
  | [] => True
  | [_] => True
  | s :: s' :: st => S.level s < S.level s' ∧ Ordered (s' :: st)

/-- Everything reachable during a run: a register holding at most one value, and a well-ordered
stack whose levels are bounded by `L`. -/
def Inv (L : ℕ) (c : List β × List σ) : Prop :=
  c.1.length ≤ 1 ∧ Ordered S c.2 ∧ ∀ s ∈ c.2, S.level s ≤ L

variable {S}

omit [Inhabited β] [Inhabited σ] in
lemma Ordered.tail {s : σ} {st : List σ} (h : Ordered S (s :: st)) : Ordered S st := by
  cases st with
  | nil => trivial
  | cons s' st => exact h.2

omit [Inhabited β] [Inhabited σ] in
lemma Ordered.push {s : σ} {st : List σ} (h : Ordered S st)
    (hlt : ∀ s', st.head? = some s' → S.level s < S.level s') : Ordered S (s :: st) := by
  cases st with
  | nil => trivial
  | cons s' st => exact ⟨hlt s' rfl, h⟩

omit [Inhabited β] [Inhabited σ] in
lemma Ordered.replace_head {s t : σ} {st : List σ} (h : Ordered S (s :: st))
    (hle : S.level t ≤ S.level s) : Ordered S (t :: st) := by
  cases st with
  | nil => trivial
  | cons s' st => exact ⟨lt_of_le_of_lt hle h.1, h.2⟩

omit [Inhabited β] [Inhabited σ] in
/-- **A strictly increasing chain of levels bounded by `hi` is short.** -/
lemma Ordered.length_le {s : σ} : ∀ {st : List σ}, Ordered S (s :: st) →
    ∀ hi, (∀ x ∈ s :: st, S.level x ≤ hi) → (s :: st).length + S.level s ≤ hi + 1 := by
  intro st
  induction st generalizing s with
  | nil =>
    intro _ hi hhi
    have := hhi s (by simp)
    simp only [List.length_cons, List.length_nil]
    omega
  | cons s' st ih =>
    intro h hi hhi
    have h1 : S.level s < S.level s' := h.1
    have h2 := ih h.2 hi (fun x hx => hhi x (by simp at hx ⊢; tauto))
    simp only [List.length_cons] at h2 ⊢
    omega

/-- The invariant is preserved by one step of the machine. -/
lemma inv_mstep {L : ℕ} {c : List β × List σ} (h : Inv S L c) : Inv S L (S.mstep c) := by
  obtain ⟨r, st⟩ := c
  obtain ⟨hr, hord, hlevel⟩ := h
  cases r with
  | cons b r =>
    cases st with
    | nil => exact ⟨hr, hord, hlevel⟩
    | cons s st =>
      rw [mstep_deliver]
      refine ⟨by simp, hord.replace_head (S.level_resume s b), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (S.level_resume s b) (hlevel s (by simp))
      · exact hlevel x (by simp [hx])
  | nil =>
    cases st with
    | nil => exact ⟨hr, hord, hlevel⟩
    | cons s st =>
      by_cases hd : S.isDone s = true
      · rw [mstep_done hd]
        exact ⟨by simp, hord.tail, fun x hx => hlevel x (by simp [hx])⟩
      · simp only [Bool.not_eq_true] at hd
        rw [mstep_ask hd]
        refine ⟨by simp, Ordered.push hord ?_, ?_⟩
        · intro s' hs'
          simp only [List.head?_cons, Option.some.injEq] at hs'
          exact hs' ▸ S.level_ask s hd
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_trans (le_of_lt (S.level_ask s hd)) (hlevel s (by simp))
          · exact hlevel x hx

/-- Hence by every reachable state. -/
lemma inv_iterate {L : ℕ} {c : List β × List σ} (h : Inv S L c) (t : ℕ) :
    Inv S L (S.mstep^[t] c) := by
  induction t generalizing c with
  | zero => simpa using h
  | succ t ih => rw [Function.iterate_succ_apply]; exact ih (inv_mstep h)

omit [Inhabited β] [Inhabited σ] in
/-- The starting state satisfies the invariant, with `L` the level of the opening activation. -/
lemma inv_minit (q : Q) : Inv S (S.level (S.enter q)) (S.minit q) :=
  ⟨by simp [minit], trivial, by
    intro x hx
    simp only [minit, List.mem_singleton] at hx
    simp [hx]⟩

omit [Inhabited β] [Inhabited σ] in
/-- **The recursion depth bounds the stack height.** -/
lemma stack_length_le {L : ℕ} {c : List β × List σ} (h : Inv S L c) :
    c.2.length ≤ L + 1 := by
  obtain ⟨_, hord, hlevel⟩ := h
  cases hc : c.2 with
  | nil => simp
  | cons s st =>
    rw [hc] at hord hlevel
    have := (hord.length_le (hi := L) hlevel)
    simp only [List.length_cons] at this ⊢
    omega

/-! ### Reachable frames

`depthRec`'s `F` and `B` obligations are about every state the machine passes through. Proving
them directly would mean reasoning about `mstep^[j]`, which is exactly the machine-level detail
the combinator exists to hide. `frame_inv` reduces them to a *schema-level* invariant: a predicate
closed under entering a sub-question and under resumption. -/

variable (S)

/-- Every frame on the stack satisfies `I`, and every value in the register is the answer of some
`I`-frame. -/
def StateInv (I : σ → Prop) (c : List β × List σ) : Prop :=
  (∀ s ∈ c.2, I s) ∧ ∀ b ∈ c.1, ∃ s, I s ∧ b = S.answer s

variable {S}

lemma stateInv_mstep {I : σ → Prop} {c : List β × List σ}
    (henter : ∀ s, I s → S.isDone s = false → I (S.enter (S.ask s)))
    (hresume : ∀ s b, I s → I (S.resume s b))
    (h : StateInv S I c) : StateInv S I (S.mstep c) := by
  obtain ⟨r, st⟩ := c
  obtain ⟨hst, hr⟩ := h
  cases r with
  | cons b r =>
    cases st with
    | nil => exact ⟨hst, hr⟩
    | cons s st =>
      rw [mstep_deliver]
      refine ⟨?_, by simp⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hresume s b (hst s (by simp))
      · exact hst x (by simp [hx])
  | nil =>
    cases st with
    | nil => exact ⟨hst, hr⟩
    | cons s st =>
      by_cases hd : S.isDone s = true
      · rw [mstep_done hd]
        refine ⟨fun x hx => hst x (by simp [hx]), ?_⟩
        intro b hb
        simp only [List.mem_singleton] at hb
        exact ⟨s, hst s (by simp), hb⟩
      · simp only [Bool.not_eq_true] at hd
        rw [mstep_ask hd]
        refine ⟨?_, by simp⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact henter s (hst s (by simp)) hd
        · exact hst x hx

/-- **The schema-level invariant transfers to every reachable machine state.** This is what
discharges `depthRec`'s `F` and `B` obligations in practice. -/
lemma frame_inv {I : σ → Prop} {q : Q}
    (hinit : I (S.enter q))
    (henter : ∀ s, I s → S.isDone s = false → I (S.enter (S.ask s)))
    (hresume : ∀ s b, I s → I (S.resume s b))
    (j : ℕ) : StateInv S I (S.mstep^[j] (S.minit q)) := by
  induction j with
  | zero =>
    refine ⟨?_, by simp [minit]⟩
    intro s hs
    simp only [Function.iterate_zero, id_eq, minit, List.mem_singleton] at hs
    exact hs ▸ hinit
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact stateInv_mstep henter hresume ih

/-! ### From the machine to a certificate -/

section Run

variable {α : Type} [DataEncode α] [DataEncode Q] [DataEncode β] [DataEncode σ]
  {f : α → β} {mkQ : α → Q}

omit [DataEncode α] [DataEncode Q] [DataEncode β] [DataEncode σ] in
/-- The machine halts on every question the algorithm evaluates. -/
lemma halts (heval : ∀ a, Eval S (mkQ a) (f a)) (a : α) :
    ∃ t, mhalt (S.mstep^[t] (S.minit (mkQ a))) = true := by
  obtain ⟨t, ht⟩ := complete (heval a) []
  refine ⟨t, ?_⟩
  rw [show S.minit (mkQ a) = ([], S.enter (mkQ a) :: []) from rfl, ht]
  simp [mhalt]

/-- The first time the machine halts.

Because `Nat.find` is *least*, `Bounds.while`'s `h_first` obligation is discharged here by
`Nat.find_min` rather than being forwarded to the caller, as `Universal.lean`'s `uRunBounds`
currently has to do. -/
noncomputable def steps (heval : ∀ a, Eval S (mkQ a) (f a)) (a : α) : ℕ :=
  open scoped Classical in Nat.find (halts heval a)

omit [DataEncode α] [DataEncode Q] [DataEncode β] [DataEncode σ] in
/-- **A step-count measure bounds the halting time.** This is how `depthRec`'s `N` obligation is
discharged: `Nat.find` is least, so any exhibited halting time bounds it. -/
lemma steps_le (heval : ∀ a, Eval S (mkQ a) (f a)) (M : σ → ℕ)
    (hret : ∀ s', S.isDone s' = true → 1 ≤ M s')
    (hask : ∀ s' b'', S.isDone s' = false →
      M (S.enter (S.ask s')) + M (S.resume s' b'') + 2 ≤ M s')
    (a : α) : steps heval a ≤ M (S.enter (mkQ a)) := by
  obtain ⟨t, hle, ht⟩ := complete_le (heval a) M hret hask []
  refine le_trans (Nat.find_le ?_) hle
  rw [show S.minit (mkQ a) = ([], S.enter (mkQ a) :: []) from rfl, ht]
  simp [mhalt]

omit [DataEncode α] [DataEncode Q] [DataEncode β] [DataEncode σ] in
/-- **At the halting time the register holds the answer and the stack is empty.** -/
lemma run_eq (heval : ∀ a, Eval S (mkQ a) (f a)) (a : α) :
    S.mstep^[steps heval a] (S.minit (mkQ a)) = ([f a], []) := by
  obtain ⟨t, ht⟩ := complete (heval a) []
  have hmi : S.minit (mkQ a) = ([], S.enter (mkQ a) :: []) := rfl
  have hle : steps heval a ≤ t := Nat.find_le (by rw [hmi, ht]; simp [mhalt])
  have hspec : mhalt (S.mstep^[steps heval a] (S.minit (mkQ a))) = true :=
    Nat.find_spec (halts heval a)
  have hempty : (S.mstep^[steps heval a] (S.minit (mkQ a))).2 = [] := by
    simpa [mhalt, List.isEmpty_iff] using hspec
  have hfix : S.mstep^[t] (S.minit (mkQ a)) = S.mstep^[steps heval a] (S.minit (mkQ a)) := by
    rw [show t = (t - steps heval a) + steps heval a by omega, Function.iterate_add_apply]
    exact mstep_iterate_halted hempty _
  rw [← hfix, hmi, ht]

omit [DataEncode α] [DataEncode Q] in
/-- **The reachable states are small.** The register holds at most one value, and the stack is no
taller than the recursion depth — this is where `depth × frame` enters the space bound. -/
lemma state_size_le (a : α) (j : ℕ) (D F B : ℕ)
    (hD : S.level (S.enter (mkQ a)) ≤ D)
    (hF : ∀ s ∈ (S.mstep^[j] (S.minit (mkQ a))).2, (DataEncode.encode s).size ≤ F)
    (hB : ∀ b ∈ (S.mstep^[j] (S.minit (mkQ a))).1, (DataEncode.encode b).size ≤ B) :
    (DataEncode.encode (S.mstep^[j] (S.minit (mkQ a)))).size ≤ B + F * (D + 1) + 6 := by
  obtain ⟨hreg, hord, hlevel⟩ := inv_iterate (inv_minit (S := S) (mkQ a)) j
  have hlen : (S.mstep^[j] (S.minit (mkQ a))).2.length ≤ D + 1 :=
    le_trans (stack_length_le ⟨hreg, hord, hlevel⟩) (by omega)
  have hsum2 := sum_map_le _ (fun s => (DataEncode.encode s).size) F hF
  have hsum1 := sum_map_le _ (fun b => (DataEncode.encode b).size) B hB
  have e : (DataEncode.encode (S.mstep^[j] (S.minit (mkQ a)))).size
      = (DataEncode.encode (S.mstep^[j] (S.minit (mkQ a))).1).size
        + (DataEncode.encode (S.mstep^[j] (S.minit (mkQ a))).2).size + 2 :=
    DataEncode.size_pair _ _
  rw [e, DataEncode.size_list, DataEncode.size_list]
  have h1 : B * (S.mstep^[j] (S.minit (mkQ a))).1.length ≤ B := by
    calc B * (S.mstep^[j] (S.minit (mkQ a))).1.length ≤ B * 1 := Nat.mul_le_mul_left _ hreg
      _ = B := by omega
  have h2 : F * (S.mstep^[j] (S.minit (mkQ a))).2.length ≤ F * (D + 1) :=
    Nat.mul_le_mul_left _ hlen
  omega

/-! ### Certificates for the machine's pieces

Each mirrors the corresponding definition constructor for constructor, so the transports are
`rfl`. -/

variable (S)

/-- A certificate for one machine step, assembled from certificates for the schema's fields. -/
def mstepBounds (he : Bounds S.enter) (hd : Bounds S.isDone) (ha : Bounds S.answer)
    (hk : Bounds S.ask) (hres : Bounds (Function.uncurry S.resume)) : Bounds S.mstep :=
  Bounds.ite (Bounds.comp Bounds.isEmpty Bounds.snd) Bounds.id
    (Bounds.ite (Bounds.comp Bounds.isEmpty Bounds.fst)
      (Bounds.ite (Bounds.comp hd (Bounds.comp (Bounds.headD default) Bounds.snd))
        (Bounds.pair
          (Bounds.cons (Bounds.comp ha (Bounds.comp (Bounds.headD default) Bounds.snd))
            (Bounds.const []))
          (Bounds.comp Bounds.tail Bounds.snd))
        (Bounds.pair (Bounds.const [])
          (Bounds.cons
            (Bounds.comp he (Bounds.comp hk (Bounds.comp (Bounds.headD default) Bounds.snd)))
            Bounds.snd)))
      (Bounds.pair (Bounds.const [])
        (Bounds.cons
          (Bounds.comp hres
            (Bounds.pair (Bounds.comp (Bounds.headD default) Bounds.snd)
              (Bounds.comp (Bounds.headD default) Bounds.fst)))
          (Bounds.comp Bounds.tail Bounds.snd))))

/-- A certificate for the starting state. -/
def minitBounds {mkQ : α → Q} (hmk : Bounds mkQ) (he : Bounds S.enter) :
    Bounds (fun a => S.minit (mkQ a)) :=
  Bounds.pair (Bounds.const []) (Bounds.cons (Bounds.comp he hmk) (Bounds.const []))

/-- A certificate for the halting test. -/
def mhaltBounds : Bounds (mhalt : List β × List σ → Bool) :=
  Bounds.comp Bounds.isEmpty Bounds.snd

end Run

end RecSchema

/-! ## The combinator -/

namespace Bounds

open RecSchema

variable {α : Type} [DataEncode α] [DataEncode Q] [DataEncode β] [DataEncode σ]
  [Inhabited β] [Inhabited σ]

/-- **Depth-bounded recursion.**

`f` is computed by the schema `S`, opened at the question `mkQ a`. The four quantities a human
must invent — the analogue of `A` for `Bounds.fold` — are:

* `N`, a bound on the total number of machine steps (the size of the call tree);
* `D`, a bound on the recursion depth, via the level of the opening activation;
* `F`, a bound on the encoded size of a single activation (the *frame*);
* `B`, a bound on the encoded size of an answer.

The space bound is `O(D · F)`: **additive in the depth**, which is the point. -/
noncomputable def depthRec (S : RecSchema Q β σ) {f : α → β} {mkQ : α → Q}
    (hmk : Bounds mkQ) (he : Bounds S.enter) (hd : Bounds S.isDone) (ha : Bounds S.answer)
    (hk : Bounds S.ask) (hres : Bounds (Function.uncurry S.resume))
    (heval : ∀ a, Eval S (mkQ a) (f a))
    (N D F B : ℕ → ℕ) (hN_mono : Monotone N)
    (hA_mono : Monotone (fun n => B n + F n * (D n + 1) + 6))
    (hN : ∀ a, steps heval a ≤ N (DataEncode.encode a).size)
    (hD : ∀ a, S.level (S.enter (mkQ a)) ≤ D (DataEncode.encode a).size)
    (hF : ∀ (a : α) (j : ℕ), ∀ s ∈ (S.mstep^[j] (S.minit (mkQ a))).2,
      (DataEncode.encode s).size ≤ F (DataEncode.encode a).size)
    (hB : ∀ (a : α) (j : ℕ), ∀ b ∈ (S.mstep^[j] (S.minit (mkQ a))).1,
      (DataEncode.encode b).size ≤ B (DataEncode.encode a).size) :
    Bounds f :=
  (Bounds.comp (Bounds.headD default)
    (Bounds.comp Bounds.fst
      (Bounds.while (minitBounds S hmk he) mhaltBounds
        (mstepBounds S he hd ha hk hres)
        (steps heval)
        (fun _ => rfl)
        (fun a => Nat.find_spec (halts heval a))
        (fun a j hj => by
          have := Nat.find_min (halts heval a) hj
          simpa using this)
        N (fun n => B n + F n * (D n + 1) + 6) hN_mono hA_mono hN
        (fun a j _ => state_size_le a j _ _ _ (hD a) (hF a j) (hB a j))))).congr
    (funext fun a => by simp only [Function.comp_apply]; rw [run_eq heval a]; rfl)

end Bounds

end MultiTapeTM

end Turing
