/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.DepthRec

/-!
# Reachability by double recursion

The algorithm behind Savitch's theorem, instantiated into `Bounds.depthRec`.

`reach E verts k a b` asks whether there is a path from `a` to `b` of length at most `2 ^ k`, by
guessing a midpoint and recursing twice:

```
reach E verts (k+1) a b  =  verts.any fun m => reach E verts k a m && reach E verts k m b
```

The two recursive calls run *sequentially*, so they reuse each other's work space; only the frame
of the enclosing call stays live. That is why the space is `depth × frame` rather than
`branching ^ depth`.

## Two encoding choices, both forced

* **Levels are unary** (`List Unit`). The schema has to test `k = 0` and form `k - 1`, and there
  is no ℕ-arithmetic primitive — but `List.isEmpty` and `List.tail` are primitives. This is the
  same device `Cnf.lean` uses for variable indices, and it is harmless: unary and binary levels
  are polynomially related.
* **The activation state is a `structure`** with named fields. Its `DataEncode` instance comes
  from `DataEncode.ofInjection Activation.toProd`, so the encoding *is* the tuple's encoding.
  `Activation.toProd` and `Activation.ofProd` are therefore no-ops on encodings and get
  certificates from `Bounds.recode` without any new assumption. Field access is then an ordinary
  `Bounds.fst`/`Bounds.snd` chain.

The midpoint search is a plain `List V` carried inside the activation, so nothing of the size of
the whole search space is ever materialised — this is the point of the resumable-strategy shape
of `RecSchema`.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace Reach

open RoseTreeMachine RecSchema

variable {V : Type} [DataEncode V] [DecidableEq V] [Inhabited V]

/-- Recursion levels, in unary. -/
abbrev Level := List Unit

/-- A question: at what level, and between which two vertices? -/
abbrev Question (V : Type) := Level × V × V

/-- An activation. -/
structure Activation (V : Type) where
  /-- This activation's recursion level, in unary. -/
  level : Level
  /-- The source vertex. -/
  source : V
  /-- The target vertex. -/
  target : V
  /-- The midpoints still to try. -/
  remaining : List V
  /-- Has this activation succeeded? -/
  finished : Bool
  /-- The result, meaningful once finished. -/
  result : Bool
  /-- Are we awaiting the right half `m → target`? -/
  awaitingRight : Bool

/-- The underlying tuple. Only carries the encoding across; never appears in the algorithm. -/
def Activation.toProd (s : Activation V) : Level × V × V × List V × Bool × Bool × Bool :=
  (s.level, s.source, s.target, s.remaining, s.finished, s.result, s.awaitingRight)

/-- The inverse, for building an activation from certified components. -/
def Activation.ofProd (p : Level × V × V × List V × Bool × Bool × Bool) : Activation V :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩

omit [DataEncode V] [DecidableEq V] [Inhabited V] in
lemma Activation.toProd_injective : Function.Injective (Activation.toProd (V := V)) := by
  intro x y h
  cases x
  cases y
  simp only [Activation.toProd, Prod.mk.injEq] at h
  simp_all

instance : DataEncode (Activation V) :=
  DataEncode.ofInjection Activation.toProd Activation.toProd_injective

/-- An activation that is still scanning midpoints. -/
def scanning (k : Level) (a b : V) (ms : List V) (aw : Bool) : Activation V :=
  { level := k, source := a, target := b, remaining := ms, finished := false, result := false,
    awaitingRight := aw }

/-- An activation that has found a midpoint and succeeded. -/
def succeeded (k : Level) (a b : V) (ms : List V) : Activation V :=
  { level := k, source := a, target := b, remaining := ms, finished := true, result := true,
    awaitingRight := false }

/-- **The algorithm.** Is there a path from `a` to `b` of length at most `2 ^ k`? -/
def reach (E : V → V → Bool) (verts : List V) : Level → V → V → Bool
  | [], a, b => (a == b) || E a b
  | _ :: ks, a, b => verts.any fun m => reach E verts ks a m && reach E verts ks m b

/-- Opening an activation. A level-zero question is answered outright. -/
def enter (E : V → V → Bool) (verts : List V) (q : Question V) : Activation V :=
  cond q.1.isEmpty
    { level := [], source := q.2.1, target := q.2.2, remaining := [], finished := true,
      result := (q.2.1 == q.2.2) || E q.2.1 q.2.2, awaitingRight := false }
    (scanning q.1 q.2.1 q.2.2 verts false)

/-- An activation is finished when it has succeeded, run out of midpoints, or is at level zero. -/
def isDone (s : Activation V) : Bool := s.finished || s.remaining.isEmpty || s.level.isEmpty

/-- The result of a finished activation. -/
def answer (s : Activation V) : Bool := s.result

/-- The sub-question: the left half `source → m`, or the right half `m → target` once the left
succeeded. -/
def ask (s : Activation V) : Question V :=
  (s.level.tail,
    cond s.awaitingRight (s.remaining.head?.getD default) s.source,
    cond s.awaitingRight s.target (s.remaining.head?.getD default))

/-- Absorbing a sub-answer: a successful left half moves on to the right half, a successful right
half finishes, and any failure moves to the next midpoint. -/
def resume (s : Activation V) (ans : Bool) : Activation V :=
  cond ans
    (cond s.awaitingRight
      { s with finished := true, result := true, awaitingRight := false }
      { s with awaitingRight := true })
    { s with
      remaining := s.remaining.tail, finished := false, result := false,
      awaitingRight := false }

/-- **The schema.** The level decreases on every sub-question, which is what bounds the stack. -/
def schema (E : V → V → Bool) (verts : List V) :
    RecSchema (Question V) Bool (Activation V) where
  enter := enter E verts
  isDone := isDone
  answer := answer
  ask := ask
  resume := resume
  level s := s.level.length
  level_ask := by
    intro s hs
    simp only [isDone, Bool.or_eq_false_iff] at hs
    obtain ⟨⟨-, hremaining⟩, hlevel⟩ := hs
    have h1 : s.level ≠ [] := by
      intro h; rw [h] at hlevel; simp at hlevel
    simp only [enter, ask]
    cases hc : (s.level.tail).isEmpty with
    | true => simpa using Nat.pos_of_ne_zero (fun h => h1 (List.eq_nil_of_length_eq_zero h))
    | false =>
      simp only [Bool.cond_false, scanning, List.length_tail]
      exact Nat.sub_lt (Nat.pos_of_ne_zero fun h => h1 (List.eq_nil_of_length_eq_zero h))
        Nat.one_pos
  level_resume := by
    intro s b
    cases b <;> cases hw : s.awaitingRight <;> simp [resume, hw]

/-! ## Correctness: the schema evaluates to `reach` -/

omit [DataEncode V] in
/-- Scanning the remaining midpoints at one level. The inner induction of `heval`. -/
lemma scan (E : V → V → Bool) (verts : List V) (ks : Level) (u : Unit)
    (ih : ∀ x y : V, EvalFrom (schema E verts) ((schema E verts).enter (ks, x, y))
      (reach E verts ks x y)) (a b : V) (ms : List V) :
    EvalFrom (schema E verts) (scanning (u :: ks) a b ms false)
      (ms.any fun m => reach E verts ks a m && reach E verts ks m b) := by
  induction ms with
  | nil =>
    have hd : (schema E verts).isDone (scanning (u :: ks) a b ([] : List V) false)
        = true := by simp [schema, isDone, scanning]
    simpa [schema, answer, scanning, succeeded] using EvalFrom.ret (S := schema E verts) hd
  | cons m ms ih2 =>
    have hd : (schema E verts).isDone (scanning (u :: ks) a b (m :: ms) false)
        = false := by simp [schema, isDone, scanning]
    have hq : (schema E verts).ask (scanning (u :: ks) a b (m :: ms) false)
        = (ks, a, m) := by simp [schema, ask, scanning]
    rw [List.any_cons]
    refine EvalFrom.ask (b' := reach E verts ks a m) hd (by rw [hq]; exact ih a m) ?_
    cases hL : reach E verts ks a m with
    | false =>
      have he : (schema E verts).resume (scanning (u :: ks) a b (m :: ms) false) false
          = (scanning (u :: ks) a b ms false) := by simp [schema, resume, scanning]
      rw [he]
      simpa using ih2
    | true =>
      have he : (schema E verts).resume (scanning (u :: ks) a b (m :: ms) false) true
          = (scanning (u :: ks) a b (m :: ms) true) := by simp [schema, resume, scanning]
      rw [he]
      have hd2 : (schema E verts).isDone (scanning (u :: ks) a b (m :: ms) true)
          = false := by simp [schema, isDone, scanning]
      have hq2 : (schema E verts).ask (scanning (u :: ks) a b (m :: ms) true)
          = (ks, m, b) := by simp [schema, ask, scanning]
      refine EvalFrom.ask (b' := reach E verts ks m b) hd2 (by rw [hq2]; exact ih m b) ?_
      cases hR : reach E verts ks m b with
      | false =>
        have he2 : (schema E verts).resume
            (scanning (u :: ks) a b (m :: ms) true) false
            = (scanning (u :: ks) a b ms false) := by simp [schema, resume, scanning]
        rw [he2]
        simpa using ih2
      | true =>
        have he2 : (schema E verts).resume
            (scanning (u :: ks) a b (m :: ms) true) true
            = (succeeded (u :: ks) a b (m :: ms)) := by simp [schema, resume, scanning, succeeded]
        rw [he2]
        have hd3 : (schema E verts).isDone (succeeded (u :: ks) a b (m :: ms))
            = true := by simp [schema, isDone, succeeded]
        simpa [schema, answer, scanning, succeeded] using EvalFrom.ret (S := schema E verts) hd3

omit [DataEncode V] in
/-- **The schema computes `reach`.** This is `depthRec`'s `heval` obligation, and it is a plain
induction on the level — the machine never appears. -/
lemma heval (E : V → V → Bool) (verts : List V) (k : Level) (a b : V) :
    Eval (schema E verts) (k, a, b) (reach E verts k a b) := by
  induction k generalizing a b with
  | nil =>
    have hd : (schema E verts).isDone ((schema E verts).enter (([] : Level), a, b)) = true := by
      simp [schema, enter, isDone, scanning]
    change EvalFrom (schema E verts) ((schema E verts).enter (([] : Level), a, b)) _
    simpa [schema, enter, answer, reach, scanning] using EvalFrom.ret (S := schema E verts) hd
  | cons u ks ih =>
    have he : (schema E verts).enter ((u :: ks : Level), a, b)
        = (scanning (u :: ks) a b verts false) := by simp [schema, enter, scanning]
    change EvalFrom (schema E verts) ((schema E verts).enter ((u :: ks : Level), a, b)) _
    rw [he]
    simpa [reach] using scan E verts ks u (fun x y => ih x y) a b verts

end Reach

end MultiTapeTM

end Turing
