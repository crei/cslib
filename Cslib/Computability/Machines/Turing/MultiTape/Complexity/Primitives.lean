/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Bounds
public import Mathlib.Data.Fintype.Lattice

/-!
# Elementary building blocks

The base of the combinator algebra. Every declaration here is a `Bounds` certificate whose
`computes` field is `sorry`: no concrete multi-tape Turing machine is constructed anywhere in this
development, so the machines are assumed and only their *resource discipline* is checked.

That split is deliberate and is worth stating precisely: in each definition below the
`time`/`space`/`outSize` bounds, their monotonicity and the output-size proof are all genuinely
proved. The single assumed thing is the existence of the machine.

## The primitives

* `Bounds.id`, `Bounds.const`, `Bounds.fst`, `Bounds.snd`, `Bounds.headD`, `Bounds.tail` — no
  work tape at all: the machine copies part of its read-only input to its write-only output tape,
  and neither is charged for space. Skipping over a subtree needs a nesting counter, which is free
  precisely because `DataEncode.depth` bounds the depth by a constant of the type — see the
  `DataEncode` docstring.
* `Bounds.ofFintype` — a function between finite types is a lookup: constant time and no work tape.
* `Bounds.comp` — sequential composition; the intermediate result has to be materialised on a work
  tape, which is why `f`'s output size appears in the *space* bound.
* `Bounds.pair` — fan-out: run both machines on the same input and juxtapose their outputs. Time
  and space both **sum** (both results must coexist), unlike the `max` that a case split would
  give.
* `Bounds.cons` — fan-out fused with a cons, matching the `cons (h t : Prog)` node of
  [issue #611](https://github.com/leanprover/cslib/issues/611). This, rather than the unary
  `α × List α → List α`, is the primitive worth assuming: the unary version is `pair` followed by
  deleting one bracket, and falls out as `Bounds.consUncurried`.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

variable {α β γ : Type} [DataEncode α] [DataEncode β] [DataEncode γ]

namespace Bounds

/-- **Identity.** Copy the read-only input to the write-only output; no work tape is used, and
neither of those tapes is charged for space. -/
def id : Bounds (_root_.id : α → α) where
  time n := n + 2
  space _ := 0
  outSize n := n
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := monotone_id
  computes := sorry
  out_le _ := le_refl _

/-- **Constants.** Emit a fixed value; its size is a constant of the machine. -/
def const (b : β) : Bounds (fun _ : α => b) where
  time _ := (DataEncode.encode b).size + 2
  space _ := 0
  outSize _ := (DataEncode.encode b).size
  time_mono := monotone_const
  space_mono := monotone_const
  outSize_mono := monotone_const
  computes := sorry
  out_le _ := le_refl _

/-- **First projection.** Copy the first child of the input node to the output. -/
def fst : Bounds (Prod.fst : α × β → α) where
  time n := n + 2
  space _ := 0
  outSize n := n
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := monotone_id
  computes := sorry
  out_le p := by
    have h : (DataEncode.encode p).size
        = (DataEncode.encode p.1).size + (DataEncode.encode p.2).size + 2 :=
      DataEncode.size_pair _ _
    omega

/-- **Second projection.** -/
def snd : Bounds (Prod.snd : α × β → β) where
  time n := n + 2
  space _ := 0
  outSize n := n
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := monotone_id
  computes := sorry
  out_le p := by
    have h : (DataEncode.encode p).size
        = (DataEncode.encode p.1).size + (DataEncode.encode p.2).size + 2 :=
      DataEncode.size_pair _ _
    omega

/-- **Functions on a finite domain.** There are finitely many inputs, so the machine can decide
the answer from its state alone: constant time, no work tape. -/
def ofFintype [Fintype α] (f : α → β) : Bounds f where
  time _ := (Finset.univ.sup fun a : α =>
    (DataEncode.encode a).size + (DataEncode.encode (f a)).size) + 2
  space _ := 0
  outSize _ := Finset.univ.sup fun a : α => (DataEncode.encode (f a)).size
  time_mono := monotone_const
  space_mono := monotone_const
  outSize_mono := monotone_const
  computes := sorry
  out_le a := Finset.le_sup (f := fun x : α => (DataEncode.encode (f x)).size)
    (Finset.mem_univ a)

/-- **Sequential composition.** Run the machine for `f`, materialise its output on a work tape,
then run the machine for `g` on it — which is why `f`'s output size is charged to the space
bound and `g`'s bounds are evaluated at it. -/
def comp {f : α → β} {g : β → γ} (hg : Bounds g) (hf : Bounds f) : Bounds (g ∘ f) where
  time n := hf.time n + hg.time (hf.outSize n)
  space n := hf.space n + hg.space (hf.outSize n) + hf.outSize n
  outSize n := hg.outSize (hf.outSize n)
  time_mono := by
    intro a b h
    exact Nat.add_le_add (hf.time_mono h) (hg.time_mono (hf.outSize_mono h))
  space_mono := by
    intro a b h
    exact Nat.add_le_add
      (Nat.add_le_add (hf.space_mono h) (hg.space_mono (hf.outSize_mono h)))
      (hf.outSize_mono h)
  outSize_mono := by
    intro a b h
    exact hg.outSize_mono (hf.outSize_mono h)
  computes := sorry
  out_le a := le_trans (hg.out_le (f a)) (hg.outSize_mono (hf.out_le a))

/-- **Fan-out.** Run both machines on the same input and pair the results. Both outputs have to
coexist on tape, so time and space add rather than taking a maximum. -/
def pair {f : α → β} {g : α → γ} (hf : Bounds f) (hg : Bounds g) :
    Bounds (fun a => (f a, g a)) where
  time n := hf.time n + hg.time n + hf.outSize n + hg.outSize n
  space n := hf.space n + hg.space n + hf.outSize n + hg.outSize n
  outSize n := hf.outSize n + hg.outSize n + 2
  time_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hf.time_mono h) (hg.time_mono h))
      (hf.outSize_mono h)) (hg.outSize_mono h)
  space_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hf.space_mono h) (hg.space_mono h))
      (hf.outSize_mono h)) (hg.outSize_mono h)
  outSize_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (hf.outSize_mono h) (hg.outSize_mono h)) (le_refl 2)
  computes := sorry
  out_le a := by
    rw [DataEncode.size_pair]
    have := hf.out_le a
    have := hg.out_le a
    omega

/-- **Fan-out fused with a cons.** This is the `cons (h t : Prog)` node of issue #611, and the
list primitive worth assuming: the unary `α × List α → List α` is this composed with the
projections. Note the output size is *exactly* the sum — a cons cell costs no bracket of its
own beyond what the two parts already pay. -/
def cons {f : α → β} {g : α → List β} (hf : Bounds f) (hg : Bounds g) :
    Bounds (fun a => f a :: g a) where
  time n := hf.time n + hg.time n + hf.outSize n + hg.outSize n
  space n := hf.space n + hg.space n + hf.outSize n + hg.outSize n
  outSize n := hf.outSize n + hg.outSize n
  time_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hf.time_mono h) (hg.time_mono h))
      (hf.outSize_mono h)) (hg.outSize_mono h)
  space_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hf.space_mono h) (hg.space_mono h))
      (hf.outSize_mono h)) (hg.outSize_mono h)
  outSize_mono := fun _ _ h => Nat.add_le_add (hf.outSize_mono h) (hg.outSize_mono h)
  computes := sorry
  out_le a := by
    rw [DataEncode.size_cons]
    have := hf.out_le a
    have := hg.out_le a
    omega

/-- **Head with a default.** Copy the first child of the input node to the output, or the
default if there is none. The default's size is a constant of the machine, hence the `+` in the
output bound. -/
def headD (a₀ : α) : Bounds (fun xs : List α => xs.head?.getD a₀) where
  time n := n + 2
  space _ := 0
  outSize n := n + (DataEncode.encode a₀).size
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := fun _ _ h => Nat.add_le_add_right h _
  computes := sorry
  out_le xs := by
    cases xs with
    | nil => simp
    | cons x xs =>
      have h := DataEncode.size_mem_le (xs := x :: xs) (x := x) (by simp)
      simpa using by omega

/-- **`Option.getD`.** An `Option` encodes exactly like a list of length at most one, so this is
the same bracket surgery as `headD`. -/
def optionGetD (a₀ : α) : Bounds (fun o : Option α => o.getD a₀) where
  time n := n + 2
  space _ := 0
  outSize n := n + (DataEncode.encode a₀).size
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := fun _ _ h => Nat.add_le_add_right h _
  computes := sorry
  out_le o := by
    cases o with
    | none => simp
    | some x =>
      have h : (DataEncode.encode (some x)).size = (DataEncode.encode x).size + 2 :=
        DataEncode.size_some x
      simpa using by omega

/-- **Tail.** Drop the first child of the input node. -/
def tail : Bounds (fun xs : List α => xs.tail) where
  time n := n + 2
  space _ := 0
  outSize n := n
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := monotone_id
  computes := sorry
  out_le xs := by
    cases xs with
    | nil => simp
    | cons x xs =>
      have h := DataEncode.size_cons x xs
      have h2 := Data.two_le_size (DataEncode.encode x)
      simpa using by omega

/-- **Emptiness test.** Whether the input node has any children at all — one look at the tape,
no work space. -/
def isEmpty : Bounds (fun l : List α => l.isEmpty) where
  time n := n + 2
  space _ := 0
  outSize _ := 4
  time_mono := fun _ _ h => Nat.add_le_add_right h 2
  space_mono := monotone_const
  outSize_mono := monotone_const
  computes := sorry
  out_le l := DataEncode.size_bool _

/-- **Branching.** Evaluate the condition, then whichever branch it selects. `cond` is used
rather than `if` so that no `Decidable` instance travels with the statement. -/
def ite {c : α → Bool} {f g : α → β} (hc : Bounds c) (hf : Bounds f) (hg : Bounds g) :
    Bounds (fun a => cond (c a) (f a) (g a)) where
  time n := hc.time n + hf.time n + hg.time n
  space n := hc.space n + hf.space n + hg.space n
  outSize n := hf.outSize n + hg.outSize n
  time_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (hc.time_mono h) (hf.time_mono h)) (hg.time_mono h)
  space_mono := fun _ _ h =>
    Nat.add_le_add (Nat.add_le_add (hc.space_mono h) (hf.space_mono h)) (hg.space_mono h)
  outSize_mono := fun _ _ h => Nat.add_le_add (hf.outSize_mono h) (hg.outSize_mono h)
  computes := sorry
  out_le a := by
    have h1 := hf.out_le a
    have h2 := hg.out_le a
    cases c a
    · simp only [Bool.cond_false]; omega
    · simp only [Bool.cond_true]; omega

/-- The unary cons, derived: pair up the two projections and cons them. -/
def consUncurried : Bounds (fun p : β × List β => p.1 :: p.2) :=
  cons fst snd

/-- Swapping the components of a pair, derived from fan-out and the projections. -/
def swap : Bounds (fun p : α × β => (p.2, p.1)) :=
  pair snd fst

end Bounds

end MultiTapeTM

end Turing
