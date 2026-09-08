/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Ite
import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Option
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Tuple

namespace CslibTests

open Cslib Turing MultiTapeTM

/-- The Boolean `and` function is computable in constant time and zero space. -/
example : ∀ encIn encOut, ∃ c, ComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry Bool.and)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply computableInTimeAndSpace_of_finite

def fullAdder (a b carry : Bool) : Bool × Bool :=
  let sum := (a != b) != carry
  let newCarry := (a && b) || (carry && (a != b))
  (sum, newCarry)

/-- The binary full adder is computable in constant time and zero space. -/
example : ∀ encIn encOut, ∃ c, ComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (Function.uncurry fullAdder)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut
  apply computableInTimeAndSpace_of_finite

/-- Equality comparison to a constant is computable in constant time and zero space,
also for infinite domains. -/
example {α : Type*} [DecidableEq α] : ∀ encIn encOut out, ∃ c, ComputableInTimeAndSpace
    (encIn := encIn)
    (encOut := encOut)
    (fun a : α => a == out)
    (fun _ => c) (fun _ => 0) := by
  intro encIn encOut out
  refine computableInTimeAndSpace_of_exists_finite_ne ⟨false, ?_⟩
  exact Set.Finite.subset (Set.finite_singleton out) (by intro a ha; simp_all)

/-! ## Case analysis

The single primitive `computableInTimeAndSpace_match` covers all of them: it needs nothing of the
scrutinee's type beyond being finite, and `cond`, `ite` and `dite` are its instances at `Bool`. -/

/-- A conditional on a decidable predicate is computable as soon as the predicate is decided by a
machine and both branches are computable. Only the branch that is taken runs, hence the `max`. -/
example {α β : Type} {encIn : α ↪ List Bool} {encBool : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {p : α → Prop} [DecidablePred p] {f g : α → β} {tc sc tf sf tg sg : α → ℕ}
    (hp : ComputableInTimeAndSpace (fun a => decide (p a)) encIn encBool tc sc)
    (hf : ComputableInTimeAndSpace f encIn encOut tf sf)
    (hg : ComputableInTimeAndSpace g encIn encOut tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun a => if p a then f a else g a) encIn encOut
      (fun a => c * (tc a + max (tf a) (tg a) + 1))
      (fun a => c * (sc a + max (sf a) (sg a) + 1)) :=
  computableInTimeAndSpace_ite hp hf hg

/-- A `match` on a finite inductive type is computable as soon as the scrutinee and every branch
are — here on `Ordering`, the result of a `compare`. Nothing about the type is needed beyond
`Finite`. The scrutinee and the branches share one pair of bounds, which costs nothing: separate
bounds are weakened to a common one, as here where the scrutinee's and the branches' are added.
Testing which constructor the scrutinee is costs no space beyond the scrutinee's own, since a
finite type has only finitely many encodings and so the encoded scrutinee is of constant length. -/
example {α β : Type} {encIn : α ↪ List Bool} {encO : Ordering ↪ List Bool}
    {encOut : β ↪ List Bool}
    {sel : α → Ordering} {onLt onEq onGt : α → β} {tsel ssel t s : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn encO tsel ssel)
    (hlt : ComputableInTimeAndSpace onLt encIn encOut t s)
    (heq : ComputableInTimeAndSpace onEq encIn encOut t s)
    (hgt : ComputableInTimeAndSpace onGt encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace
      (fun a => match sel a with
        | .lt => onLt a
        | .eq => onEq a
        | .gt => onGt a)
      encIn encOut
      (fun a => c * (tsel a + t a + 1))
      (fun a => c * (ssel a + s a + 1)) := by
  have hweak : ∀ g : α → β, ComputableInTimeAndSpace g encIn encOut t s →
      ComputableInTimeAndSpace g encIn encOut (fun a => tsel a + t a) (fun a => ssel a + s a) :=
    fun _ h => h.mono (fun a => Nat.le_add_left _ _) (fun a => Nat.le_add_left _ _)
  have hbr : ∀ i : Ordering, ComputableInTimeAndSpace
      (fun a => match i with | .lt => onLt a | .eq => onEq a | .gt => onGt a)
      encIn encOut (fun a => tsel a + t a) (fun a => ssel a + s a) := by
    intro i
    cases i
    exacts [hweak _ hlt, hweak _ heq, hweak _ hgt]
  exact computableInTimeAndSpace_match (Set.toFinite _) (fun _ => rfl)
    (hsel.mono (fun a => Nat.le_add_right _ _) (fun a => Nat.le_add_right _ _)) fun i _ => hbr i

/-- Branches of *different* result types need no dependent version of the combinator: the output
type is the sigma, and the case analysis is the same theorem instantiated at it. What makes this
work is that computability depends only on the encoded strings, not on the types they encode, so
the eliminator's `motive` has no computational content. -/
example {α ι : Type} [Finite ι] {β : ι → Type}
    {sel : α → ι} {br : (i : ι) → α → β i}
    {encIn : α ↪ List Bool} {encι : ι ↪ List Bool} {encS : (Σ i, β i) ↪ List Bool}
    {t s : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn encι t s)
    (hbr : ∀ i, ComputableInTimeAndSpace (fun a => (⟨i, br i a⟩ : Σ i, β i)) encIn encS t s) :
    ∃ c, ComputableInTimeAndSpace (fun a => (⟨sel a, br (sel a) a⟩ : Σ i, β i)) encIn encS
      (fun a => c * (t a + 1)) (fun a => c * (s a + 1)) :=
  computableInTimeAndSpace_match (br := fun i a => (⟨i, br i a⟩ : Σ i, β i))
    (Set.toFinite _) (fun _ => rfl) hsel fun i _ => hbr i

/-! ## Constructors

Dually to the eliminator, a constructor of a non-recursive inductive type is the introduction rule
of a finite product, so it is `computableInTimeAndSpace_concat` nested once per field. Unlike the
eliminator, every field is computed, so the fields contribute their sum rather than their maximum;
and unlike the eliminator, nothing is required of the encoding beyond that it be the concatenation
of the encoded fields. -/

/-- A two-field constructor carrying data from an infinite type. -/
structure Interval where
  lo : ℕ
  hi : ℕ

example {α : Type} {encIn : α ↪ List Bool} {encN : ℕ ↪ List Bool} {encI : Interval ↪ List Bool}
    {lo hi : α → ℕ} {tl sl th sh : α → ℕ}
    (henc : ∀ a, encI ⟨lo a, hi a⟩ = encN (lo a) ++ encN (hi a))
    (hlo : ComputableInTimeAndSpace lo encIn encN tl sl)
    (hhi : ComputableInTimeAndSpace hi encIn encN th sh) :
    ∃ c, ComputableInTimeAndSpace (fun a => (⟨lo a, hi a⟩ : Interval)) encIn encI
      (fun a => c * (tl a + th a + (encIn a).length + 1))
      (fun a => c * (sl a + sh a + 1)) := by
  exact computableInTimeAndSpace_ctor (A := fun _ : Fin 2 => ℕ) (fs := ![lo, hi])
    (encIn := encIn) (encA := fun _ => encN)
    (t := fun a => tl a + th a) (s := fun a => sl a + sh a)
    (fun a => by simpa [List.ofFn_succ] using henc a)
    (Fin.forall_fin_two.mpr
      ⟨by simpa using hlo.mono (fun a => by omega) (fun a => by omega),
        by simpa using hhi.mono (fun a => by omega) (fun a => by omega)⟩)

/-- `Option.some`, at the canonical encoding of `Encodings.Option`. A tagged constructor is built
by treating the tag as a field computed by a constant function, so nothing beyond
`computableInTimeAndSpace_concat` is involved. -/
example {α : Type} {enc : α ↪ List Bool} :
    ∃ c, ComputableInTimeAndSpace (fun a => (some a : Option α)) enc (encOption enc)
      (fun a => c * ((enc a).length + 1)) (fun _ => c) := by
  obtain ⟨c₁, h₁⟩ := computableInTimeAndSpace_of_const (α := α) (encIn := enc)
    (encOut := (⟨fun _ => [true], fun a b _ => Subsingleton.elim a b⟩ : Unit ↪ List Bool)) ()
  obtain ⟨c₂, h₂⟩ := computableInTimeAndSpace_id (α := α) (enc := enc)
  obtain ⟨c₃, h₃⟩ := computableInTimeAndSpace_concat (h := fun a => (some a : Option α))
    (encD := encOption enc) (fun _ => rfl) h₁ h₂
  refine ⟨c₁ + c₂ + c₃ + 3, h₃.mono (fun a => ?_) (fun a => by omega)⟩
  have hexp : (c₁ + c₂ + c₃ + 3) * ((enc a).length + 1)
      = c₁ * ((enc a).length + 1) + c₂ * ((enc a).length + 1) + c₃ * ((enc a).length + 1)
        + 3 * ((enc a).length + 1) := by ring
  have h1 : c₁ ≤ c₁ * ((enc a).length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- A subtype constructor costs nothing at all: the proof field is erased, so the encoding of the
constructed value *is* the encoding of the data field, and the whole constructor is a change of
coordinates — `ComputableInTimeAndSpace.congr`, with no combinator involved. -/
example {α β : Type} {p : β → Prop} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encS : {x // p x} ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (hp : ∀ a, p (f a)) (henc : ∀ x : {x // p x}, encS x = encB x.val)
    (hf : ComputableInTimeAndSpace f encIn encB t s) :
    ComputableInTimeAndSpace (fun a => (⟨f a, hp a⟩ : {x // p x})) encIn encS t s :=
  hf.congr (fun _ => rfl) fun _ => henc _

/-- Three fields of different types, encoded flat rather than as nested pairs. The index family of
`computableInTimeAndSpace_ctor` is dependent, which is awkward when the fields have different
types; the `List Bool`-valued `computableInTimeAndSpace_flatten` avoids it — encode each field,
concatenate, and read the result back with `ComputableInTimeAndSpace.congr`. -/
example {α : Type} {encIn : α ↪ List Bool} {encN : ℕ ↪ List Bool} {encB : Bool ↪ List Bool}
    {encT : ℕ × Bool × ℕ ↪ List Bool} {f h : α → ℕ} {g : α → Bool} {t₁ s₁ t₂ s₂ t₃ s₃ : α → ℕ}
    (henc : ∀ a, encT (f a, g a, h a) = encN (f a) ++ encB (g a) ++ encN (h a))
    (hf : ComputableInTimeAndSpace f encIn encN t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn encB t₂ s₂)
    (hh : ComputableInTimeAndSpace h encIn encN t₃ s₃) :
    ∃ c, ComputableInTimeAndSpace (fun a => (f a, g a, h a)) encIn encT
      (fun a => c * (t₁ a + t₂ a + t₃ a + (encIn a).length + 1))
      (fun a => c * (s₁ a + s₂ a + s₃ a + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_flatten (encIn := encIn)
    (fs := ![fun a => encN (f a), fun a => encB (g a), fun a => encN (h a)])
    (t := fun a => t₁ a + t₂ a + t₃ a) (s := fun a => s₁ a + s₂ a + s₃ a)
    (by
      intro j
      fin_cases j
      · exact (hf.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega)
      · exact (hg.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega)
      · exact (hh.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega))
  exact ⟨c, hc.congr (fun _ => rfl) (fun a => by simpa [List.ofFn_succ] using henc a)⟩

/-! ## A proper inductive type

`Shape` has several alternatives of different arities, two of them carrying data from an infinite
type. Its constructors are covered by the combinators below; its eliminator is covered as far as
the tag, and no further — see the last example. -/

/-- Three alternatives, of arities zero, one and two. -/
inductive Shape
  | point
  | circle (r : ℕ)
  | rect (w h : ℕ)
deriving DecidableEq

/-- Which alternative a shape is. -/
def Shape.tag : Shape → Fin 3
  | .point => 0
  | .circle _ => 1
  | .rect _ _ => 2

section Shape

variable {α : Type} {encIn : α ↪ List Bool} {encN : ℕ ↪ List Bool} {encS : Shape ↪ List Bool}

/-- A nullary constructor is a constant, so it needs nothing at all of the encoding. -/
example : ∃ c, ComputableInTimeAndSpace (fun _ : α => Shape.point) encIn encS
    (fun _ => c) (fun _ => 0) :=
  computableInTimeAndSpace_of_const _

/-- A constructor with one field. The two-bit tag is a field computed by a constant function, so
this is one `computableInTimeAndSpace_concat` and nothing else. -/
example {f : α → ℕ} {t s : α → ℕ}
    (henc : ∀ r, encS (.circle r) = [false, true] ++ encN r)
    (hf : ComputableInTimeAndSpace f encIn encN t s) :
    ∃ c, ComputableInTimeAndSpace (fun a => Shape.circle (f a)) encIn encS
      (fun a => c * (t a + (encIn a).length + 1)) (fun a => c * (s a + 1)) := by
  obtain ⟨c₁, h₁⟩ := computableInTimeAndSpace_of_const (α := α) (encIn := encIn)
    (encOut := (⟨fun _ => [false, true], fun a b _ => Subsingleton.elim a b⟩ : Unit ↪ List Bool)) ()
  obtain ⟨c₂, h₂⟩ := computableInTimeAndSpace_concat (h := fun a => Shape.circle (f a))
    (encD := encS) (fun a => henc (f a)) h₁ hf
  refine ⟨c₁ + c₂ + 3, h₂.mono (fun a => ?_) (fun a => ?_)⟩
  · have hexp : (c₁ + c₂ + 3) * (t a + (encIn a).length + 1)
        = c₁ * (t a + (encIn a).length + 1) + c₂ * (t a + (encIn a).length + 1)
          + 3 * (t a + (encIn a).length + 1) := by ring
    have h1 : c₁ ≤ c₁ * (t a + (encIn a).length + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hexp : (c₁ + c₂ + 3) * (s a + 1)
        = c₁ * (s a + 1) + c₂ * (s a + 1) + 3 * (s a + 1) := by ring
    have h2 : c₂ ≤ c₂ * (s a + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- A constructor with two fields: the tag and the two fields are three computations whose outputs
are concatenated, so `computableInTimeAndSpace_flatten` applies directly and there is no need to
nest pairs. -/
example {f g : α → ℕ} {tf sf tg sg : α → ℕ}
    (henc : ∀ w h, encS (.rect w h) = [true, false] ++ encN w ++ encN h)
    (hf : ComputableInTimeAndSpace f encIn encN tf sf)
    (hg : ComputableInTimeAndSpace g encIn encN tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun a => Shape.rect (f a) (g a)) encIn encS
      (fun a => c * (tf a + tg a + (encIn a).length + 1))
      (fun a => c * (sf a + sg a + 1)) := by
  obtain ⟨c₀, h₀⟩ := computableInTimeAndSpace_of_const (α := α) (encIn := encIn)
    (encOut := Function.Embedding.refl (List Bool)) ([true, false] : List Bool)
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_flatten (encIn := encIn)
    (fs := ![fun _ => [true, false], fun a => encN (f a), fun a => encN (g a)])
    (t := fun a => c₀ + tf a + tg a) (s := fun a => sf a + sg a)
    (by
      intro j
      fin_cases j
      · exact h₀.mono (fun a => by omega) (fun a => by omega)
      · exact (hf.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega)
      · exact (hg.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega))
  refine ⟨c * (c₀ + 1), ((hc.congr (fun _ => rfl)
    (fun a => by simpa [List.ofFn_succ] using henc (f a) (g a))).mono (fun a => ?_)
      (fun a => ?_))⟩
  · calc c * (c₀ + tf a + tg a + (encIn a).length + 1)
        ≤ c * ((c₀ + 1) * (tf a + tg a + (encIn a).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : c₀ ≤ c₀ * (tf a + tg a + (encIn a).length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          have h2 : (c₀ + 1) * (tf a + tg a + (encIn a).length + 1)
              = c₀ * (tf a + tg a + (encIn a).length + 1)
                + (tf a + tg a + (encIn a).length + 1) := by ring
          omega
      _ = c * (c₀ + 1) * (tf a + tg a + (encIn a).length + 1) := by ring
  · exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))

/-- Matching on a type with several alternatives, as far as the tag. Given that the alternative can
be read off — which is a requirement on the encoding, not something derivable, and the one piece
`Encodings/` would have to supply for a general type — the `match` is
`computableInTimeAndSpace_match` at the tag.

Branches that *use* a constructor's fields need more: a computable destructor per constructor, and
pairing to hand the branch both the original input and the extracted payload. Those are the two
things still missing, and they are requirements on the encoding rather than combinators. -/
example {β : Type} {encF : Fin 3 ↪ List Bool} {encOut : β ↪ List Bool}
    {sel : α → Shape} {onPoint onCircle onRect : α → β} {tsel ssel t s : α → ℕ}
    (htag : ComputableInTimeAndSpace (fun a => (sel a).tag) encIn encF tsel ssel)
    (hp : ComputableInTimeAndSpace onPoint encIn encOut t s)
    (hc : ComputableInTimeAndSpace onCircle encIn encOut t s)
    (hr : ComputableInTimeAndSpace onRect encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace
      (fun a => match sel a with
        | .point => onPoint a
        | .circle _ => onCircle a
        | .rect _ _ => onRect a)
      encIn encOut
      (fun a => c * (tsel a + t a + 1)) (fun a => c * (ssel a + s a + 1)) := by
  have hweak : ∀ g : α → β, ComputableInTimeAndSpace g encIn encOut t s →
      ComputableInTimeAndSpace g encIn encOut (fun a => tsel a + t a) (fun a => ssel a + s a) :=
    fun _ h => h.mono (fun a => Nat.le_add_left _ _) (fun a => Nat.le_add_left _ _)
  have hbr : ∀ i : Fin 3, ComputableInTimeAndSpace (![onPoint, onCircle, onRect] i)
      encIn encOut (fun a => tsel a + t a) (fun a => ssel a + s a) := by
    intro i
    fin_cases i
    · exact hweak _ hp
    · exact hweak _ hc
    · exact hweak _ hr
  exact computableInTimeAndSpace_match (Set.toFinite _) (fun a => by cases sel a <;> rfl)
    (htag.mono (fun a => Nat.le_add_right _ _) (fun a => Nat.le_add_right _ _)) fun i _ => hbr i

/-- The payload of `circle`, and of anything else by convention. -/
def Shape.r : Shape → ℕ
  | .circle r => r
  | _ => 0

/-- The first payload of `rect`, and of anything else by convention. -/
def Shape.w : Shape → ℕ
  | .rect w _ => w
  | _ => 0

/-- The second payload of `rect`, and of anything else by convention. -/
def Shape.h : Shape → ℕ
  | .rect _ h => h
  | _ => 0

/-- **A destructuring `match` whose branches need junk.** `Span`'s alternatives all have arity two,
so its fields are total functions and nothing is invented. `Shape`'s have arities zero, one and
two, so `Shape.r` has to return something on a `rect` and `Shape.w` on a `circle`, and the value
chosen — `0` here — is arbitrary.

That is exactly what `hagree` licenses. The `circle` branch reads `Shape.w`'s junk nowhere, because
it is only ever run where the scrutinee is a `circle`, and the hypothesis only asks the branches to
agree with the `match` where they are taken. A version of the combinator demanding the branches
equal the `match` everywhere could not be applied here at all: off its own alternative each branch
computes something the `match` never returns.

Note the branch family is written `fun a => ![…] i` and not `![…] i` with the input abstracted
inside each entry. The two are equal by `funext`, but only in the first does the scrutinee occur
applied to the outer variable, and `cases` cannot generalise it under a binder — with the other
spelling `hagree` is no longer `rfl`. -/
example {β : Type} {encF : Fin 3 ↪ List Bool} {encOut : β ↪ List Bool}
    {sel : α → Shape} {onPoint : α → β} {onCircle : α → ℕ → β} {onRect : α → ℕ → ℕ → β}
    {t s : α → ℕ}
    (htag : ComputableInTimeAndSpace (fun a => (sel a).tag) encIn encF t s)
    (hbr : ∀ i : Fin 3, ComputableInTimeAndSpace
      (fun a => ![onPoint a, onCircle a (sel a).r, onRect a (sel a).w (sel a).h] i)
      encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace
      (fun a => match sel a with
        | .point => onPoint a
        | .circle r => onCircle a r
        | .rect w h => onRect a w h)
      encIn encOut
      (fun a => c * (t a + 1)) (fun a => c * (s a + 1)) :=
  computableInTimeAndSpace_match (Set.toFinite _) (fun a => by cases sel a <;> rfl) htag
    fun i _ => hbr i

end Shape

/-! ## Several alternatives of the same arity

`Shape` has only one constructor of arity two. `Span` has two, which is the case where the tag is
doing real work: the two alternatives are indistinguishable by their payload and only the tag tells
them apart. Each is built the same way — the tag and the two fields are three computations whose
outputs are concatenated — so the construction is shared and only the tag and the constructor
differ. -/

/-- Two alternatives, each carrying two fields. -/
inductive Span
  | ofLength (start len : ℕ)
  | ofBounds (lo hi : ℕ)
deriving DecidableEq

/-- Either alternative of `Span`, built from the tag and the two fields. -/
private theorem span_ctor {α : Type} {encIn : α ↪ List Bool} {encN : ℕ ↪ List Bool}
    {encS : Span ↪ List Bool} {f g : α → ℕ} {tf sf tg sg : α → ℕ}
    (tag : List Bool) (mk : ℕ → ℕ → Span)
    (henc : ∀ u v, encS (mk u v) = tag ++ encN u ++ encN v)
    (hf : ComputableInTimeAndSpace f encIn encN tf sf)
    (hg : ComputableInTimeAndSpace g encIn encN tg sg) :
    ∃ c, ComputableInTimeAndSpace (fun a => mk (f a) (g a)) encIn encS
      (fun a => c * (tf a + tg a + (encIn a).length + 1))
      (fun a => c * (sf a + sg a + 1)) := by
  obtain ⟨c₀, h₀⟩ := computableInTimeAndSpace_of_const (α := α) (encIn := encIn)
    (encOut := Function.Embedding.refl (List Bool)) tag
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_flatten (encIn := encIn)
    (fs := ![fun _ => tag, fun a => encN (f a), fun a => encN (g a)])
    (t := fun a => c₀ + tf a + tg a) (s := fun a => sf a + sg a)
    (by
      intro j
      fin_cases j
      · exact h₀.mono (fun a => by omega) (fun a => by omega)
      · exact (hf.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega)
      · exact (hg.congr (fun _ => rfl) fun _ => rfl).mono (fun a => by omega) (fun a => by omega))
  refine ⟨c * (c₀ + 1), ((hc.congr (fun _ => rfl)
    (fun a => by simpa [List.ofFn_succ] using henc (f a) (g a))).mono (fun a => ?_)
      (fun a => ?_))⟩
  · calc c * (c₀ + tf a + tg a + (encIn a).length + 1)
        ≤ c * ((c₀ + 1) * (tf a + tg a + (encIn a).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : c₀ ≤ c₀ * (tf a + tg a + (encIn a).length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          have h2 : (c₀ + 1) * (tf a + tg a + (encIn a).length + 1)
              = c₀ * (tf a + tg a + (encIn a).length + 1)
                + (tf a + tg a + (encIn a).length + 1) := by ring
          omega
      _ = c * (c₀ + 1) * (tf a + tg a + (encIn a).length + 1) := by ring
  · exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))

/-- A function into a type with two two-field alternatives, choosing between them. The case
analysis picks the constructor and each branch builds one, so this is `computableInTimeAndSpace_ite`
over two instances of the constructor pattern; only the branch that is taken is built, hence the
single copy of the field bounds. -/
example {α : Type} {encIn : α ↪ List Bool} {encN : ℕ ↪ List Bool} {encS : Span ↪ List Bool}
    {encBool : Bool ↪ List Bool} {sel : α → Bool} {f g : α → ℕ} {tc sc tf sf tg sg : α → ℕ}
    (hlen : ∀ u v, encS (.ofLength u v) = [false] ++ encN u ++ encN v)
    (hbnd : ∀ u v, encS (.ofBounds u v) = [true] ++ encN u ++ encN v)
    (hsel : ComputableInTimeAndSpace sel encIn encBool tc sc)
    (hf : ComputableInTimeAndSpace f encIn encN tf sf)
    (hg : ComputableInTimeAndSpace g encIn encN tg sg) :
    ∃ c, ComputableInTimeAndSpace
      (fun a => if sel a then Span.ofLength (f a) (g a) else Span.ofBounds (f a) (g a))
      encIn encS
      (fun a => c * (tc a + tf a + tg a + (encIn a).length + 1))
      (fun a => c * (sc a + sf a + sg a + 1)) := by
  obtain ⟨c₁, h₁⟩ := span_ctor [false] Span.ofLength hlen hf hg
  obtain ⟨c₂, h₂⟩ := span_ctor [true] Span.ofBounds hbnd hf hg
  obtain ⟨c₃, h₃⟩ := computableInTimeAndSpace_cond hsel h₁ h₂
  refine ⟨c₃ * (c₁ + c₂ + 2), h₃.mono (fun a => ?_) (fun a => ?_)⟩
  · have hmax : max (c₁ * (tf a + tg a + (encIn a).length + 1))
          (c₂ * (tf a + tg a + (encIn a).length + 1))
        ≤ (c₁ + c₂) * (tc a + tf a + tg a + (encIn a).length + 1) := by
      have e : (c₁ + c₂) * (tc a + tf a + tg a + (encIn a).length + 1)
          = c₁ * (tc a + tf a + tg a + (encIn a).length + 1)
            + c₂ * (tc a + tf a + tg a + (encIn a).length + 1) := by ring
      have e₁ : c₁ * (tf a + tg a + (encIn a).length + 1)
          ≤ c₁ * (tc a + tf a + tg a + (encIn a).length + 1) := Nat.mul_le_mul_left _ (by omega)
      have e₂ : c₂ * (tf a + tg a + (encIn a).length + 1)
          ≤ c₂ * (tc a + tf a + tg a + (encIn a).length + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    calc c₃ * (tc a + max (c₁ * (tf a + tg a + (encIn a).length + 1))
            (c₂ * (tf a + tg a + (encIn a).length + 1)) + 1)
        ≤ c₃ * ((c₁ + c₂ + 2) * (tc a + tf a + tg a + (encIn a).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have e : (c₁ + c₂ + 2) * (tc a + tf a + tg a + (encIn a).length + 1)
              = (c₁ + c₂) * (tc a + tf a + tg a + (encIn a).length + 1)
                + 2 * (tc a + tf a + tg a + (encIn a).length + 1) := by ring
          omega
      _ = c₃ * (c₁ + c₂ + 2) * (tc a + tf a + tg a + (encIn a).length + 1) := by ring
  · have hmax : max (c₁ * (sf a + sg a + 1)) (c₂ * (sf a + sg a + 1))
        ≤ (c₁ + c₂) * (sc a + sf a + sg a + 1) := by
      have e : (c₁ + c₂) * (sc a + sf a + sg a + 1)
          = c₁ * (sc a + sf a + sg a + 1) + c₂ * (sc a + sf a + sg a + 1) := by ring
      have e₁ : c₁ * (sf a + sg a + 1) ≤ c₁ * (sc a + sf a + sg a + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have e₂ : c₂ * (sf a + sg a + 1) ≤ c₂ * (sc a + sf a + sg a + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    calc c₃ * (sc a + max (c₁ * (sf a + sg a + 1)) (c₂ * (sf a + sg a + 1)) + 1)
        ≤ c₃ * ((c₁ + c₂ + 2) * (sc a + sf a + sg a + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have e : (c₁ + c₂ + 2) * (sc a + sf a + sg a + 1)
              = (c₁ + c₂) * (sc a + sf a + sg a + 1)
                + 2 * (sc a + sf a + sg a + 1) := by ring
          omega
      _ = c₃ * (c₁ + c₂ + 2) * (sc a + sf a + sg a + 1) := by ring

/-- Which alternative a span is. -/
def Span.tag : Span → Bool
  | .ofLength .. => false
  | .ofBounds .. => true

/-- The first field of either alternative. Total, because *both* alternatives carry two naturals,
which is what makes a destructuring `match` on `Span` expressible without any junk: a branch may
read the fields of the alternative it is not in, since it is never run there — but here it does
not even have to. -/
def Span.fst : Span → ℕ
  | .ofLength u _ => u
  | .ofBounds u _ => u

/-- The second field of either alternative. -/
def Span.snd : Span → ℕ
  | .ofLength _ v => v
  | .ofBounds _ v => v

/-- **The eliminator of a type with two alternatives of arity two, destructuring.** The branches
here do not ignore the payload as they do for `Shape`: each receives both fields of the alternative
it matched, which is the case the combinator was supposed to cover and had not been checked on.

It goes through unchanged. The branch family is indexed by the tag and each branch is the total
function reading both fields, so `hagree` is the whole content of the destructuring, and it is
`rfl` once the scrutinee is case split — the projections agree with the pattern variables by
definition of the projections.

The scrutinee is the input itself, so this is `Span`'s eliminator and nothing more; matching on a
scrutinee *computed* from some other input is the same theorem with `sel` in front, as in the
`Shape` examples.

The two hypotheses are the whole of what a type has to supply. `htag` says the alternative can be
read off, which is a requirement on `encS` and the one thing no combinator can provide. `hbr` says
a branch is computable as a function of the value being matched rather than of its payload, and
that is a computable destructor per field composed with the branch — pairing the two fields, since
the branch is binary. Both are requirements on the encoding, not further combinators. -/
example {β : Type} {encS : Span ↪ List Bool} {encB : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {onLength onBounds : ℕ → ℕ → β} {t s : Span → ℕ}
    (htag : ComputableInTimeAndSpace Span.tag encS encB t s)
    (hbr : ∀ b : Bool, ComputableInTimeAndSpace
      (fun x => (bif b then onBounds else onLength) x.fst x.snd) encS encOut t s) :
    ∃ c, ComputableInTimeAndSpace
      (fun x => match x with
        | .ofLength u v => onLength u v
        | .ofBounds u v => onBounds u v)
      encS encOut
      (fun x => c * (t x + 1)) (fun x => c * (s x + 1)) :=
  computableInTimeAndSpace_match (Set.toFinite _) (fun x => by cases x <;> rfl) htag
    fun b _ => hbr b

/-- **The selector Lean already provides.** `Span.tag` above was written by hand, but every
inductive type comes with `ctorIdx`, generated from `casesOn`, which is the same map read into `ℕ`.
It serves as the scrutinee directly. That is what makes the combinator mechanisable: a tactic
cannot invent a bespoke tag type for an arbitrary inductive, but `ctorIdx` is always there, and the
side conditions — that its range is finite, and that the branches agree — are both discharged by
case analysis on the scrutinee.

The price of landing in `ℕ` is that the branch family is indexed by `ℕ` too, so all but two of its
members are junk. That is why only the branches in the range of the selector are asked to be
computable; over all of `ℕ` the hypothesis would be unsatisfiable for any nonconstant bound. -/
example {β : Type} {encS : Span ↪ List Bool} {encN : ℕ ↪ List Bool} {encOut : β ↪ List Bool}
    {onLength onBounds : ℕ → ℕ → β} {t s : Span → ℕ}
    (hidx : ComputableInTimeAndSpace Span.ctorIdx encS encN t s)
    (h₀ : ComputableInTimeAndSpace (fun x : Span => onLength x.fst x.snd) encS encOut t s)
    (h₁ : ComputableInTimeAndSpace (fun x : Span => onBounds x.fst x.snd) encS encOut t s) :
    ∃ c, ComputableInTimeAndSpace
      (fun x => match x with
        | .ofLength u v => onLength u v
        | .ofBounds u v => onBounds u v)
      encS encOut
      (fun x => c * (t x + 1)) (fun x => c * (s x + 1)) := by
  refine computableInTimeAndSpace_match
    (br := fun i x => bif i == 0 then onLength x.fst x.snd else onBounds x.fst x.snd)
    (((Set.finite_singleton 1).insert 0).subset ?_) (fun x => by cases x <;> rfl) hidx ?_
  · rintro _ ⟨x, rfl⟩
    cases x
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  · rintro _ ⟨x, rfl⟩
    cases x
    · exact h₀
    · exact h₁

end CslibTests
