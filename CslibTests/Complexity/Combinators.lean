/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
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

Lean's `ite` is `Bool.rec` once the `Decidable` instance is erased, and a `match` on a finite
inductive type is `Bool.rec` nested once per constructor. So the single primitive
`computableInTimeAndSpace_cond` covers all of them, and the derived
`computableInTimeAndSpace_match` needs nothing of the scrutinee's type beyond being finite. -/

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
are — here on `Ordering`, the result of a `compare`. Only the branch that is taken runs, so the
branches contribute their maximum rather than their sum, and nothing about the type is needed
beyond `Fintype`. Testing which constructor the scrutinee
is costs no space beyond the scrutinee's own, since a finite type has only finitely many encodings
and so the encoded scrutinee is of constant length. -/
example {α β : Type} {encIn : α ↪ List Bool} {encO : Ordering ↪ List Bool}
    {encBool : Bool ↪ List Bool} {encOut : β ↪ List Bool}
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
  have hbr : ∀ i : Ordering, ComputableInTimeAndSpace
      (fun a => match i with | .lt => onLt a | .eq => onEq a | .gt => onGt a)
      encIn encOut t s := by
    intro i
    cases i <;> assumption
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_match (encCond := encBool) hsel hbr
  have hsupt : ∀ a, Finset.univ.sup (fun _ : Ordering => t a) ≤ t a :=
    fun a => Finset.sup_le fun _ _ => le_rfl
  have hsups : ∀ a, Finset.univ.sup (fun _ : Ordering => s a) ≤ s a :=
    fun a => Finset.sup_le fun _ _ => le_rfl
  refine ⟨c, hc.mono (fun a => Nat.mul_le_mul_left _ (by have := hsupt a; omega))
    (fun a => Nat.mul_le_mul_left _ (by have := hsups a; omega))⟩

/-- Branches of *different* result types need no dependent version of the combinator: the output
type is the sigma, and the case analysis is the same theorem instantiated at it. What makes this
work is that computability depends only on the encoded strings, not on the types they encode, so
the eliminator's `motive` has no computational content. -/
example {α ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type}
    {sel : α → ι} {br : (i : ι) → α → β i}
    {encIn : α ↪ List Bool} {encBool : Bool ↪ List Bool} {encS : (Σ i, β i) ↪ List Bool}
    {tc sc t s : ι → α → ℕ}
    (htest : ∀ i, ComputableInTimeAndSpace (fun a => decide (sel a = i)) encIn encBool
      (tc i) (sc i))
    (hbr : ∀ i, ComputableInTimeAndSpace (fun a => (⟨i, br i a⟩ : Σ i, β i)) encIn encS
      (t i) (s i)) :
    ∃ c, ComputableInTimeAndSpace (fun a => (⟨sel a, br (sel a) a⟩ : Σ i, β i)) encIn encS
      (fun a => c * (Finset.univ.sup (fun i => tc i a) + Finset.univ.sup (fun i => t i a) + 1))
      (fun a => c * (Finset.univ.sup (fun i => sc i a)
        + Finset.univ.sup (fun i => s i a) + 1)) :=
  computableInTimeAndSpace_casesOn (br := fun i a => (⟨i, br i a⟩ : Σ i, β i))
    (fun i a h => by rw [h]) htest hbr

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
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_ctor (A := fun _ : Fin 2 => ℕ) (fs := ![lo, hi])
    (encIn := encIn) (encA := fun _ => encN) (t := ![tl, th]) (s := ![sl, sh])
    (fun a => by simpa [List.ofFn_succ] using henc a)
    (Fin.forall_fin_two.mpr ⟨by simpa using hlo, by simpa using hhi⟩)
  exact ⟨c, hc.mono (fun a => by simp [Fin.sum_univ_two]) (fun a => by simp [Fin.sum_univ_two])⟩

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
    (t := ![t₁, t₂, t₃]) (s := ![s₁, s₂, s₃])
    (by
      intro j
      fin_cases j
      · exact hf.congr (fun _ => rfl) fun _ => rfl
      · exact hg.congr (fun _ => rfl) fun _ => rfl
      · exact hh.congr (fun _ => rfl) fun _ => rfl)
  refine ⟨c, (hc.congr (fun _ => rfl) (fun a => by simpa [List.ofFn_succ] using henc a)).mono
    (fun a => by simp [Fin.sum_univ_three]) (fun a => by simp [Fin.sum_univ_three])⟩

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
    (t := ![fun _ => c₀, tf, tg]) (s := ![fun _ => 0, sf, sg])
    (by
      intro j
      fin_cases j
      · exact h₀
      · exact hf.congr (fun _ => rfl) fun _ => rfl
      · exact hg.congr (fun _ => rfl) fun _ => rfl)
  refine ⟨c * (c₀ + 1), ((hc.congr (fun _ => rfl)
    (fun a => by simpa [List.ofFn_succ] using henc (f a) (g a))).mono (fun a => ?_)
      (fun a => ?_))⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    calc c * (c₀ + tf a + tg a + (encIn a).length + 1)
        ≤ c * ((c₀ + 1) * (tf a + tg a + (encIn a).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : c₀ ≤ c₀ * (tf a + tg a + (encIn a).length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          have h2 : (c₀ + 1) * (tf a + tg a + (encIn a).length + 1)
              = c₀ * (tf a + tg a + (encIn a).length + 1)
                + (tf a + tg a + (encIn a).length + 1) := by ring
          omega
      _ = c * (c₀ + 1) * (tf a + tg a + (encIn a).length + 1) := by ring
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    calc c * (0 + sf a + sg a + 1) = c * (sf a + sg a + 1) := by ring
      _ ≤ c * (c₀ + 1) * (sf a + sg a + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))

/-- Matching on a type with several alternatives, as far as the tag. Given that the alternative can
be read off — which is a requirement on the encoding, not something derivable, and the one piece
`Encodings/` would have to supply for a general type — the `match` is
`computableInTimeAndSpace_match` at the tag.

Branches that *use* a constructor's fields need more: a computable destructor per constructor, and
pairing to hand the branch both the original input and the extracted payload. Those are the two
things still missing, and they are requirements on the encoding rather than combinators. -/
example {β : Type} {encF : Fin 3 ↪ List Bool} {encBool : Bool ↪ List Bool} {encOut : β ↪ List Bool}
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
  have hbr : ∀ i : Fin 3, ComputableInTimeAndSpace (![onPoint, onCircle, onRect] i)
      encIn encOut t s := by
    intro i
    fin_cases i
    · exact hp
    · exact hc
    · exact hr
  obtain ⟨c, hc'⟩ := computableInTimeAndSpace_match (encCond := encBool) htag hbr
  have hfun : (fun a => ![onPoint, onCircle, onRect] (sel a).tag a) =
      fun a => match sel a with
        | .point => onPoint a
        | .circle _ => onCircle a
        | .rect _ _ => onRect a := by
    funext a
    cases sel a <;> rfl
  rw [hfun] at hc'
  have hsupt : ∀ a, Finset.univ.sup (fun _ : Fin 3 => t a) ≤ t a :=
    fun a => Finset.sup_le fun _ _ => le_rfl
  have hsups : ∀ a, Finset.univ.sup (fun _ : Fin 3 => s a) ≤ s a :=
    fun a => Finset.sup_le fun _ _ => le_rfl
  exact ⟨c, hc'.mono (fun a => Nat.mul_le_mul_left _ (by have := hsupt a; omega))
    (fun a => Nat.mul_le_mul_left _ (by have := hsups a; omega))⟩

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
    (t := ![fun _ => c₀, tf, tg]) (s := ![fun _ => 0, sf, sg])
    (by
      intro j
      fin_cases j
      · exact h₀
      · exact hf.congr (fun _ => rfl) fun _ => rfl
      · exact hg.congr (fun _ => rfl) fun _ => rfl)
  refine ⟨c * (c₀ + 1), ((hc.congr (fun _ => rfl)
    (fun a => by simpa [List.ofFn_succ] using henc (f a) (g a))).mono (fun a => ?_)
      (fun a => ?_))⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    calc c * (c₀ + tf a + tg a + (encIn a).length + 1)
        ≤ c * ((c₀ + 1) * (tf a + tg a + (encIn a).length + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          have h1 : c₀ ≤ c₀ * (tf a + tg a + (encIn a).length + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          have h2 : (c₀ + 1) * (tf a + tg a + (encIn a).length + 1)
              = c₀ * (tf a + tg a + (encIn a).length + 1)
                + (tf a + tg a + (encIn a).length + 1) := by ring
          omega
      _ = c * (c₀ + 1) * (tf a + tg a + (encIn a).length + 1) := by ring
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    calc c * (0 + sf a + sg a + 1) = c * (sf a + sg a + 1) := by ring
      _ ≤ c * (c₀ + 1) * (sf a + sg a + 1) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))

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

end CslibTests
