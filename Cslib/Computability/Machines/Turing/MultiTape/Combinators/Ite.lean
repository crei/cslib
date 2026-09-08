/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Tactic.Ring
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp

/-!
# Complexity of a case analysis

Lean's `ite` is not primitive: `ite c t e` is `Decidable.casesOn`, the recursor of the two
constructor inductive `Decidable c`, and both of its constructors carry only proofs. Since `Prop`
is erased, the computational content of `ite` is therefore exactly the recursor of `Bool`,

```
cond (c : Bool) (x y : α) : α := match c with | true => x | false => y
```

and that is what `computableInTimeAndSpace_cond` is about. The `Decidable` layer contributes
nothing beyond a computable Boolean test, which is supplied as a hypothesis;
`computableInTimeAndSpace_ite` is the resulting statement about Lean's `ite`, and
`DecidableInTimeAndSpace` is the same test read as a decision procedure for a language.

## Why this has to be a combinator

`cond` is a perfectly ordinary computable *function*: as a map `Bool × β × β → β` it reads a tag
and streams out the component it selects, in linear time and no space. But that function does not
give the case analysis, because

```
fun a => if c a then f a else g a  =  cond ∘ (fun a => (c a, f a, g a))
```

computes *both* `f a` and `g a`. That costs `tf + tg` instead of `max tf tg`, it stores both
encoded results on work tapes, and — the real problem — nesting `n` conditionals evaluates `2 ^ n`
branches instead of `n`. The content of a case analysis is that the branch not taken is never run,
and that laziness is not expressible by composing total functions: the machine has to choose before
it runs, which is why this is a combinator with a machine-level branch behind it and not a
consequence of `computableInTimeAndSpace_comp`.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_cond`: the primitive, the recursor of `Bool`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_ite`: Lean's `ite`, for a decidable predicate.
* `Turing.MultiTapeTM.computableInTimeAndSpace_casesOn`: a `match` on a finite type, obtained from
  the primitive by nesting it once per constructor. This is how a `match` on any finite inductive
  type is handled.
* `Turing.MultiTapeTM.computableInTimeAndSpace_match`: the same from a computable scrutinee, which
  is the form to use. See `CslibTests.Complexity.Combinators` for worked examples.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- **Complexity of a two-way case analysis**, the recursor of `Bool`. The machine runs the machine
for `sel`, redirecting its output onto a work tape. Since `encCond` is injective, the two possible
contents of that tape are two different fixed strings, which the finite control can tell apart in
constant time; it then continues with the machine for the branch that is taken, on the original
input.

Only the branch that is taken is executed, hence the `max` of the two bounds rather than their
sum. -/
public theorem computableInTimeAndSpace_cond {sel : α → Bool} {_if _else : α → β}
    {encIn : α ↪ List Bool} {encCond : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {tc sc tif sif telse selse : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn encCond tc sc)
    (hif : ComputableInTimeAndSpace _if encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace _else encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => if sel a then _if a else _else a) encIn encOut
      (fun a => c * (tc a + max (tif a) (telse a) + 1))
      (fun a => c * (sc a + max (sif a) (selse a) + 1)) :=
  sorry

/-- **Complexity of Lean's `ite`.** A conditional on a decidable predicate, given a machine that
decides it. This is `computableInTimeAndSpace_cond` read through `decide`: the `Decidable` instance
of `ite` carries no computational content, so all that is needed of the predicate is that its
Boolean test is computable — which for a language is exactly `DecidableInTimeAndSpace`. -/
public theorem computableInTimeAndSpace_ite {p : α → Prop} [DecidablePred p] {_if _else : α → β}
    {encIn : α ↪ List Bool} {encCond : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {tc sc tif sif telse selse : α → ℕ}
    (hp : ComputableInTimeAndSpace (fun a => decide (p a)) encIn encCond tc sc)
    (hif : ComputableInTimeAndSpace _if encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace _else encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => if p a then _if a else _else a) encIn encOut
      (fun a => c * (tc a + max (tif a) (telse a) + 1))
      (fun a => c * (sc a + max (sif a) (selse a) + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_cond hp hif helse
  refine ⟨c, ?_⟩
  have hfun : (fun a => if decide (p a) = true then _if a else _else a) =
      fun a => if p a then _if a else _else a := by
    funext a
    simp
  rwa [hfun] at hc

/-- **Complexity of a `match` on a finite type.** If every constructor of the scrutinee can be
tested for and every branch is computable, then so is the `match`. Only the branch that is taken is
executed, and the number of tests is a constant of the type, so both are absorbed into the
supremum and the constant factor.

A branch only has to *agree* with the function being computed on the inputs at which it is taken;
what it does elsewhere is irrelevant, since it is never run there. That is what `hagree` says, and
it is what a `match` that destructures data needs: the machine that extracts a constructor's
payload is only meaningful on the encodings of that constructor, so the branch built from it has to
be extended by junk to become a total function, and the junk must not have to be accounted for.
The same weakening lets a computable function be patched at finitely many points, by taking the
selector to be membership in the finite set of exceptions.

This is the primitive nested once per constructor, which is how a `match` on any finite inductive
type is handled. It is not how a `match` on a *recursive* inductive type is handled: the recursor of
`Nat` or `List` is a fold, whose combinator is the loop of
`Cslib.Computability.Machines.Turing.MultiTape.Combinators.Loop` with an iteration bound, not a
case analysis.

The branches may perfectly well have different result types: take the output type to be `Σ i, β i`
and the branches to be `fun i a => ⟨i, br i a⟩`. Making the statement dependent would gain nothing,
because computability depends only on the two encoded strings and not on the types they encode —
that is `ComputableInTimeAndSpace.congr` — so a `motive` has no computational content. The
genuinely dependent conclusion, about a function `(a : α) → β (sel a)`, cannot even be stated: it
has no single output encoding. The tag that the sigma carries is not overhead either, since without
it the result would in general not be decodable. -/
public theorem computableInTimeAndSpace_casesOn {ι : Type} [Fintype ι] [DecidableEq ι]
    {sel : α → ι} {f : α → β} {br : ι → α → β}
    {encIn : α ↪ List Bool} {encCond : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {tc sc t s : ι → α → ℕ}
    (hagree : ∀ i a, sel a = i → br i a = f a)
    (htest : ∀ i, ComputableInTimeAndSpace (fun a => decide (sel a = i)) encIn encCond
      (tc i) (sc i))
    (hbr : ∀ i, ComputableInTimeAndSpace (br i) encIn encOut (t i) (s i)) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut
      (fun a => c * (Finset.univ.sup (fun i => tc i a) + Finset.univ.sup (fun i => t i a) + 1))
      (fun a => c * (Finset.univ.sup (fun i => sc i a)
        + Finset.univ.sup (fun i => s i a) + 1)) := by
  classical
  set TC : α → ℕ := fun a => Finset.univ.sup fun i => tc i a with hTC
  set TB : α → ℕ := fun a => Finset.univ.sup fun i => t i a with hTB
  set SC : α → ℕ := fun a => Finset.univ.sup fun i => sc i a with hSC
  set SB : α → ℕ := fun a => Finset.univ.sup fun i => s i a with hSB
  have hle : ∀ (i : ι) (a : α),
      tc i a ≤ TC a ∧ t i a ≤ TB a ∧ sc i a ≤ SC a ∧ s i a ≤ SB a := fun i a =>
    ⟨Finset.le_sup (f := fun i => tc i a) (Finset.mem_univ i),
      Finset.le_sup (f := fun i => t i a) (Finset.mem_univ i),
      Finset.le_sup (f := fun i => sc i a) (Finset.mem_univ i),
      Finset.le_sup (f := fun i => s i a) (Finset.mem_univ i)⟩
  -- The branches are chained one constructor at a time, keeping the shape of the bounds fixed.
  have key : ∀ (l : List ι) (d : α → β),
      (∃ c, ComputableInTimeAndSpace d encIn encOut
        (fun a => c * (TC a + TB a + 1)) (fun a => c * (SC a + SB a + 1))) →
      ∃ c, ComputableInTimeAndSpace (fun a => if sel a ∈ l then f a else d a)
        encIn encOut (fun a => c * (TC a + TB a + 1)) (fun a => c * (SC a + SB a + 1)) := by
    intro l
    induction l with
    | nil => exact fun d hd => by simpa using hd
    | cons i l ih =>
      intro d hd
      obtain ⟨c₀, hc₀⟩ := ih d hd
      obtain ⟨c₁, hc₁⟩ := computableInTimeAndSpace_cond (htest i) (hbr i) hc₀
      refine ⟨c₁ * (c₀ + 2), ?_⟩
      have hfun : (fun a => if decide (sel a = i) = true then br i a else
          if sel a ∈ l then f a else d a) =
          fun a => if sel a ∈ i :: l then f a else d a := by
        funext a
        by_cases h : sel a = i
        · simp [List.mem_cons, h, hagree i a h]
        · simp [List.mem_cons, h]
      rw [hfun] at hc₁
      refine hc₁.mono (fun a => ?_) (fun a => ?_)
      · have h1 := (hle i a).1
        have h3 : max (t i a) (c₀ * (TC a + TB a + 1)) ≤ (c₀ + 1) * (TC a + TB a + 1) := by
          refine max_le ((hle i a).2.1.trans ?_) (Nat.mul_le_mul_right _ (by omega))
          calc TB a ≤ TC a + TB a + 1 := by omega
            _ ≤ (c₀ + 1) * (TC a + TB a + 1) := Nat.le_mul_of_pos_left _ (by omega)
        calc c₁ * (tc i a + max (t i a) (c₀ * (TC a + TB a + 1)) + 1)
            ≤ c₁ * ((TC a + TB a + 1) + (c₀ + 1) * (TC a + TB a + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = c₁ * (c₀ + 2) * (TC a + TB a + 1) := by ring
      · have h1 := (hle i a).2.2.1
        have h3 : max (s i a) (c₀ * (SC a + SB a + 1)) ≤ (c₀ + 1) * (SC a + SB a + 1) := by
          refine max_le ((hle i a).2.2.2.trans ?_) (Nat.mul_le_mul_right _ (by omega))
          calc SB a ≤ SC a + SB a + 1 := by omega
            _ ≤ (c₀ + 1) * (SC a + SB a + 1) := Nat.le_mul_of_pos_left _ (by omega)
        calc c₁ * (sc i a + max (s i a) (c₀ * (SC a + SB a + 1)) + 1)
            ≤ c₁ * ((SC a + SB a + 1) + (c₀ + 1) * (SC a + SB a + 1)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = c₁ * (c₀ + 2) * (SC a + SB a + 1) := by ring
  -- An empty scrutinee type means an empty domain, where every function is computable.
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hα : IsEmpty α := ⟨fun a => hι.elim (sel a)⟩
    have : Finite α := Finite.of_injective (fun a => hα.elim a : α → Empty) fun a => hα.elim a
    obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encOut) f
    exact ⟨c, hc.mono (fun a => hα.elim a) (fun a => hα.elim a)⟩
  · obtain ⟨i₀⟩ := hι
    obtain ⟨c, hc⟩ := key Finset.univ.toList (br i₀)
      ⟨1, (hbr i₀).mono (fun a => by have := (hle i₀ a).2.1; omega)
        (fun a => by have := (hle i₀ a).2.2.2; omega)⟩
    refine ⟨c, ?_⟩
    have hfun : (fun a => if sel a ∈ Finset.univ.toList then f a else br i₀ a) = f := by
      funext a
      simp
    rwa [hfun] at hc

/-- **Complexity of a `match` on a finite type, from a computable scrutinee.** The tests that
`computableInTimeAndSpace_casesOn` asks for come for free: deciding which value the scrutinee has
is a function on a finite type, hence computable in constant time by
`computableInTimeAndSpace_of_finite`, so a test costs one composition with the scrutinee. The
composition parks the encoded scrutinee on a work tape, but its length is bounded by a constant of
the type rather than by the time that produced it, since a finite type has finitely many encodings;
so the space bound picks up nothing beyond the scrutinee's own. -/
public theorem computableInTimeAndSpace_match {ι : Type} [Fintype ι]
    {sel : α → ι} {br : ι → α → β}
    {encIn : α ↪ List Bool} {encι : ι ↪ List Bool} {encCond : Bool ↪ List Bool}
    {encOut : β ↪ List Bool} {tsel ssel : α → ℕ} {t s : ι → α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn encι tsel ssel)
    (hbr : ∀ i, ComputableInTimeAndSpace (br i) encIn encOut (t i) (s i)) :
    ∃ c, ComputableInTimeAndSpace (fun a => br (sel a) a) encIn encOut
      (fun a => c * (tsel a + Finset.univ.sup (fun i => t i a) + 1))
      (fun a => c * (ssel a + Finset.univ.sup (fun i => s i a) + 1)) := by
  classical
  -- a finite type has finitely many encodings, so the encoded scrutinee is of constant length
  set K : ℕ := Finset.univ.sup (fun i : ι => (encι i).length) with hK
  have hKle : ∀ a, (encι (sel a)).length ≤ K := fun a =>
    Finset.le_sup (f := fun i : ι => (encι i).length) (Finset.mem_univ (sel a))
  -- deciding which value the scrutinee has, one constructor at a time
  have htest : ∀ i : ι, ∃ c, ComputableInTimeAndSpace (fun a => decide (sel a = i))
      encIn encCond (fun a => c * (tsel a + 1)) (fun a => c * (ssel a + 1)) := by
    intro i
    obtain ⟨cd, hd⟩ := computableInTimeAndSpace_of_finite (encIn := encι) (encOut := encCond)
      fun j => decide (j = i)
    obtain ⟨c, hc⟩ := computableInTimeAndSpace_comp hsel hd
    refine ⟨c * (cd + K + 1), hc.mono (fun a => ?_) (fun a => ?_)⟩
    · have hlen := hKle a
      have hring : (cd + K + 1) * (tsel a + 1) = (cd + K + 1) * tsel a + (cd + K + 1) := by ring
      have hmul : tsel a ≤ (cd + K + 1) * tsel a := Nat.le_mul_of_pos_left _ (by omega)
      calc c * (tsel a + cd + (encι (sel a)).length + 1)
          ≤ c * ((cd + K + 1) * (tsel a + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = c * (cd + K + 1) * (tsel a + 1) := by ring
    · have hlen := hKle a
      have hring : (cd + K + 1) * (ssel a + 1) = (cd + K + 1) * ssel a + (cd + K + 1) := by ring
      have hmul : ssel a ≤ (cd + K + 1) * ssel a := Nat.le_mul_of_pos_left _ (by omega)
      calc c * (ssel a + 0 + (encι (sel a)).length + 1)
          ≤ c * ((cd + K + 1) * (ssel a + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = c * (cd + K + 1) * (ssel a + 1) := by ring
  choose C hC using htest
  -- one bound for all of the finitely many tests
  set cmax : ℕ := Finset.univ.sup C with hcmax
  have hCle : ∀ i : ι, C i ≤ cmax := fun i => Finset.le_sup (Finset.mem_univ i)
  have htest' : ∀ i : ι, ComputableInTimeAndSpace (fun a => decide (sel a = i)) encIn encCond
      (fun a => cmax * (tsel a + 1)) (fun a => cmax * (ssel a + 1)) := fun i =>
    (hC i).mono (fun a => Nat.mul_le_mul_right _ (hCle i))
      (fun a => Nat.mul_le_mul_right _ (hCle i))
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_casesOn (f := fun a => br (sel a) a)
      (fun i a h => by rw [h]) htest' hbr
  refine ⟨c * (cmax + 1), hc.mono (fun a => ?_) (fun a => ?_)⟩
  · have hsup : Finset.univ.sup (fun _ : ι => cmax * (tsel a + 1)) ≤ cmax * (tsel a + 1) :=
      Finset.sup_le fun _ _ => le_rfl
    have hring : (cmax + 1) * (tsel a + Finset.univ.sup (fun i => t i a) + 1)
        = cmax * (tsel a + 1) + cmax * Finset.univ.sup (fun i => t i a)
          + (tsel a + Finset.univ.sup (fun i => t i a) + 1) := by ring
    calc c * (Finset.univ.sup (fun _ : ι => cmax * (tsel a + 1))
            + Finset.univ.sup (fun i => t i a) + 1)
        ≤ c * ((cmax + 1) * (tsel a + Finset.univ.sup (fun i => t i a) + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = c * (cmax + 1) * (tsel a + Finset.univ.sup (fun i => t i a) + 1) := by ring
  · have hsup : Finset.univ.sup (fun _ : ι => cmax * (ssel a + 1))
        ≤ cmax * (ssel a + 1) := Finset.sup_le fun _ _ => le_rfl
    have hring : (cmax + 1) * (ssel a + Finset.univ.sup (fun i => s i a) + 1)
        = cmax * (ssel a + 1) + cmax * Finset.univ.sup (fun i => s i a)
          + (ssel a + Finset.univ.sup (fun i => s i a) + 1) := by ring
    calc c * (Finset.univ.sup (fun _ : ι => cmax * (ssel a + 1))
            + Finset.univ.sup (fun i => s i a) + 1)
        ≤ c * ((cmax + 1) * (ssel a + Finset.univ.sup (fun i => s i a) + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = c * (cmax + 1) * (ssel a + Finset.univ.sup (fun i => s i a) + 1) := by ring

end Turing.MultiTapeTM
