/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of a case analysis

A case analysis runs a machine that says which case holds and then continues with the machine for
that case. This file has one primitive, `computableInTimeAndSpace_match`, which does exactly that
for a scrutinee in an arbitrary finite type; `cond`, `ite` and `dite` are the instances at `Bool`.

## Why the finite case is the primitive and not the binary one

Lean's `ite` is not primitive: `ite c t e` is `Decidable.casesOn`, the recursor of the two
constructor inductive `Decidable c`, whose constructors carry only proofs. Since `Prop` is erased,
the computational content of `ite` is exactly the recursor of `Bool`, and a `match` on a finite
inductive type is that recursor nested once per constructor. So `Bool.rec` is the primitive of the
*elaborator*.

It is not the right primitive here, because a machine does not nest. Deciding among `n` cases is
one machine reading a scrutinee of constant length and dispatching from its finite control, which
is no harder than deciding among two; the nesting is a fiction that the machine never performs.
Building the finite case analysis out of the binary one therefore does not decompose it into
anything simpler — it only replays `n - 1` copies of the same argument, and each replay multiplies
the constants, so the bounds have to be renormalised into a fixed shape at every step to make the
induction go through. Taking the finite case as the primitive deletes all of that: what remains is
`Finset.sup_le` at `Bool`.

The two are equivalent up to constant factors in both directions, so there is no loss. Tests for
individual cases, which is what the binary form consumes, and the tag itself, which is what this
one consumes, are interderivable at constant cost: the tag gives every test by one composition
with a function on a finite type, and the tests give the tag by running all `n` of them. There is
consequently no reason to state both.

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

* `Turing.MultiTapeTM.computableInTimeAndSpace_match`: the primitive, a case analysis on a
  scrutinee in a finite type. See `CslibTests.Complexity.Combinators` for worked examples.
* `Turing.MultiTapeTM.computableInTimeAndSpace_cond`: the recursor of `Bool`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_ite`: Lean's `ite`, for a decidable predicate.
* `Turing.MultiTapeTM.computableInTimeAndSpace_dite`: Lean's `dite`, whose branches are defined
  only under a hypothesis and so are supplied through total extensions.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- **Complexity of a case analysis on a finite type.** If the scrutinee and every branch are
computable, then so is the case analysis. The machine runs the machine for `sel`, redirecting its
output onto a work tape; since the scrutinee's type is finite there are only finitely many possible
contents, all of constant length, so the finite control can tell them apart in constant time and
continue with the machine for the branch that is taken, on the original input.

Only the branch that is taken is executed, hence the supremum of the branches' bounds rather than
their sum. The number of cases is a constant of the type and is absorbed into the constant factor,
as is the cost of rewinding the input, which is bounded by the time already spent.

A branch only has to *agree* with the function being computed where it is taken; what it does
elsewhere is irrelevant, since it is never run there. That is what `hagree` says. It is what a
`match` that destructures data needs — the machine extracting a constructor's payload is only
meaningful on encodings of that constructor, so the branch built from it has to be extended by junk
to become a total function, and the junk must not have to be accounted for — and it is what `dite`
needs, where a branch is not even defined outside its case. The same weakening lets a computable
function be patched at finitely many points, by taking the scrutinee to be membership in the finite
set of exceptions.

This is a case analysis, not a recursor: a `match` on a *recursive* inductive type is a fold, whose
combinator is the loop of `Cslib.Computability.Machines.Turing.MultiTape.Combinators.Loop` with an
iteration bound.

The branches may perfectly well have different result types: take the output type to be `Σ i, β i`
and the branches to be `fun i a => ⟨i, br i a⟩`. Making the statement dependent would gain nothing,
because computability depends only on the two encoded strings and not on the types they encode —
that is `ComputableInTimeAndSpace.congr` — so a `motive` has no computational content. The
genuinely dependent conclusion, about a function `(a : α) → β (sel a)`, cannot even be stated: it
has no single output encoding. The tag that the sigma carries is not overhead either, since without
it the result would in general not be decodable. -/
public theorem computableInTimeAndSpace_match {ι : Type} [Fintype ι]
    {sel : α → ι} {f : α → β} {br : ι → α → β}
    {encIn : α ↪ List Bool} {encι : ι ↪ List Bool} {encOut : β ↪ List Bool}
    {tsel ssel : α → ℕ} {t s : ι → α → ℕ}
    (hagree : ∀ a, br (sel a) a = f a)
    (hsel : ComputableInTimeAndSpace sel encIn encι tsel ssel)
    (hbr : ∀ i, ComputableInTimeAndSpace (br i) encIn encOut (t i) (s i)) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut
      (fun a => c * (tsel a + Finset.univ.sup (fun i => t i a) + 1))
      (fun a => c * (ssel a + Finset.univ.sup (fun i => s i a) + 1)) :=
  sorry

/-- **Complexity of a two-way case analysis**, the recursor of `Bool`. This is
`computableInTimeAndSpace_match` at `ι = Bool`, where the supremum over the two branches is their
maximum. -/
public theorem computableInTimeAndSpace_cond {sel : α → Bool} {_if _else : α → β}
    {encIn : α ↪ List Bool} {encCond : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {tc sc tif sif telse selse : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn encCond tc sc)
    (hif : ComputableInTimeAndSpace _if encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace _else encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => if sel a then _if a else _else a) encIn encOut
      (fun a => c * (tc a + max (tif a) (telse a) + 1))
      (fun a => c * (sc a + max (sif a) (selse a) + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_match (encι := encCond)
    (f := fun a => if sel a then _if a else _else a)
    (br := fun b a => bif b then _if a else _else a)
    (t := fun b => bif b then tif else telse) (s := fun b => bif b then sif else selse)
    (fun a => by cases sel a <;> simp)
    hsel (fun b => by cases b; exacts [helse, hif])
  refine ⟨c, hc.mono (fun a => ?_) (fun a => ?_)⟩
  · have h : Finset.univ.sup (fun b : Bool => (bif b then tif else telse) a)
        ≤ max (tif a) (telse a) := Finset.sup_le fun b _ => by cases b <;> simp
    exact Nat.mul_le_mul_left _ (by omega)
  · have h : Finset.univ.sup (fun b : Bool => (bif b then sif else selse) a)
        ≤ max (sif a) (selse a) := Finset.sup_le fun b _ => by cases b <;> simp
    exact Nat.mul_le_mul_left _ (by omega)

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

/-- **Complexity of Lean's `dite`.** The branches of a `dite` are not functions of the input alone:
each is defined only under the hypothesis that its case holds, so neither can be asked to be
computable as it stands. What is asked instead is a computable *total* function agreeing with the
branch where that branch is taken, which is `computableInTimeAndSpace_match`'s `hagree` in the
concrete case `ι = Bool`. Outside its case a branch may be anything at all, which is exactly the
freedom needed to extend it to a total function. -/
public theorem computableInTimeAndSpace_dite {p : α → Prop} [DecidablePred p]
    {_if : (a : α) → p a → β} {_else : (a : α) → ¬ p a → β} {If Else : α → β}
    {encIn : α ↪ List Bool} {encCond : Bool ↪ List Bool} {encOut : β ↪ List Bool}
    {tc sc tif sif telse selse : α → ℕ}
    (hIf : ∀ a (h : p a), If a = _if a h)
    (hElse : ∀ a (h : ¬ p a), Else a = _else a h)
    (hp : ComputableInTimeAndSpace (fun a => decide (p a)) encIn encCond tc sc)
    (hif : ComputableInTimeAndSpace If encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace Else encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => dite (p a) (_if a) (_else a)) encIn encOut
      (fun a => c * (tc a + max (tif a) (telse a) + 1))
      (fun a => c * (sc a + max (sif a) (selse a) + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_ite (p := p) hp hif helse
  refine ⟨c, ?_⟩
  have hfun : (fun a => if p a then If a else Else a) =
      fun a => dite (p a) (_if a) (_else a) := by
    funext a
    by_cases h : p a
    · simp [h, hIf a h]
    · simp [h, hElse a h]
  rwa [hfun] at hc

end Turing.MultiTapeTM
