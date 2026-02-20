/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

import Mathlib.Tactic.DeriveFintype

namespace Turing

-- TODO use a better alphabet
public inductive OneTwo where
  | one
  | two
deriving DecidableEq, Inhabited, Fintype


/-- An alphabet for list encoding -/
public inductive WithSep (α : Type) where
  | blank
  | ofChar (c : α)
  | comma
  -- TODO need to decide if we want to encode lists with parentheses or not.
  -- Is annoying when pushing and popping from lists, but can be useful to avoid
  -- running "off the tape"
  -- | lParen
  -- | rParen
deriving Fintype, DecidableEq, Inhabited

/-- A list of words is transformed by appending a comma after each word and concatenating.
Note that the comma is not only a separator but also appears as the final character
of the resulting string (if the list is non-empty). -/
public def listToString (ls : List (List α)) : List (WithSep α) :=
  (ls.map (fun w : List α => (w.map .ofChar) ++ [.comma])).flatten

public def listToTape (ls : List (List α)) : BiTape (WithSep α) :=
  BiTape.mk₁ (listToString ls)

public def MultiTapeTM.TransformsLists
    (tm : MultiTapeTM k (WithSep α))
    (tapes tapes' : Fin k → List (List α)) : Prop :=
  tm.TransformsTapes (listToTape ∘ tapes) (listToTape ∘ tapes')

public noncomputable def MultiTapeTM.eval_list
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part (Fin k → List (List α)) :=
  ⟨∃ tapes', tm.TransformsLists tapes tapes', fun h => h.choose⟩

@[simp, grind =]
public theorem MultiTapeTM.extend_eval_list
    {α : Type} [Fintype α]
    {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
    {tm : MultiTapeTM k₁ (WithSep α)}
    {tapes : Fin k₂ → List (List α)} :
  (tm.extend h_le).eval_list tapes =
    (tm.eval_list (tapes ⟨·, by omega⟩)).map (fun tapes' =>
      fun i : Fin k₂ => if h : i.val < k₁ then tapes' ⟨i, h⟩ else tapes i) := by
  sorry

@[simp, grind =]
public theorem MultiTapeTM.permute_tapes_eval_list
  {α : Type} [Fintype α] [Inhabited α]
  (tm : MultiTapeTM k (WithSep α)) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → List (List α)) :
  (tm.permute_tapes σ).eval_list tapes =
    (tm.eval_list (tapes ∘ σ)).map (fun tapes' => tapes' ∘ σ.symm) := by
  sorry

@[simp, grind =]
public theorem MultiTapeTM.with_tapes_eval_list
  {α : Type} [Fintype α] [Inhabited α]
  {k₁ k₂ : ℕ}
  {tm : MultiTapeTM k₁ (WithSep α)} {f : Fin k₁ → Fin k₂} {h_inj : f.Injective}
  {tapes : Fin k₂ → List (List α)} :
  (tm.with_tapes f h_inj).eval_list tapes =
    (tm.eval_list (tapes ∘ f)).map
      (fun tapes' => fun t => apply_updates tapes tapes' f t) := by
   sorry

def MultiTapeTM.TransformsListsWithStats
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α))
    (ts : (Fin k → List (List α)) × (Fin k → HeadStats)) : Prop :=
    tm.evalWithStats (listToTape ∘ tapes) = .some (listToTape ∘ ts.1, ts.2)

public noncomputable def MultiTapeTM.evalWithStats_list
    (tm : MultiTapeTM k (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part ((Fin k → List (List α)) × (Fin k → HeadStats)) :=
  ⟨∃ ts, tm.TransformsListsWithStats tapes ts, fun h => h.choose⟩

-- TODO Multiple ways to define this here:
-- 1. Use Part, then it captures non-decidable computations as well.
-- 2. Use Option but only make a partial statement: If the result of the function is None,
--  then we do not know what the TM does.
-- 3. State it as it is now.
-- I think we should rather use 1 and 2, but it could complicate the usage.
public def MultiTapeTM.cond_computes
    (tm : MultiTapeTM k (WithSep α))
    (f : (Fin k → List (List α)) → Option (Fin k → List (List α))) : Prop :=
  ∀ tapes, tm.eval_list tapes = f tapes

@[simp]
theorem MultiTapeTM.eval_of_cond_computes
    {tm : MultiTapeTM k (WithSep α)}
    (f : (Fin k → List (List α)) → Option (Fin k → List (List α)))
    (h_computes : tm.cond_computes f)
    {tapes : Fin k → List (List α)} :
    tm.eval_list tapes = f tapes := by
  specialize h_computes tapes
  simpa [MultiTapeTM.cond_computes] using h_computes

-- TOOD how is the definition different from the theorem?
public def MultiTapeTM.computes
    (tm : MultiTapeTM k (WithSep α))
    (f : (Fin k → List (List α)) → (Fin k → List (List α))) : Prop :=
  ∀ tapes, tm.eval_list tapes = .some (f tapes)

@[simp]
public theorem MultiTapeTM.eval_of_computes
    {tm : MultiTapeTM k (WithSep α)}
    {f : (Fin k → List (List α)) → (Fin k → List (List α))}
    (h_computes : tm.computes f)
    {tapes : Fin k → List (List α)} :
    tm.eval_list tapes = .some (f tapes) := by
  specialize h_computes tapes
  simpa [MultiTapeTM.computes] using h_computes

end Turing
