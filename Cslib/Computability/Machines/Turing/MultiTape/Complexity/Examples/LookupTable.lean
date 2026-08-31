/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.Lookup

/-!
# Faithfulness of tabulated lookup tables

A universal machine carries the transition function of the machine it simulates as data: an
association list built by tabulating that function over a list of its arguments. Consulting the
table is then `Lookup.lookupFn`, and what the simulation needs is that consulting it gives back
exactly what applying the original function would have given.

That is the content of `firstMatch_map_of_mem`: if the keys of a tabulated table are pairwise
distinct — the key function `g` is injective on the tabulated list — then looking up `g x`
returns `some (h x)`. Injectivity is what rules out an earlier entry shadowing `x`'s own.

The `Fintype` corollary is the shape a tabulation actually takes: the table lists *every*
argument, so `Finset.univ.toList` is the list being tabulated over and no membership side
condition survives.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace Lookup

/-! ### Tabulated tables are faithful -/

/-- **Looking up a tabulated entry returns the tabulated value.** In a table obtained by
tabulating `fun w => (g w, h w)` over `l`, the first entry whose key is `g x` is `x`'s own, so
its value is `h x`. The hypothesis is injectivity of `g` on `l`: without it an earlier element
sharing `x`'s key would shadow it. -/
lemma firstMatch_map_of_mem {K V W : Type} [BEq K] [LawfulBEq K]
    (l : List W) (g : W → K) (h : W → V)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y)
    (x : W) (hx : x ∈ l) :
    firstMatch (g x) (l.map fun w => (g w, h w)) = some (h x) := by
  induction l with
  | nil => simp at hx
  | cons w l ih =>
    simp only [List.map_cons, firstMatch]
    cases hb : (g w == g x) with
    | true =>
      have hgw : g w = g x := eq_of_beq hb
      have hw : w = x := hinj w List.mem_cons_self x hx hgw
      rw [Bool.cond_true, hw]
    | false =>
      rw [Bool.cond_false]
      have hne : g w ≠ g x := fun hgw => by simp [hgw] at hb
      have hxl : x ∈ l := by
        rcases List.mem_cons.mp hx with rfl | hxl
        · exact absurd rfl hne
        · exact hxl
      exact ih (fun a ha b hbm => hinj a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hbm)) hxl

/-- The same statement for `lookupFn`, the fold that a machine actually runs. -/
lemma lookupFn_map_of_mem {K V W : Type} [BEq K] [LawfulBEq K]
    (l : List W) (g : W → K) (h : W → V)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y)
    (x : W) (hx : x ∈ l) :
    lookupFn (l.map (fun w => (g w, h w)), g x) = some (h x) := by
  rw [lookupFn_eq]
  exact firstMatch_map_of_mem l g h hinj x hx

/-! ### Tabulating over a finite type -/

/-- Tabulating `h` over *all* of a finite type, keyed by an injective `g`, gives a table in which
every key lookup succeeds with the tabulated value. This is the form a universal machine's
encoded transition table takes: the argument type is finite, so the table is complete and the
membership hypothesis of `firstMatch_map_of_mem` discharges itself. -/
lemma firstMatch_map_univ_toList {K V W : Type} [BEq K] [LawfulBEq K] [Fintype W]
    (g : W → K) (hg : Function.Injective g) (h : W → V) (x : W) :
    firstMatch (g x) (Finset.univ.toList.map fun w => (g w, h w)) = some (h x) :=
  firstMatch_map_of_mem _ g h (fun _ _ _ _ hab => hg hab) x
    (Finset.mem_toList.mpr (Finset.mem_univ x))

/-- The `Fintype` tabulation lemma, phrased for `lookupFn`. -/
lemma lookupFn_map_univ_toList {K V W : Type} [BEq K] [LawfulBEq K] [Fintype W]
    (g : W → K) (hg : Function.Injective g) (h : W → V) (x : W) :
    lookupFn ((Finset.univ.toList.map fun w => (g w, h w) : Table K V), g x) = some (h x) := by
  rw [lookupFn_eq]
  exact firstMatch_map_univ_toList g hg h x

end Lookup

end MultiTapeTM

end Turing
