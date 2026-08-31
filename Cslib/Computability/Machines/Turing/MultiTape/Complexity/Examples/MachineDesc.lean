/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.LookupTable

/-!
# An untyped description of a multi-tape machine

A `MultiTapeTM k Symbol State` is a *typed* object: its transition function ranges over `Fin k`,
over `Symbol` and over `State`, so a term mentioning it is already committed to one particular
number of work tapes, one alphabet and one state set. A universal machine cannot be committed in
that way — it has to accept, as data on its input, the description of an arbitrary machine.

This file therefore replaces every one of those types by `ℕ`. A state is its index, a tape symbol
is `Option ℕ` (with `none` the blank), and the work-head tuple `Fin k → Option Symbol` becomes a
plain `List`. The resulting types `UKey` and `UOut` are built solely from `ℕ`, `Option`, `List`,
`Prod` and `SignType`, so they inherit `DataEncode` from `Encoding` with no new instance, and —
this is the point of being untyped — a *single* value of type `UTable` can describe a machine for
any `k`, any alphabet size and any state count. One universal machine can interpret them all.

The description itself, `desc`, is the transition function tabulated over its (finite) domain:
`Lookup.Table`. What the simulation needs from it is faithfulness, `lookupFn_desc`: consulting the
table at `keyOf q a w` returns exactly `outOf (tm.tr q a w)`. That follows from
`Lookup.lookupFn_map_univ_toList` once `keyOf` is known to be injective, which is
`keyOf_injective`: erasing the `Fin` bounds loses no information, because the components are
recovered by `Fin.val_injective` and `List.ofFn_inj`.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace MachineDesc

/-! ### The untyped types -/

/-- An untyped tape symbol: an index into the alphabet, with `none` the blank. -/
abbrev USym := Option ℕ

/-- An untyped key of the transition table: the state, the input symbol and the symbols under the
work heads. -/
abbrev UKey := ℕ × USym × List USym

/-- An untyped action on one work tape: optionally a symbol to write, then a head movement. -/
abbrev UAction := Option USym × SignType

/-- An untyped transition output: the input head's movement, the actions on the work tapes, the
symbol to output and the successor state (`none` to halt). -/
abbrev UOut := SignType × List UAction × USym × Option ℕ

/-- An untyped machine description: the transition function as an association list. -/
abbrev UTable := Lookup.Table UKey UOut

/-! ### Erasing the types -/

/-- The untyped key of a state, an input symbol and a tuple of work-head symbols. -/
def keyOf {k sym state : ℕ} (q : Fin state) (a : Option (Fin sym))
    (w : Fin k → Option (Fin sym)) : UKey :=
  (q.val, a.map Fin.val, (List.ofFn w).map (Option.map Fin.val))

/-- The untyped form of a transition output. -/
def outOf {k sym state : ℕ} (o : TransitionOut k (Fin sym) (Fin state)) : UOut :=
  (o.inputMove,
   (List.ofFn o.workActions).map (fun p => (p.1.map (Option.map Fin.val), p.2)),
   o.outS.map Fin.val,
   o.q'.map Fin.val)

/-- **The description of a machine**: its transition function tabulated over the whole (finite)
domain, keyed by `keyOf`. -/
noncomputable def desc {k sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state)) : UTable :=
  Finset.univ.toList.map fun x : Fin state × Option (Fin sym) × (Fin k → Option (Fin sym)) =>
    (keyOf x.1 x.2.1 x.2.2, outOf (tm.tr x.1 x.2.1 x.2.2))

/-! ### Faithfulness -/

/-- **Erasing the types loses nothing.** The key of a transition argument determines that
argument, so no two entries of `desc` share a key. -/
lemma keyOf_injective {k sym state : ℕ} :
    Function.Injective
      (fun x : Fin state × Option (Fin sym) × (Fin k → Option (Fin sym)) =>
        keyOf x.1 x.2.1 x.2.2) := by
  rintro ⟨q₁, a₁, w₁⟩ ⟨q₂, a₂, w₂⟩ h
  simp only [keyOf, Prod.mk.injEq] at h
  obtain ⟨hq, ha, hw⟩ := h
  have hq' : q₁ = q₂ := Fin.val_injective hq
  have ha' : a₁ = a₂ := Option.map_injective Fin.val_injective ha
  have hw' : w₁ = w₂ :=
    List.ofFn_inj.mp (List.map_injective_iff.mpr (Option.map_injective Fin.val_injective) hw)
  subst hq'
  subst ha'
  subst hw'
  rfl

/-- **The description is faithful.** Looking a key up in `desc tm` returns exactly the untyped
form of what `tm.tr` returns on the corresponding arguments — so a machine that interprets the
description takes the same steps as `tm`. -/
lemma lookupFn_desc {k sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (q : Fin state) (a : Option (Fin sym)) (w : Fin k → Option (Fin sym)) :
    Lookup.lookupFn (desc tm, keyOf q a w) = some (outOf (tm.tr q a w)) :=
  Lookup.lookupFn_map_univ_toList
    (g := fun x : Fin state × Option (Fin sym) × (Fin k → Option (Fin sym)) =>
      keyOf x.1 x.2.1 x.2.2)
    keyOf_injective (fun x => outOf (tm.tr x.1 x.2.1 x.2.2)) (q, a, w)

end MachineDesc

end MultiTapeTM

end Turing
