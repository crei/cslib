/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Lean

/-!
# The `@[bounds]` attribute

Registers a `Bounds` certificate as a *leaf* for the `bounds` tactic. Anything already proved —
a primitive, a hand-built certificate, or the result of `Bounds.fold` / `Bounds.while` — can be
registered, and the tactic will stop its recursion there.

This is the intended way to handle loops and recursion. `Bounds.fold` and `Bounds.while` take
arguments a tactic cannot invent (the accumulator bound `A`, the trip count `N`), so they are
deliberately *not* given tactic support; instead the human proves the certificate once and
registers it.

The extension lives in its own module because Lean forbids using an `initialize` declaration in
the module that declares it.
-/

open Lean

public section

/-- Certificates registered as leaves for the `bounds` tactic. -/
initialize boundsExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension
    { addEntryFn := Array.push
      addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- Simp set unfolding every `Bounds` combinator, so a synthesised certificate's bounds can be
read off. Populated in `BoundsTactic.lean`, where the combinators are in scope. -/
register_simp_attr boundsDefs

initialize registerBuiltinAttribute {
    name := `bounds
    descr := "register a `Bounds` certificate as a leaf for the `bounds` tactic"
    add := fun decl _ _ => modifyEnv fun env => boundsExt.addEntry env decl
  }

end
