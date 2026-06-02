/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Lean.LabelAttribute
public meta import Lean.LabelAttribute
public import Lean.Elab.Tactic.SolveByElim
public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-! # The `computes` tactic for RoseTreeMachine V3 program semantics

The resource-erased semantic correctness lemmas of program builders (`*_computes` /
`*_computes_enc`) follow the structure of the program: to prove that a compound builder
computes a value, one applies the `_computes` lemma of the outermost combinator/routine and
recurses on the arguments, closing leaves with the hypotheses about the inputs. This is a
structural, backtracking proof search — exactly what `solve_by_elim` performs over a labelled
set of lemmas together with the local hypotheses.

This module provides:

* `register_label_attr computes` — tag the routine `_computes` lemmas that the search may use.
* `register_simp_attr computes_simp` — the encode-bridge lemmas used to expose the encoded
  structure of a value before the search starts.
* the `computes` tactic — `simp only` preprocessing (unfolding `PB.computes_enc`, any
  user-supplied program/value definitions and the `computes_simp` bridges) followed by
  `solve_by_elim ... using computes`.

The attribute must be *registered in a separate, imported module* (its `initialize` does not
run in the file that defines it), which is why this lives in its own file. -/

public meta section

/-- Lemmas of the form `… .computes …` / `… .computes_enc …` for the `computes` tactic to use
during proof search. -/
register_label_attr computes

/-- Encode-bridge lemmas (e.g. `encode_biTape`) that rewrite the encoding of a structured value
into the encoding of its components, exposing the shape that the routine `_computes` lemmas
conclude about. Used by the preprocessing step of the `computes` tactic. -/
register_simp_attr computes_simp

end

namespace Turing.RoseTreeMachine

open Lean Elab Tactic

/-- Prove a resource-erased semantic goal `… .computes_enc env value` (or `PB.computes …`) by
structural proof search. The optional bracketed list supplies the program and value definitions
to unfold (e.g. `computes [bitape_move_right, BiTape.move_right]`) so that the outermost
combinator and the encoded value structure are exposed. The search then applies `@[computes]`
lemmas and local hypotheses via `solve_by_elim`. -/
syntax (name := computesTac) "computes" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean in
macro_rules
  | `(tactic| computes) => do
      let cenc := mkIdent `Turing.RoseTreeMachine.PB.computes_enc
      let csimp := mkIdent `computes_simp
      let clab := mkIdent `computes
      `(tactic|
        simp only [$cenc:ident, $csimp:ident] <;>
        solve_by_elim (config := { maxDepth := 30 }) using $clab:ident)
  | `(tactic| computes [ $unfolds,* ]) => do
      let cenc := mkIdent `Turing.RoseTreeMachine.PB.computes_enc
      let csimp := mkIdent `computes_simp
      let clab := mkIdent `computes
      `(tactic|
        simp only [$cenc:ident, $csimp:ident, $unfolds,*] <;>
        solve_by_elim (config := { maxDepth := 30 }) using $clab:ident)

end Turing.RoseTreeMachine
