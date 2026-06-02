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

/-! # The `computes` attributes for RoseTreeMachine V3 program semantics

The resource-erased semantic correctness lemmas of program builders (`*_computes` /
`*_computes_enc`) follow the structure of the program: to prove that a compound builder
computes a value, one applies the `_computes` lemma of the outermost combinator/routine and
recurses on the arguments, closing leaves with the hypotheses about the inputs. This is a
structural, backtracking proof search — exactly what `solve_by_elim` performs over a labelled
set of lemmas together with the local hypotheses.

This module provides the two attributes used to drive such proofs:

* `register_label_attr computes` — tag the routine `_computes` lemmas that the search may use.
* `register_simp_attr computes_simp` — the encode-bridge lemmas used to expose the encoded
  structure of a value before the search starts.

A typical proof unfolds `PB.computes_enc`, the relevant program/value definitions and the
`computes_simp` bridges, then runs the search, e.g.:

```
simp only [PB.computes_enc, computes_simp, bitape_move_right, BiTape.move_right] <;>
  solve_by_elim (config := { maxDepth := 30 }) using computes
```

The attributes must be *registered in a separate, imported module* (their `initialize` does not
run in the file that defines them), which is why this lives in its own file. -/

public meta section

/-- Lemmas of the form `… .computes …` / `… .computes_enc …` for `solve_by_elim ... using computes`
to use during proof search. -/
register_label_attr computes

/-- Encode-bridge lemmas (e.g. `encode_biTape`) that rewrite the encoding of a structured value
into the encoding of its components, exposing the shape that the routine `_computes` lemmas
conclude about. Used by the `simp only [..., computes_simp]` preprocessing step. -/
register_simp_attr computes_simp

end
