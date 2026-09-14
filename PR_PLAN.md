# Turing MultiTape complexity — campaign PR plan

This branch (`loop/06-tape-transformers`) is the campaign branch: it proves **function
composition** (`computableInTimeAndSpace_comp`) and the **loop combinator**
(`computableInTimeAndSpace_loopFunction`) on top of a reusable machine-layer toolkit. It is also
the PR into `main` that tracks *what is still to do*.

The work is being split into small, independently reviewable PRs against `main`, one at a time.
After each split PR is finalized, this branch's copies of the files it owns are made byte-identical
to it, so once it lands the campaign diff shows only the remaining work.

This file is campaign bookkeeping; it is **not** part of any split PR and should never be merged
into `main`.

## Status

| PR | Name | State | Branch |
|----|------|-------|--------|
| 1  | transforms-tapes | **finalized** | `pr/transforms-tapes` (off `main`) |
| 2+ | see below | planned | — |

Sibling PRs already split earlier in the campaign: `loop/03` (AlmostConstant), `loop/04`
(Option encoding), `loop/05` (Id).

## Files: new vs. modified

Pre-existing on `main` (campaign only *adds* to them): `Configuration.lean`, `Deterministic.lean`,
`TapeLemmas.lean`. Everything else under `Cslib/Computability/Machines/Turing/MultiTape/`
(`Plumbing/*`, `NormalForms/*`, `Combinators/*`, `Encodings/Option`) is new.

## Dependency DAG (intra-`MultiTape` imports)

```
Configuration            (base; +mapState +withState)
  └─ Deterministic       (+runFrom_eq_of_halt +exists_minimal_halting_time +...)
       ├─ TapeLemmas     (+space lemmas)
       │    └─ Plumbing/TransformsTapes
       │         ├─ Plumbing/Sequential          (transformsTapes_seq; seq_spec deferred)
       │         ├─ Plumbing/Clear
       │         ├─ NormalForms/Instrument
       │         └─ NormalForms/Sweep
       ├─ Plumbing/StepLemmas
       │    ├─ Plumbing/ExtendTapes      (+TapeLemmas)
       │    ├─ Plumbing/OutputToTape     (+TransformsTapes)
       │    ├─ Plumbing/InputFromTape    (+TransformsTapes)
       │    ├─ Plumbing/EmitTape         (+TransformsTapes)
       │    ├─ Plumbing/RewindTape       (+TransformsTapes)
       │    ├─ Plumbing/Branch           (+TransformsTapes)
       │    └─ Plumbing/Repeat           (+TransformsTapes)
       ├─ Plumbing/RewindInput
       └─ Combinators/AlmostConstant     (sibling PR)  ─┐
            └─ Encodings/Option          (sibling PR)   │
       Combinators/Id                    (sibling PR)  ─┘

NormalForms/Tidy      <- Instrument, Sweep, RewindInput, Sequential   (uses seq_spec)
NormalForms/Adapters  <- Tidy, OutputToTape, RewindTape, InputFromTape, EmitTape, ExtendTapes
                                                                       (uses seq_spec)
Combinators/Comp      <- Adapters
Combinators/Ite       <- Comp, AlmostConstant, Branch, Sequential, Adapters
Combinators/Loop      <- Option, Id, Adapters, Branch, Repeat, Clear, Sequential, TransformsTapes
```

## Proposed PR sequence

Each foundation lemma (in `Configuration`/`Deterministic`/`TapeLemmas`) rides with the PR of its
first user — no standalone "lemmas only" PR.

| PR | Contents | Depends on |
|----|----------|-----------|
| **1** ✅ | `TapeLemmas` (space lemmas) · `Plumbing/TransformsTapes` · `Plumbing/Sequential` (interface-level `transformsTapes_seq` only) · `Configuration` (`mapState`, `withState`) · `Deterministic` (`runFrom_eq_of_halt`, `exists_minimal_halting_time`) | `main` |
| **2** | `Plumbing/StepLemmas` · `ExtendTapes` · `OutputToTape` · `InputFromTape` (+ their `Config`/`Deterministic` lemmas: `withOutput`, `val_moveInputPos_*`, `inputSymbol_eq_none_of_boundary`) | 1 |
| **3** | `EmitTape` · `RewindTape` · `RewindInput` · `Clear` | 1, 2 |
| **4** | `Branch` · `Repeat` | 1, 2 |
| **5** | `NormalForms/Instrument` · `Sweep` · `Tidy` (+ `Sequential.seq_spec`, `Deterministic.inputPos_runFrom_le`) | 1–4 |
| **6** | `NormalForms/Adapters` (+ `Deterministic.length_encOut_le`, `length_output_runFrom_le`) | 1–5 |
| **7** | `Combinators/Comp` (`computableInTimeAndSpace_comp`) | 6 |
| **8** | `Combinators/Ite` (`cond`/`ite`/`dite`/`match`) | 6, 7, sibling AlmostConstant |
| **9** | `Combinators/Loop` (`computableInTimeAndSpace_loopFunction`) | 6, siblings Option/Id |

Siblings `AlmostConstant`, `Encodings/Option`, `Id` land via their own PRs (`loop/03`–`05`) and are
prerequisites for PRs 8–9.

## Notes / deferrals

- **`seq_spec`** (raw-configuration composition, `Plumbing/Sequential`) is *not* in PR 1. Its users
  are `Tidy` and `Adapters`, so it ships with **PR 5** (first user). PR 1 keeps only the
  interface-level `transformsTapes_seq`. On this campaign branch `seq_spec` is already present.
- **`withState`** was moved `TransformsTapes` → `Configuration` (it is a special case of
  `mapState`). Applied on this branch too.
- **Follow-up (known):** `isOptionEncoding_encOption` (`Encodings/Option`) is still `proof_wanted`,
  so `computableInTimeAndSpace_loopFunction` cannot yet be instantiated end-to-end with the
  canonical `Option` encoding. Sound conditional result; discharge to make loop usable with it.
- **Policy:** don't build on Sam's PRs (#872, tm-03..06); credit him as author where his design is
  used. Use Mathlib naming even where it conflicts with #872.
- Keep every PR building independently with `lake build --wfail` (+ `lake lint`, `lint-style`).
