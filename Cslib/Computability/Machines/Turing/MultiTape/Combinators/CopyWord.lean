/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OnWords
import Mathlib.Tactic.FinCases

/-!
# Moving words between tapes

Three machines, built from the tidy identity `Turing.MultiTapeTM.tidyCopy`, that move a word
between the input, the work tapes and the output, leaving everything else as it is:

* `Turing.MultiTapeTM.loadWord Symbol i` writes the input to the blank work tape `i`;
* `Turing.MultiTapeTM.copyWord e mark` copies the word on tape `e 1` to the blank tape `e 0`;
* `Turing.MultiTapeTM.emitWord e mark` outputs the word on tape `e 0`.

The last two use a further blank tape to flag the left end of the word with `mark`.

## Main results

* `Turing.MultiTapeTM.transformsTapes_loadWord`, `Turing.MultiTapeTM.transformsTapes_copyWord`,
  `Turing.MultiTapeTM.transformsTapes_emitWord`: their specifications.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*}

/-- Writes the input to the work tape `i`. -/
public noncomputable def loadWord (Symbol : Type*) (i : Fin k) :
    MultiTapeTM k Symbol ((Unit ⊕ RewindState) ⊕ RewindWorkState) :=
  ((tidyCopy Symbol).outputToWord).extendTapes (tapeEmb i)

/-- Copies the word on tape `e 1` to tape `e 0`, using tape `e 2` to flag the left end of the word
with `mark`. -/
public noncomputable def copyWord (e : Fin (0 + 1 + 2) ↪ Fin k) (mark : Symbol) :
    MultiTapeTM k Symbol
      (MarkWorkState ⊕ ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕ MarkWorkState) :=
  ((tidyCopy Symbol).onWords mark).extendTapes e

/-- Outputs the word on tape `e 0`, using tape `e 1` to flag the left end of the word with
`mark`. -/
public noncomputable def emitWord (e : Fin (0 + 2) ↪ Fin k) (mark : Symbol) :
    MultiTapeTM k Symbol (MarkWorkState ⊕ (Unit ⊕ RewindState) ⊕ MarkWorkState) :=
  ((tidyCopy Symbol).inputFromWord mark).extendTapes e

/-- `loadWord Symbol i` writes the input `v` to the blank tape `i` and changes nothing else. -/
public theorem transformsTapes_loadWord (i : Fin k) (v : List Symbol) :
    TransformsTapes (loadWord Symbol i) (fun inp ws => inp = v ∧ ws i = [])
      (fun _ ws ws' e => ws' = Function.update ws i v ∧ e = [])
      (3 * v.length + 6) (2 * v.length + k + 2) :=
  ((computesTidily_tidyCopy v).outputToWord.tapeEmb i).imp
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, funext fun _ => hws⟩)
    (fun _ _ _ _ _ ⟨u, ⟨hu, he⟩, hws'⟩ => ⟨by rw [hws', hu]; simp, he⟩) (by omega)
    (by have := i.pos; omega)

/-- `copyWord e mark` writes the word `v` on tape `e 1` to the blank tape `e 0`, given a blank tape
`e 2`, and changes nothing else. -/
public theorem transformsTapes_copyWord (e : Fin (0 + 1 + 2) ↪ Fin k) (mark : Symbol)
    (v : List Symbol) :
    TransformsTapes (copyWord e mark) (fun _ ws => ws (e 1) = v ∧ ws (e 0) = [] ∧ ws (e 2) = [])
      (fun _ ws ws' em => ws' = Function.update ws (e 0) v ∧ em = [])
      (3 * v.length + 10) (4 * v.length + k + 15) := by
  refine (((computesTidily_tidyCopy v).onWords mark).extendTapes e).imp
    (fun _ ws ⟨h1, h0, h2⟩ => ?_)
    (fun _ ws ws' _ ⟨h1, h0, h2⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨?_, he⟩) (by omega) (by omega)
  · funext j
    fin_cases j <;> simp [h0, h1, h2]
  · funext l
    by_cases hl : l ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hl
      have := congrFun hv j
      fin_cases j <;> simp_all [e.injective.eq_iff]
    · rw [hx l hl, Function.update_of_ne fun h => hl ⟨0, h.symm⟩]

/-- `emitWord e mark` outputs the word `v` on tape `e 0`, given a blank tape `e 1`, and changes no
tape. -/
public theorem transformsTapes_emitWord (e : Fin (0 + 2) ↪ Fin k) (mark : Symbol)
    (v : List Symbol) :
    TransformsTapes (emitWord e mark) (fun _ ws => ws (e 0) = v ∧ ws (e 1) = [])
      (fun _ ws ws' em => ws' = ws ∧ em = v) (2 * v.length + 8) (2 * v.length + k + 10) := by
  obtain ⟨hrun, hspace⟩ := computesTidily_iff.mp (computesTidily_tidyCopy v)
  have happend (ws : Fin k → List Symbol) (h0 : ws (e 0) = v) (h1 : ws (e 1) = []) :
      (fun j => ws (e j)) = Fin.append (fun _ : Fin 0 => []) ![v, []] := by
    funext j
    fin_cases j <;> assumption
  refine ((transformsTapes_inputFromWord_of_runFrom mark hrun hspace).extendTapes e).imp
    (fun _ ws ⟨h0, h1⟩ => happend ws h0 h1)
    (fun _ ws ws' _ ⟨h0, h1⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨?_, he⟩) (by omega) (by omega)
  funext l
  by_cases hl : l ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hl
    exact (congrFun hv j).trans (congrFun (happend ws h0 h1) j).symm
  · exact hx l hl

end Turing.MultiTapeTM
