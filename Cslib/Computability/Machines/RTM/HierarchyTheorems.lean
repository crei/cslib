/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.TMSimulator
public import Cslib.Computability.Machines.RTM.PB

/-!
# Hierarchy Theorems

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak2009], Chapter 4

-/


@[expose] public section

namespace Turing

namespace RoseTreeMachine


variable {env : List Value} {α β : Type} [DataEncode α] [DataEncode β]

/-- A TM normalized to use `Fin k` for its `State` and `Symbol` type. -/
structure NormalizedTM where
  states : ℕ
  symbols : ℕ
  toSingleTapeTM : SingleTapeTM (Fin (symbols + 2))
  h_states : toSingleTapeTM.State = Fin (states + 1)

def NormalizedTM.Cfg (tm : NormalizedTM) := tm.toSingleTapeTM.Cfg

def NormalizedTM.step (tm : NormalizedTM) (cfg : tm.Cfg) : tm.Cfg :=
  match tm.toSingleTapeTM.step cfg with
  | none => cfg
  | some cfg' => cfg'

def binaryToFin {n : ℕ} (x : List Bool) : List (Fin (n + 2)) :=
  List.map (fun b => if b then 1 else 0) x

/-- If the TM `tm` is in the final state after at most `t` steps, returns the output.
Note that this is a slightly different output notion since we do not require the tape to be in
its canonical state. Also we just filter out any symbol that is not the encoding of a bool. -/
def NormalizedTM.output? (tm : NormalizedTM) (input : List Bool) (t : ℕ) : Option (List Bool) :=
  let cfg := tm.step^[t] (tm.toSingleTapeTM.initCfg (binaryToFin input))
  if cfg.state = none then
    (cfg.BiTape.head :: cfg.BiTape.right.toList).filterMap
      (fun c => match c with | some 0 => some false | some 1 => some true | _ => none)
  else
    none

def NormalizedTM.ComputesFunInTime (tm : NormalizedTM) (f : List Bool → List Bool) (t : ℕ → ℕ) :
    Prop :=
  ∀ input, ∃ t' < t input.length, tm.output? input t' = some (f input)

def DSPACE (t : ℕ → ℕ) := { f : List Bool → Bool | ∃ tm : NormalizedTM, ∃ a,
        tm.ComputesFunInTime (fun x => [f x]) fun n => a * t n + a }

/-- An enumeration of Turing machines such that every TM appears infinitely often in the
enumeration. -/
def Enumerates (e : ℕ → NormalizedTM) : Prop := ∀ tm n, ∃ n' > n, e n' = tm

-- /-- A universal machine for an enumeration can simulate any Turing machine from the enumeration
-- with quadratic overhead.
-- TODO: It is possible to have an overhead of `t log t`, but quadratic is fine for now. -/
-- def UniversalMachineSemantics_old
--     (allTMs : ℕ → NormalizedTM)
--     (p : PB → PB) : Prop :=
--   ∃ a, ∀ m input t, ∃ s, PB.ComputesEncInTimeAndSpace p
--     (t, input, m)
--     ((allTMs m).output? input t)
--     ((a * (allTMs m).states * (allTMs m).symbols * t * t) + a)
--     s

def simulator (allTMs : ℕ → NormalizedTM) (m : ℕ) (input : List Bool) (t : ℕ) :
    Option (List Bool) :=
  (allTMs m).output? input t

/-- A universal machine for an enumeration can simulate any Turing machine from the enumeration
with quadratic overhead.
TODO: It is possible to have an overhead of `t log t`, but quadratic is fine for now. -/
def UniversalMachineSemantics
    (allTMs : ℕ → NormalizedTM)
    (p : PB → PB) : Prop :=
  ∃ a, ∃ s, PB.ComputesFunEncInTimeAndSpace p
    (fun (m, input, t) => simulator allTMs m input t)
    (fun (m, _, t) =>
      -- The runtime of the simulation has an overhead in the "size" of the TM, but does not
      -- depend on the input.
      (a * (allTMs m).states * (allTMs m).symbols * t * t) + a)
    s

def succ (x : PB) : PB := sorry

def length (x : PB) : PB := sorry

theorem length_computes {p : PB} {x : List α} (h_p : p.ComputesEnc env x) :
  (length p).ComputesEnc env x.length := by
  sorry

/-- Computes `x * x` -/
def mul (x y : PB) : PB := sorry

theorem mul_computes {p q : PB} {x y : ℕ} (h_p : p.ComputesEnc env x) (h_q : q.ComputesEnc env y) :
  (mul p q).ComputesEnc env (x * y) := by
  sorry

def cube (x : PB) : PB := mul (mul x x) x

theorem cube_computes {p : PB} {x : ℕ} (h_p : p.ComputesEnc env x) :
  (cube p).ComputesEnc env (x * x * x) := by
  exact mul_computes (mul_computes h_p h_p) h_p

/-- Run the universal machine on (x, x, |x|^3) and invert its output, if it halts. -/
def diagonalizer (p : PB → PB) (x : PB) : PB :=
  let output := p (PB.toPair x (PB.toPair x (cube (length x))))
  PB.ifEq output (PB.constantEnc (Option.some [true]))
      (PB.constantEnc [false])
      (PB.constantEnc [true])

/-- Semantic core of the diagonalizer (resources ignored): if the inner universal-machine call
outputs `some [b]`, the diagonalizer outputs the inverted bit `[!b]`. This isolates the inversion
logic from the resource bound and from the `log`/`mul`/`cube` stubs. -/
theorem diagonalizer_inverts
    {p_u : PB → PB}
    {f_u : ℕ × List Bool × ℕ → List Bool}
    {h_u : PB.ComputesFunEnc p_u f_u}
    {p_in : PB}
    {x : ℕ}
    {h_in : p_in.ComputesEnc env x} :
    (diagonalizer p_u p_in).ComputesEnc env [!(f_u (x, Nat.bits x, x * x * x) = [true])] :=
  match f_u (x, Nat.bits x, x * x * x) with
  | [true] => by
    refine PB.ifeq_eq_computes ?_ PB.constantEnc_computesEnc PB.constantEnc_computesEnc
    sorry
  | _ => by
    -- refine PB.ifeq_ne_computes ?_ PB.constantEnc_computesEnc ?_ ?_
    sorry

theorem hierarchy
    (enum : ℕ → NormalizedTM)
    (h_enum : Enumerates enum)
    (h_exists_univ : ∃ p, UniversalMachineSemantics enum p) :
    DSPACE id ≠ DSPACE (fun n => n^5) := by
  obtain ⟨h, h_u⟩ := h_exists_univ
  let diag := fun x : List Bool =>
    let n := Nat.ofBits x.get
    simulator enum n x (n * n * n) != some [true]
  let m := diagonalizer h
  -- TODO m computes diagm in a certain time, therfore it is in DSPACE (fun n => n^5)
  have h_diag_in_quint : diag ∈ DSPACE (fun n => n^5) := by
     sorry
  have h_notin_linear : diag ∉ DSPACE id := by
    intro h_linear
    obtain ⟨tm, a, h_tm⟩ := h_linear

    sorry
  intro h_eq
  simp_all

end RoseTreeMachine

end Turing
