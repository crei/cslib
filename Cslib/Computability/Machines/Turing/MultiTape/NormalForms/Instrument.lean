/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Instrumenting a machine with footprint tapes

`instrument tm mark` runs `tm` unchanged while pairing each of its `k` work tapes with a
*footprint* tape: the footprint head moves in lockstep with its partner, and every cell it stands
on gets the symbol `mark` — unless the cell is already nonblank, which is what preserves a
distinguished anchor placed at cell `0` beforehand. A head path is connected, so the marked region
of a footprint is an interval: the footprint restores, next to a tape whose garbage may contain
embedded blanks, the scannability that the garbage lacks. This is the run phase of the tidy
normal form (`Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Tidy`); the sweep phase
erases each pair by walking the footprint towards the anchor.

The instrumented machine relates to `tm` in two ways, and the split matters:

* everything except the footprints is a *projection*: `projCfg` forgets the footprint tapes, and
  `step` commutes with it unconditionally, so the instrumented run mirrors the original run by
  `Turing.MultiTapeTM.runFrom_comm_of_step` — no induction;
* the footprint contents are a function of the run's *history*, not of its current configuration,
  so they get their own run invariant: after `τ` live steps, footprint `j` carries `mark` exactly
  on the cells its partner's head occupied before time `τ`, on top of what it held initially.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with each work tape `j` paired with the footprint tape `k + j`: the footprint head
mirrors the moves of head `j` and writes `mark` on every blank cell it stands on, leaving nonblank
cells (in particular an anchor at cell `0`) alone. -/
@[expose] public def instrument (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + k) Symbol State where
  q₀ := tm.q₀
  tr q inp work :=
    let a := tm.tr q inp fun j => work (j.castAdd k)
    { inputTape := a.inputTape
      workTapes := Fin.addCases (fun j => a.workTapes j)
        (fun j => (match work (j.natAdd k) with
          | none => some (some mark)
          | some _ => none, (a.workTapes j).2))
      output := a.output
      state := a.state }

/-- Forgetting the footprint tapes of an instrumented configuration. -/
@[expose, simps] public def projCfg (c : Cfg (k + k) Symbol State input) :
    Cfg k Symbol State input :=
  ⟨c.state, c.inputPos, fun j => c.workTapes (j.castAdd k), fun j => c.workTapePos (j.castAdd k),
    c.output⟩

@[simp]
public lemma projCfg_inputSymbol (c : Cfg (k + k) Symbol State input) :
    (projCfg c).inputSymbol = c.inputSymbol := rfl

@[simp]
public lemma projCfg_workTapeSymbols (c : Cfg (k + k) Symbol State input) (j : Fin k) :
    (projCfg c).workTapeSymbols j = c.workTapeSymbols (j.castAdd k) := rfl

/-- The projection is a step-semiconjugation: the instrumented machine acts on everything except
the footprints exactly as the original does. -/
public lemma step_projCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg (k + k) Symbol State input) :
    tm.step (projCfg c) = projCfg ((tm.instrument mark).step c) := by
  cases hq : c.state with
  | none =>
    have h1 : (projCfg c).state = none := hq
    simp only [step, h1, hq]
  | some q =>
    have h1 : (projCfg c).state = some q := hq
    have hsym : (projCfg c).workTapeSymbols = fun j => c.workTapeSymbols (j.castAdd k) := rfl
    simp only [step, h1, hq, projCfg_inputSymbol, hsym]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext j z
      simp [Action.apply, instrument, Fin.addCases_left, projCfg]
    · funext j
      simp [Action.apply, instrument, Fin.addCases_left, projCfg]

/-- The instrumented run mirrors the original run, footprints aside. -/
public lemma runFrom_projCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg (k + k) Symbol State input) (n : ℕ) :
    tm.runFrom (projCfg c) n = projCfg ((tm.instrument mark).runFrom c n) :=
  runFrom_comm_of_step projCfg (fun c => step_projCfg tm mark c) c n

section Footprint

variable {tm : MultiTapeTM k Symbol State} {mark : Symbol}

/-- `Fin.addCases_right`, in the `addNat` spelling that `simp` normalises to. -/
private lemma addCases_addNat {γ : Sort*} (f : Fin k → γ) (g : Fin k → γ) (j : Fin k) :
    Fin.addCases (motive := fun _ => γ) f g (j.addNat k) = g j := by
  rw [← Fin.natAdd_eq_addNat]
  exact Fin.addCases_right j

/-- The action of the instrumented machine moves a footprint head exactly as it moves the
partner head. -/
private lemma instrument_move (q : State) (inp : Option Symbol)
    (work : Fin (k + k) → Option Symbol) (j : Fin k) :
    (((tm.instrument mark).tr q inp work).workTapes (j.addNat k)).2 =
      (((tm.instrument mark).tr q inp work).workTapes (j.castAdd k)).2 := by
  simp [instrument, Fin.addCases_left, addCases_addNat]

/-- What the instrumented machine writes on a footprint: `mark` if the cell under the head is
blank, nothing otherwise. -/
private lemma instrument_write (q : State) (inp : Option Symbol)
    (work : Fin (k + k) → Option Symbol) (j : Fin k) :
    (((tm.instrument mark).tr q inp work).workTapes (j.addNat k)).1 =
      match work (j.addNat k) with
      | none => some (some mark)
      | some _ => none := by
  simp [instrument, addCases_addNat]

/-- A live step moves each head by the amount its action prescribes. -/
private lemma step_workTapePos_of_state {C : Cfg (k + k) Symbol State input} {q : State}
    (hq : C.state = some q) (l : Fin (k + k)) :
    ((tm.instrument mark).step C).workTapePos l =
      C.workTapePos l +
        (((tm.instrument mark).tr q C.inputSymbol C.workTapeSymbols).workTapes l).2 := by
  simp [step, hq, Action.apply]

/-- Footprint heads stay aligned with their partners throughout a live run. -/
public lemma workTapePos_addNat_instrument (c : Cfg (k + k) Symbol State input) (j : Fin k)
    (halign : c.workTapePos (j.addNat k) = c.workTapePos (j.castAdd k)) (τ : ℕ)
    (hlive : ∀ m < τ, ((tm.instrument mark).runFrom c m).state ≠ none) :
    ((tm.instrument mark).runFrom c τ).workTapePos (j.addNat k) =
      ((tm.instrument mark).runFrom c τ).workTapePos (j.castAdd k) := by
  induction τ with
  | zero => exact halign
  | succ τ ih =>
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive τ (by omega))
    rw [runFrom_succ_eq_step', step_workTapePos_of_state hq, step_workTapePos_of_state hq,
      instrument_move, ih fun m hm => hlive m (by omega)]

/-- **The footprint invariant.** After `τ` live steps, footprint `j` holds `mark` on every cell
its partner's head occupied at an earlier time, on top of what it held initially — which is never
overwritten, so an anchor placed before the run survives it. -/
public lemma workTapes_addNat_instrument (c : Cfg (k + k) Symbol State input) (j : Fin k)
    (halign : c.workTapePos (j.addNat k) = c.workTapePos (j.castAdd k)) (τ : ℕ)
    (hlive : ∀ m < τ, ((tm.instrument mark).runFrom c m).state ≠ none) :
    ((tm.instrument mark).runFrom c τ).workTapes (j.addNat k) = fun z =>
      match c.workTapes (j.addNat k) z with
      | some s => some s
      | none =>
        if z ∈ (Finset.range τ).image
            (fun m => ((tm.instrument mark).runFrom c m).workTapePos (j.castAdd k)) then
          some mark
        else none := by
  induction τ with
  | zero =>
    funext z
    rcases h : c.workTapes (j.addNat k) z with _ | s <;> simp [h]
  | succ τ ih =>
    have hlive' : ∀ m < τ, ((tm.instrument mark).runFrom c m).state ≠ none :=
      fun m hm => hlive m (by omega)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive τ (by omega))
    set Cτ := (tm.instrument mark).runFrom c τ with hCτ
    -- the footprint head stands on the partner's position
    have hpos : Cτ.workTapePos (j.addNat k) = Cτ.workTapePos (j.castAdd k) :=
      workTapePos_addNat_instrument c j halign τ hlive'
    have hstep : ((tm.instrument mark).runFrom c (τ + 1)).workTapes (j.addNat k) =
        match (((tm.instrument mark).tr q Cτ.inputSymbol Cτ.workTapeSymbols).workTapes
            (j.addNat k)).1 with
        | none => Cτ.workTapes (j.addNat k)
        | some s =>
          Function.update (Cτ.workTapes (j.addNat k)) (Cτ.workTapePos (j.addNat k)) s := by
      rw [runFrom_succ_eq_step', ← hCτ]
      simp only [step, hq, Action.apply]
      rfl
    rw [hstep, instrument_write]
    have hmarks : (Finset.range (τ + 1)).image
        (fun m => ((tm.instrument mark).runFrom c m).workTapePos (j.castAdd k)) =
        insert (Cτ.workTapePos (j.castAdd k)) ((Finset.range τ).image
          (fun m => ((tm.instrument mark).runFrom c m).workTapePos (j.castAdd k))) := by
      rw [Finset.range_add_one, Finset.image_insert, hCτ]
    -- the current footprint cell, read through the invariant at time `τ`
    have hread : Cτ.workTapeSymbols (j.addNat k) =
        match c.workTapes (j.addNat k) (Cτ.workTapePos (j.castAdd k)) with
        | some s => some s
        | none =>
          if Cτ.workTapePos (j.castAdd k) ∈ (Finset.range τ).image
              (fun m => ((tm.instrument mark).runFrom c m).workTapePos (j.castAdd k)) then
            some mark
          else none := by
      simp only [Cfg.workTapeSymbols, hpos, ih hlive']
    rw [hread]
    funext z
    rcases hinit : c.workTapes (j.addNat k) (Cτ.workTapePos (j.castAdd k)) with _ | s
    · -- the cell under the head was initially blank
      by_cases hmem : Cτ.workTapePos (j.castAdd k) ∈ (Finset.range τ).image
          (fun m => ((tm.instrument mark).runFrom c m).workTapePos (j.castAdd k))
      · -- already marked: nothing written, and the new mark set adds nothing at this cell
        simp only [hmem, ite_true]
        rw [ih hlive', hmarks]
        rcases hz : c.workTapes (j.addNat k) z with _ | s
        · simp only [hz, Finset.mem_insert]
          by_cases hzp : z = Cτ.workTapePos (j.castAdd k)
          · subst hzp; simp [hmem]
          · simp [hzp]
        · simp [hz]
      · -- unmarked: the machine writes `mark` at the head position
        simp only [hmem, ite_false]
        rw [hpos, ih hlive', hmarks]
        by_cases hzp : z = Cτ.workTapePos (j.castAdd k)
        · subst hzp
          simp [Function.update_self, hinit]
        · rw [Function.update_of_ne hzp]
          rcases hz : c.workTapes (j.addNat k) z with _ | s
          · simp [hzp]
          · simp
    · -- the cell under the head was initially nonblank: nothing written
      rw [ih hlive', hmarks]
      rcases hz : c.workTapes (j.addNat k) z with _ | s
      · simp only [hz, Finset.mem_insert]
        by_cases hzp : z = Cτ.workTapePos (j.castAdd k)
        · subst hzp; simp_all
        · simp [hzp]
      · simp [hz]

end Footprint

section MarkAnchors

/-- The one-step machine that writes `mark` on every footprint tape at its head — placing the
anchors before an instrumented run — and halts. Everything else is untouched. -/
private def markAnchors (k : ℕ) (Symbol : Type*) (mark : Symbol) :
    MultiTapeTM (k + k) Symbol Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputTape := 0
      workTapes := Fin.addCases (fun _ => (none, 0)) (fun _ => (some (some mark), 0))
      output := none
      state := none }

/-- One step of `markAnchors`: anchors written at the footprint heads, nothing else changed. -/
public theorem exists_markAnchors (k : ℕ) (Symbol : Type*) (mark : Symbol) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM (k + k) Symbol State),
      ∀ (input : List Symbol) (c : Cfg (k + k) Symbol State input), c.state = some tm.q₀ →
        (tm.runFrom c 1).state = none ∧
        (tm.runFrom c 1).inputPos = c.inputPos ∧
        (tm.runFrom c 1).output = c.output ∧
        (tm.runFrom c 1).workTapePos = c.workTapePos ∧
        (∀ j : Fin k, (tm.runFrom c 1).workTapes (j.castAdd k) = c.workTapes (j.castAdd k)) ∧
        (∀ j : Fin k, (tm.runFrom c 1).workTapes (j.addNat k) =
          Function.update (c.workTapes (j.addNat k)) (c.workTapePos (j.addNat k)) (some mark)) := by
  refine ⟨Unit, inferInstance, markAnchors k Symbol mark, fun input c hq => ?_⟩
  have hstep : (markAnchors k Symbol mark).runFrom c 1 = (markAnchors k Symbol mark).step c := by
    rw [runFrom_succ_eq_step', runFrom_zero]
  rw [hstep]
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_, fun j => ?_⟩
  · simp [step, hq, Action.apply, markAnchors]
  · simp [step, hq, Action.apply, markAnchors]
  · simp [step, hq, Action.apply, markAnchors]
  · funext l
    induction l using Fin.addCases with
    | left j => simp [step, hq, Action.apply, markAnchors, Fin.addCases_left]
    | right j => simp [step, hq, Action.apply, markAnchors, addCases_addNat]
  · simp [step, hq, Action.apply, markAnchors, Fin.addCases_left]
  · simp [step, hq, Action.apply, markAnchors, addCases_addNat]

/-- The one-step machine that writes `mark` on every footprint tape at its head — but only on a
blank cell, so an anchor under a head survives. Run after an instrumented machine halts, it marks
the final head positions, which the run itself never wrote: the footprint then covers exactly the
visited cells. -/
private def markCurrent (k : ℕ) (Symbol : Type*) (mark : Symbol) :
    MultiTapeTM (k + k) Symbol Unit where
  q₀ := ()
  tr _ _ work :=
    { inputTape := 0
      workTapes := Fin.addCases (fun _ => (none, 0))
        (fun j => (match work (j.natAdd k) with
          | none => some (some mark)
          | some _ => none, 0))
      output := none
      state := none }

/-- One step of `markCurrent`: the cells under the footprint heads are marked if blank, nothing
else changes. -/
public theorem exists_markCurrent (k : ℕ) (Symbol : Type*) (mark : Symbol) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM (k + k) Symbol State),
      ∀ (input : List Symbol) (c : Cfg (k + k) Symbol State input), c.state = some tm.q₀ →
        (tm.runFrom c 1).state = none ∧
        (tm.runFrom c 1).inputPos = c.inputPos ∧
        (tm.runFrom c 1).output = c.output ∧
        (tm.runFrom c 1).workTapePos = c.workTapePos ∧
        (∀ j : Fin k, (tm.runFrom c 1).workTapes (j.castAdd k) = c.workTapes (j.castAdd k)) ∧
        (∀ j : Fin k, (tm.runFrom c 1).workTapes (j.addNat k) = fun z =>
          match c.workTapes (j.addNat k) z with
          | some s => some s
          | none =>
            if z = c.workTapePos (j.addNat k) ∧
                c.workTapes (j.addNat k) (c.workTapePos (j.addNat k)) = none then
              some mark
            else none) := by
  refine ⟨Unit, inferInstance, markCurrent k Symbol mark, fun input c hq => ?_⟩
  have hstep : (markCurrent k Symbol mark).runFrom c 1 = (markCurrent k Symbol mark).step c := by
    rw [runFrom_succ_eq_step', runFrom_zero]
  rw [hstep]
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_, fun j => ?_⟩
  · simp [step, hq, Action.apply, markCurrent]
  · simp [step, hq, Action.apply, markCurrent]
  · simp [step, hq, Action.apply, markCurrent]
  · funext l
    induction l using Fin.addCases with
    | left j => simp [step, hq, Action.apply, markCurrent, Fin.addCases_left]
    | right j =>
      rcases h : c.workTapeSymbols (j.natAdd k) with _ | s <;>
        simp [step, hq, Action.apply, markCurrent, addCases_addNat]
  · simp [step, hq, Action.apply, markCurrent, Fin.addCases_left]
  · funext z
    simp only [step, hq, Action.apply, markCurrent, addCases_addNat]
    rw [show c.workTapeSymbols (Fin.natAdd k j) =
        c.workTapes (j.addNat k) (c.workTapePos (j.addNat k)) from by
      rw [Fin.natAdd_eq_addNat]; rfl]
    rcases hcell : c.workTapes (j.addNat k) (c.workTapePos (j.addNat k)) with _ | s
    · -- blank under the head: write the mark there
      by_cases hz : z = c.workTapePos (j.addNat k)
      · subst hz
        simp [hcell, Function.update_self]
      · rcases hzc : c.workTapes (j.addNat k) z with _ | t <;>
          simp [hzc, hz]
    · -- nonblank under the head: no write
      rcases hzc : c.workTapes (j.addNat k) z with _ | t <;> simp [hzc]

end MarkAnchors

section Space

/-- An instrumented run uses exactly twice the space of the original: each footprint head visits
exactly the cells its partner visits. -/
public lemma spaceUsed_instrument (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg (k + k) Symbol State input) (τ : ℕ)
    (halign : ∀ j : Fin k, c.workTapePos (j.addNat k) = c.workTapePos (j.castAdd k))
    (hlive : ∀ m < τ, ((tm.instrument mark).runFrom c m).state ≠ none) :
    (tm.instrument mark).spaceUsed c τ = 2 * tm.spaceUsed (projCfg c) τ := by
  have hcast : ∀ (j : Fin k),
      (tm.instrument mark).visitedByTapeHead c τ (j.castAdd k) =
        tm.visitedByTapeHead (projCfg c) τ j := by
    intro j
    refine Finset.image_congr fun m hm => ?_
    rw [runFrom_projCfg tm mark]
    rfl
  have hnat : ∀ (j : Fin k),
      (tm.instrument mark).visitedByTapeHead c τ (j.addNat k) =
        tm.visitedByTapeHead (projCfg c) τ j := by
    intro j
    refine Finset.image_congr fun m hm => ?_
    have hm' : m ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [workTapePos_addNat_instrument c j (halign j) m fun r hr => hlive r (by omega),
      runFrom_projCfg tm mark]
    rfl
  rw [spaceUsed, spaceUsed, Fin.sum_univ_add, two_mul]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => congrArg Finset.card (hcast j)
  · refine Finset.sum_congr rfl fun j _ => congrArg Finset.card ?_
    -- natAdd vs addNat spelling
    rw [Fin.natAdd_eq_addNat]
    exact hnat j
end Space


end Turing.MultiTapeTM
