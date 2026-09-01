/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.InputCursor
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeStep

/-!
# A finite stand-in for a whole configuration

`MultiTapeTM.Cfg` is not encodable: its `workTapes` field is a family of *functions*
`ℤ → Option Symbol`. `SimCfg` replaces that family by a list of zippers and the input head by a
cursor, so every component is a finite value and the whole configuration inherits `DataEncode`
from the `Prod`, `List` and `Option` instances — no new instance, no new assumption.

`Represents` says a stand-in denotes a given real configuration. The two theorems here are the
*observation* half of a step simulation: under `Represents`, the stand-in reads exactly the input
symbol and exactly the work-head symbols that the real machine reads. Since `MultiTapeTM.step`
consults `tm.tr` on precisely those two, the same transition fires on both sides.

The *update* half — that carrying out that transition on the stand-in denotes the updated
configuration — is assembled from lemmas already proved elsewhere: `cursorR_repr`/`cursorL_repr`
for the input head (including `moveInputPos`'s clamping), and `tapeFun_applyAction` for each work
tape.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace Simulation

open RoseTreeMachine

/-- A finite stand-in for a configuration: the state, a cursor into the padded input, one zipper
per work tape, and the output produced so far. Every component is finite, so this is encodable
where `Cfg` is not. -/
abbrev SimCfg (sym state : ℕ) :=
  Option (Fin state) × Cursor (Option (Fin sym)) × List (Tape (Option (Fin sym))) × List (Fin sym)

/-- The zipper the stand-in holds for work tape `i`. -/
def workZipper {sym state : ℕ} (sc : SimCfg sym state) (i : ℕ) : Tape (Option (Fin sym)) :=
  (sc.2.2.1[i]?).getD ([], [])

/-- `sc` denotes the configuration `cfg`: same state, the cursor sits where the input head does,
each zipper denotes the corresponding work tape at its head position, and the outputs agree. -/
def Represents {k sym state : ℕ} {inp : List (Fin sym)}
    (sc : SimCfg sym state) (cfg : Cfg k (Fin sym) (Fin state) inp) : Prop :=
  sc.1 = cfg.state
    ∧ CursorRepr inp sc.2.1 cfg.inputPos
    ∧ sc.2.2.1.length = k
    ∧ (∀ i : Fin k, cfg.workTapes i = tapeFun none (workZipper sc i.val) (cfg.workTapePos i))
    ∧ sc.2.2.2 = cfg.output

/-- **The stand-in reads the input symbol the machine reads.** -/
lemma Represents.inputSymbol {k sym state : ℕ} {inp : List (Fin sym)}
    {sc : SimCfg sym state} {cfg : Cfg k (Fin sym) (Fin state) inp}
    (h : Represents sc cfg) :
    cursorRead none sc.2.1 = cfg.inputSymbol := by
  rw [cursorRead_eq h.2.1, inputSymbol_eq]

/-- **The stand-in reads the work-head symbols the machine reads.** -/
lemma Represents.workSymbols {k sym state : ℕ} {inp : List (Fin sym)}
    {sc : SimCfg sym state} {cfg : Cfg k (Fin sym) (Fin state) inp}
    (h : Represents sc cfg) (i : Fin k) :
    read none (workZipper sc i.val) = cfg.workTapeSymbols i := by
  have hw := h.2.2.2.1 i
  unfold Cfg.workTapeSymbols
  rw [hw, tapeFun_self]

/-- **The stand-in sees the same transition argument as the machine**, hence the very same
transition fires: `MultiTapeTM.step` consults `tm.tr` on exactly the state, input symbol and
work-head symbols that `Represents` pins down. -/
lemma Represents.tr_eq {k sym state : ℕ} {inp : List (Fin sym)}
    {sc : SimCfg sym state} {cfg : Cfg k (Fin sym) (Fin state) inp}
    (h : Represents sc cfg) (tm : MultiTapeTM k (Fin sym) (Fin state)) (q : Fin state) :
    tm.tr q (cursorRead none sc.2.1) (fun i => read none (workZipper sc i.val))
      = tm.tr q cfg.inputSymbol cfg.workTapeSymbols := by
  rw [h.inputSymbol]
  congr 1
  funext i
  exact h.workSymbols i

/-! ### The update half: one simulated step -/

/-- Move the input cursor according to a `SignType`. -/
def moveCursor {α : Type} (blank : α) (m : SignType) (c : Cursor α) : Cursor α :=
  match m with
  | .zero => c
  | .neg => cursorL blank c
  | .pos => cursorR blank c

lemma moveCursor_zero {α : Type} (blank : α) (c : Cursor α) :
    moveCursor blank SignType.zero c = c := rfl

lemma moveCursor_neg {α : Type} (blank : α) (c : Cursor α) :
    moveCursor blank SignType.neg c = cursorL blank c := rfl

lemma moveCursor_pos {α : Type} (blank : α) (c : Cursor α) :
    moveCursor blank SignType.pos c = cursorR blank c := rfl

/-- **Moving the cursor implements `moveInputPos`**, clamping included. -/
lemma cursorMove_repr {Symbol : Type} {input : List Symbol} {c : Cursor (Option Symbol)}
    {pos : Fin (input.length + 2)} (d : Option Symbol) (m : SignType)
    (h : CursorRepr input c pos) :
    CursorRepr input (moveCursor d m c) (moveInputPos pos m) := by
  cases m with
  | zero => simpa [moveCursor] using h
  | neg => exact cursorL_repr d h
  | pos => exact cursorR_repr d h

/-- One step of the simulated machine on the finite stand-in. (Named `cfgStep` to avoid
clashing with `Simulation.simStep`, which steps a machine with a *fixed* transition function.) -/
def cfgStep {k sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (sc : SimCfg sym state) : SimCfg sym state :=
  match sc.1 with
  | none => sc
  | some q =>
    let o := tm.tr q (cursorRead none sc.2.1) (fun i : Fin k => read none (workZipper sc i.val))
    (o.q',
     moveCursor none o.inputMove sc.2.1,
     List.ofFn (fun i : Fin k => applyAction none (o.workActions i) (workZipper sc i.val)),
     sc.2.2.2 ++ o.outS.toList)

/-! ### Field-by-field projections of `MultiTapeTM.step`

`MultiTapeTM.step` is a `match` on `cfg.state` returning an anonymous structure, so reasoning
about one of its fields by unfolding it inside a larger proof drags the whole record along — and
`simp` then normalises `tm.tr` to the raw projection on one side of the goal only. These five
lemmas do the unfolding once each, in a form already phrased with `tm.tr`. They belong next to
`step` itself (cslib has `step_output` in the same spirit); anything else that simulates `step`
will want them. -/

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

lemma step_state (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) :
    (tm.step cfg).state = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).q' := by
  unfold MultiTapeTM.step
  rw [hq]

lemma step_inputPos (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) :
    (tm.step cfg).inputPos
      = moveInputPos cfg.inputPos (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove := by
  unfold MultiTapeTM.step
  rw [hq]

lemma step_workTapePos (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapePos i
      = cfg.workTapePos i + ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).2 := by
  unfold MultiTapeTM.step
  rw [hq]

lemma step_workTapes (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapes i
      = stepTape (cfg.workTapes i) (cfg.workTapePos i)
          ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).1 := by
  cases ha : ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).1 with
  | none => simp [MultiTapeTM.step, stepTape, hq, ha]
  | some s => simp [MultiTapeTM.step, stepTape, hq, ha]

lemma step_output' (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) :
    (tm.step cfg).output
      = cfg.output ++ (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).outS.toList := by
  unfold MultiTapeTM.step
  rw [hq]

/-- **The finite step simulates `MultiTapeTM.step`.**

Every field is accounted for: the state and output directly, the input head through
`cursorMove_repr` (so `moveInputPos`'s clamping is respected), and each work tape through
`tapeFun_applyAction`. Because `Represents.tr_eq` shows the stand-in sees exactly the arguments the
machine passes to `tm.tr`, the *same* transition drives both sides. -/
lemma Represents.step {sym state : ℕ} {inp : List (Fin sym)}
    {sc : SimCfg sym state} {cfg : Cfg k (Fin sym) (Fin state) inp}
    (tm : MultiTapeTM k (Fin sym) (Fin state)) (h : Represents sc cfg) :
    Represents (cfgStep tm sc) (tm.step cfg) := by
  obtain ⟨hstate, hcur, hlen, hwork, hout⟩ := h
  cases hq : sc.1 with
  | none =>
    have hcfg : cfg.state = none := by rw [← hstate, hq]
    have h1 : cfgStep tm sc = sc := by simp [cfgStep, hq]
    have h2 : tm.step cfg = cfg := MultiTapeTM.step_of_halt hcfg
    rw [h1, h2]
    exact ⟨hstate, hcur, hlen, hwork, hout⟩
  | some q =>
    have hcfg : cfg.state = some q := by rw [← hstate, hq]
    have htr : tm.tr q (cursorRead none sc.2.1)
        (fun i : Fin k => read none (workZipper sc i.val))
        = tm.tr q cfg.inputSymbol cfg.workTapeSymbols :=
      Represents.tr_eq ⟨hstate, hcur, hlen, hwork, hout⟩ tm q
    have hsim : cfgStep tm sc =
        ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).q',
         moveCursor none (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove sc.2.1,
         List.ofFn (fun i : Fin k =>
           applyAction none ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i)
             (workZipper sc i.val)),
         sc.2.2.2 ++ (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).outS.toList) := by
      simp only [cfgStep, hq, htr]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsim, step_state tm cfg q hcfg]
    · rw [hsim, step_inputPos tm cfg q hcfg]
      exact cursorMove_repr none _ hcur
    · rw [hsim]
      simp
    · intro i
      have hz : workZipper (cfgStep tm sc) i.val
          = applyAction none ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i)
              (workZipper sc i.val) := by
        rw [hsim]
        unfold workZipper
        rw [List.getElem?_ofFn, dite_eq_left i.isLt]
        simp
      rw [hz, step_workTapePos tm cfg q hcfg i, tapeFun_applyAction, ← hwork i,
        step_workTapes tm cfg q hcfg i]
    · rw [hsim, step_output' tm cfg q hcfg]
      simp only []
      rw [hout]

/-- How `cfgStep` acts on a single work zipper, given the transition it uses. -/
lemma workZipper_cfgStep {sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (sc : SimCfg sym state) (q : Fin state) (hq : sc.1 = some q)
    (o : TransitionOut k (Fin sym) (Fin state))
    (ho : tm.tr q (cursorRead none sc.2.1)
      (fun j : Fin k => read none (workZipper sc j.val)) = o) (i : Fin k) :
    workZipper (cfgStep tm sc) i.val
      = applyAction none (o.workActions i) (workZipper sc i.val) := by
  have hsim : cfgStep tm sc =
      (o.q', moveCursor none o.inputMove sc.2.1,
       List.ofFn (fun j : Fin k => applyAction none (o.workActions j) (workZipper sc j.val)),
       sc.2.2.2 ++ o.outS.toList) := by
    simp only [cfgStep, hq, ho]
  rw [hsim]
  unfold workZipper
  rw [List.getElem?_ofFn, dite_eq_left i.isLt]
  simp

/-! ### Assembly: a finite computation reproduces the whole run -/

/-- The finite stand-in for the initial configuration: the start state, the cursor just past the
left blank, one empty zipper per work tape, and no output. -/
def initSimCfg {sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (inp : List (Fin sym)) : SimCfg sym state :=
  (some tm.q₀, ([none], inp.map some ++ [none]),
   List.replicate k (([], []) : Tape (Option (Fin sym))), [])

/-- A fresh zipper denotes the all-blank tape. -/
lemma tapeFun_empty {α : Type} (blank : α) (p : ℤ) :
    tapeFun blank (([], []) : Tape α) p = fun _ => blank := by
  funext z
  by_cases h : z < p <;> simp [tapeFun, h]

/-- **The finite stand-in denotes the initial configuration.** -/
lemma initRepresents {sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (inp : List (Fin sym)) :
    Represents (initSimCfg tm inp) (tm.initCfg inp) := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_, ?_, rfl⟩
  · simp [initSimCfg]
  · simp [initSimCfg, padded]
  · simp [initSimCfg]
  · intro i
    have hz : workZipper (initSimCfg tm inp) i.val = (([], []) : Tape (Option (Fin sym))) := by
      unfold workZipper initSimCfg
      simp [i.isLt]
    rw [hz, tapeFun_empty]
    simp

/-- **`Represents` is preserved along a whole run.** -/
lemma Represents.runFrom {sym state : ℕ} {inp : List (Fin sym)}
    {sc : SimCfg sym state} {cfg : Cfg k (Fin sym) (Fin state) inp}
    (tm : MultiTapeTM k (Fin sym) (Fin state)) (h : Represents sc cfg) (t : ℕ) :
    Represents ((cfgStep tm)^[t] sc) (tm.runFrom cfg t) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    rw [Function.iterate_succ_apply', MultiTapeTM.runFrom_succ_eq_step']
    exact Represents.step tm ih

/-- **The simulation theorem.** Iterating the finite step from the finite initial configuration
denotes the machine's real configuration after the same number of steps — for every number of
tapes, alphabet size and state count. Both sides of `Represents` are ordinary values here: the
left one is encodable, the right one is not. -/
theorem simulates {sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (inp : List (Fin sym)) (t : ℕ) :
    Represents ((cfgStep tm)^[t] (initSimCfg tm inp)) (tm.runFrom (tm.initCfg inp) t) :=
  Represents.runFrom tm (initRepresents tm inp) t

/-- **The simulated run produces the machine's output.** -/
theorem simulates_output {sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (inp : List (Fin sym)) (t : ℕ) :
    ((cfgStep tm)^[t] (initSimCfg tm inp)).2.2.2 = (tm.runFrom (tm.initCfg inp) t).output :=
  (simulates tm inp t).2.2.2.2

/-- **The simulated run halts exactly when the machine does.** -/
theorem simulates_state {sym state : ℕ} (tm : MultiTapeTM k (Fin sym) (Fin state))
    (inp : List (Fin sym)) (t : ℕ) :
    ((cfgStep tm)^[t] (initSimCfg tm inp)).1 = (tm.runFrom (tm.initCfg inp) t).state :=
  (simulates tm inp t).1

end Simulation

end MultiTapeTM

end Turing
