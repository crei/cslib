/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Constant space is the same as no work tapes

A multi-tape Turing machine that never uses more than a constant number `s` of work-tape cells can
be replaced by a machine without any work tapes at all (`k = 0`), computing the same outputs in
exactly the same number of steps.

The converse is trivial: a machine without work tapes uses zero space
(`MultiTapeTM.spaceUsed_zero_tapes_eq_zero`), which is bounded by any constant.

## Design

The simulating machine `MultiTapeTM.zeroTapeSim tm s` stores the whole (bounded) work-tape
situation of `tm` in its finite state: for every tape, the contents of the window `[-s, s]` and the
position of the head inside that window. Since a computation starts with all heads at `0` and moves
by at most one cell per step, a computation that visits at most `s` cells per tape keeps every head
inside this window (`MultiTapeTM.natAbs_workTapePos_le`), so no information is lost. Head moves that
would leave the window are clamped; this never happens along a space-bounded computation.

The simulation is step-by-step: `zeroTapeSim tm s` performs the same input-head move and emits the
same output symbol as `tm` in every step, so time bounds are preserved exactly, and it halts in
exactly the same step.

The window argument (positions and non-blank cells stay within `[-s, s]`) is the same one used for
counting reachable configurations of space-bounded machines; here only the bound on the head
positions is needed, since the simulating state agrees with the simulated tape only inside the
window.

## Important Declarations

* `MultiTapeTM.zeroTapeSim`: the simulating machine without work tapes
* `MultiTapeTM.Sim`: the invariant relating configurations of `tm` and of `zeroTapeSim tm s`
* `MultiTapeTM.ComputesInTimeAndSpace.zeroTapeSim`: the simulating machine computes the same output
  in the same time, using zero space
* `MultiTapeTM.ComputesFunInTimeAndSpace.zeroTapeSim`: a constant-space machine computing a function
  can be replaced by the machine `zeroTapeSim` without work tapes
* `MultiTapeTM.exists_zeroTape_computesFun_iff`: "constant space" and "no work tapes" describe the
  same functions (with the same time bound)
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}
variable {s : ℕ}

/-! ## The window of tape cells available to a space-bounded computation -/

/-- The window `[-s, s]` of tape positions available to a tape that uses at most `s` cells. -/
def window (s : ℕ) : Finset ℤ := Finset.Icc (-(s : ℤ)) s

@[scoped grind =]
lemma mem_window {z : ℤ} : z ∈ window s ↔ z.natAbs ≤ s := by
  grind [window]

/-- Restrict a tape position to the window, mapping positions outside of it to `0`.
Along a computation that uses at most `s` cells the clamping never takes effect. -/
def clampWindow (s : ℕ) (z : ℤ) : ↥(window s) :=
  if h : z ∈ window s then ⟨z, h⟩ else ⟨0, mem_window.mpr (Nat.zero_le _)⟩

@[simp]
lemma clampWindow_val {z : ℤ} (h : z ∈ window s) : (clampWindow s z : ℤ) = z := by
  simp [clampWindow, h]

/-! ## The simulating machine without work tapes -/

/-- The state of a machine that simulates the `k` work tapes of a space-`s`-bounded machine in its
state: the simulated state together with the contents of the window `[-s, s]` of every work tape
and the position of every work-tape head inside that window. -/
structure ConstSpaceState (Symbol State : Type*) (k s : ℕ) where
  /-- the state of the simulated machine (cf. `Cfg.state`) -/
  state : State
  /-- the contents of the window of work tape `i` (cf. `Cfg.workTapes`) -/
  workTapes (i : Fin k) : ↥(window s) → Option Symbol
  /-- the position of the head of work tape `i` (cf. `Cfg.workTapePos`) -/
  workTapePos (i : Fin k) : ↥(window s)

/-- A `ConstSpaceState` is just a product of its fields; this equivalence provides its `Fintype`
instance. -/
def ConstSpaceState.equivProd (Symbol State : Type*) (k s : ℕ) :
    ConstSpaceState Symbol State k s ≃
      State × ((i : Fin k) → ↥(window s) → Option Symbol) × (Fin k → ↥(window s)) where
  toFun x := (x.state, x.workTapes, x.workTapePos)
  invFun := fun ⟨state, workTapes, workTapePos⟩ => ⟨state, workTapes, workTapePos⟩

instance (Symbol State : Type*) [Fintype Symbol] [Fintype State] (k s : ℕ) :
    Fintype (ConstSpaceState Symbol State k s) :=
  Fintype.ofEquiv _ (ConstSpaceState.equivProd Symbol State k s).symm

/-- The machine without work tapes that simulates `tm` under the assumption that `tm` uses at most
`s` cells of work-tape space: it keeps the work tapes of `tm` in its state and performs the same
input-head moves and outputs as `tm`. -/
def zeroTapeSim (tm : MultiTapeTM k Symbol State) (s : ℕ) :
    MultiTapeTM 0 Symbol (ConstSpaceState Symbol State k s) where
  q₀ := ⟨tm.q₀, fun _ _ => none, fun _ => clampWindow s 0⟩
  tr q inputSymbol _ :=
    let out := tm.tr q.state inputSymbol fun i => q.workTapes i (q.workTapePos i)
    { inputMove := out.inputMove
      workActions := fun i => i.elim0
      outS := out.outS
      q' := out.q'.map fun q'' =>
        { state := q''
          workTapes := fun i =>
            match (out.workActions i).1 with
            | none => q.workTapes i
            | some sym => Function.update (q.workTapes i) (q.workTapePos i) sym
          workTapePos := fun i =>
            clampWindow s ((q.workTapePos i : ℤ) + ((out.workActions i).2 : ℤ)) } }

/-! ## The simulation invariant -/

/-- The invariant relating a configuration `c` of `tm` with a configuration `c'` of
`zeroTapeSim tm s`: both are at the same input position, in the same state, and (if not halted) the
state of `c'` records the work tapes of `c` inside the window and the work-tape head positions. -/
structure Sim (s : ℕ) (c : Cfg k Symbol State input)
    (c' : Cfg 0 Symbol (ConstSpaceState Symbol State k s) input) : Prop where
  /-- both machines are at the same input position -/
  inputPos : c'.inputPos = c.inputPos
  /-- both machines are in the same state (in particular, one has halted iff the other has) -/
  state : c.state = c'.state.map ConstSpaceState.state
  /-- the simulating state records the work tapes inside the window -/
  workTapes : ∀ q' ∈ c'.state, ∀ (i : Fin k) (z : ↥(window s)),
    q'.workTapes i z = c.workTapes i (z : ℤ)
  /-- the simulating state records the work-tape head positions -/
  workTapePos : ∀ q' ∈ c'.state, ∀ i : Fin k, (q'.workTapePos i : ℤ) = c.workTapePos i

/-- Simulated and simulating machine read the same work-tape symbols. -/
private lemma sim_read {c : Cfg k Symbol State input}
    {c' : Cfg 0 Symbol (ConstSpaceState Symbol State k s) input}
    {q' : ConstSpaceState Symbol State k s}
    (hsim : Sim s c c') (hq' : c'.state = some q') :
    (fun i => q'.workTapes i (q'.workTapePos i)) = c.workTapeSymbols := by
  funext i
  rw [hsim.workTapes q' hq' i (q'.workTapePos i), hsim.workTapePos q' hq' i]
  rfl

/-- One step of the simulating machine mirrors one step of the simulated machine, provided the
work-tape heads stay inside the window. -/
lemma sim_step {c : Cfg k Symbol State input}
    {c' : Cfg 0 Symbol (ConstSpaceState Symbol State k s) input}
    (hsim : Sim s c c')
    (hpos : ∀ i, ((tm.step c).workTapePos i).natAbs ≤ s) :
    Sim s (tm.step c) ((tm.zeroTapeSim s).step c') := by
  rcases hq' : c'.state with _ | q'
  · -- Both machines have halted, so both configurations are unchanged.
    have hc : c.state = none := by rw [hsim.state, hq']; rfl
    rw [step_of_halt hc, step_of_halt hq']
    exact hsim
  · have hc : c.state = some q'.state := by rw [hsim.state, hq']; rfl
    -- Both machines evaluate the transition function on the same arguments.
    set out := tm.tr q'.state c.inputSymbol c.workTapeSymbols with hout
    have hinputSymbol : c'.inputSymbol = c.inputSymbol := by
      simp [Cfg.inputSymbol, hsim.inputPos]
    have hstep' : (tm.zeroTapeSim s).step c' =
        { state := out.q'.map fun q'' =>
            { state := q''
              workTapes := fun i =>
                match (out.workActions i).1 with
                | none => q'.workTapes i
                | some sym => Function.update (q'.workTapes i) (q'.workTapePos i) sym
              workTapePos := fun i =>
                clampWindow s ((q'.workTapePos i : ℤ) + ((out.workActions i).2 : ℤ)) },
          inputPos := moveInputPos c'.inputPos out.inputMove,
          workTapes := fun i => i.elim0,
          workTapePos := fun i => i.elim0 } := by
      unfold step zeroTapeSim
      rw [hq']
      simp only [hinputSymbol, sim_read hsim hq', ← hout]
      exact Cfg.ext rfl rfl (funext fun i => i.elim0) (funext fun i => i.elim0)
    have hstep : tm.step c =
        { state := out.q',
          inputPos := moveInputPos c.inputPos out.inputMove,
          workTapes := fun i =>
            match (out.workActions i).1 with
            | none => c.workTapes i
            | some sym => Function.update (c.workTapes i) (c.workTapePos i) sym,
          workTapePos := fun i => c.workTapePos i + ((out.workActions i).2 : ℤ) } := by
      unfold step
      rw [hc]
      rfl
    rw [hstep, hstep']
    refine ⟨by rw [hsim.inputPos], by rcases out.q' with _ | q₂ <;> simp, ?_, ?_⟩
    · rintro q'' hq'' i z
      simp only [Option.mem_def, Option.map_eq_some_iff] at hq''
      obtain ⟨q₂, _, rfl⟩ := hq''
      -- The written cell is the one under the head, which lies inside the window.
      rcases hw : (out.workActions i).1 with _ | sym
      · simpa [hw] using hsim.workTapes q' hq' i z
      · have hz : (z = q'.workTapePos i) ↔ ((z : ℤ) = c.workTapePos i) := by
          rw [← hsim.workTapePos q' hq' i, Subtype.ext_iff]
        simp only [hw]
        by_cases h : z = q'.workTapePos i
        · rw [hz.mp h, h, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h, Function.update_of_ne (fun hc => h (hz.mpr hc))]
          exact hsim.workTapes q' hq' i z
    · rintro q'' hq'' i
      simp only [Option.mem_def, Option.map_eq_some_iff] at hq''
      obtain ⟨q₂, _, rfl⟩ := hq''
      have hin : (q'.workTapePos i : ℤ) + ((out.workActions i).2 : ℤ) ∈ window s := by
        have := hpos i
        rw [hstep] at this
        rw [mem_window, hsim.workTapePos q' hq' i]
        simpa using this
      rw [clampWindow_val hin, hsim.workTapePos q' hq' i]

/-- The simulating machine emits the same symbols as the simulated machine. -/
lemma sim_outputSymbol {c : Cfg k Symbol State input}
    {c' : Cfg 0 Symbol (ConstSpaceState Symbol State k s) input}
    (hsim : Sim s c c') :
    (tm.zeroTapeSim s).outputSymbol c' = tm.outputSymbol c := by
  rcases hq' : c'.state with _ | q'
  · have hc : c.state = none := by rw [hsim.state, hq']; rfl
    simp [outputSymbol, hq', hc]
  · have hc : c.state = some q'.state := by rw [hsim.state, hq']; rfl
    have hinputSymbol : c'.inputSymbol = c.inputSymbol := by
      simp [Cfg.inputSymbol, hsim.inputPos]
    simp only [outputSymbol, hq', hc, zeroTapeSim, hinputSymbol, sim_read hsim hq']

/-! ## Simulation of space-bounded computations -/

/-- A work-tape head of a computation that uses at most `s` cells of space up to step `t` stays
within the window `[-s, s]` up to step `t`. -/
lemma natAbs_workTapePos_le {t : ℕ} (hs : tm.spaceUsed (tm.initCfg input) t ≤ s) (i : Fin k) :
    ((tm.configs (tm.initCfg input) t).workTapePos i).natAbs ≤ s := by
  -- The heads start at `0`, so the displacement bound is a bound on the position itself.
  have h := tm.natAbs_le_spaceUsedByTape_of_mem_visited
    (tm.mem_visitedByTapeHead_self (tm.initCfg input) t i)
  simp only [initCfg, sub_zero] at h
  exact h.trans ((tm.spaceUsedByTape_le_spaceUsed _ t i).trans hs)

/-- Along a computation that uses at most `s` cells of work-tape space, the machine without work
tapes simulates the original machine step by step. -/
theorem sim_configs (tm : MultiTapeTM k Symbol State) (input : List Symbol)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) (t : ℕ) :
    Sim s (tm.configs (tm.initCfg input) t)
      ((tm.zeroTapeSim s).configs ((tm.zeroTapeSim s).initCfg input) t) := by
  induction t with
  | zero =>
    refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    · rintro q' hq' i
      simp only [configs_zero, initCfg, Option.mem_def, Option.some.injEq] at hq'
      subst hq'
      simp [zeroTapeSim, clampWindow, mem_window]
  | succ t ih =>
    have hpos : ∀ i, ((tm.step (tm.configs (tm.initCfg input) t)).workTapePos i).natAbs ≤ s := by
      intro i
      rw [← configs_succ_eq_step']
      exact natAbs_workTapePos_le (hs (t + 1)) i
    rw [configs_succ_eq_step', configs_succ_eq_step']
    exact sim_step ih hpos

/-- The machine without work tapes produces the same output as the simulated machine. -/
theorem sim_outputString (tm : MultiTapeTM k Symbol State) (input : List Symbol)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) (t : ℕ) :
    (tm.zeroTapeSim s).outputString ((tm.zeroTapeSim s).initCfg input) t
      = tm.outputString (tm.initCfg input) t := by
  induction t with
  | zero => simp [outputString]
  | succ t ih =>
    rw [outputString_succ, outputString_succ, ih, sim_outputSymbol (sim_configs tm input hs t)]

/-- The machine without work tapes halts in exactly the same step as the simulated machine. -/
theorem sim_state_isNone (tm : MultiTapeTM k Symbol State) (input : List Symbol)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) (t : ℕ) :
    ((tm.zeroTapeSim s).configs ((tm.zeroTapeSim s).initCfg input) t).state = none
      ↔ (tm.configs (tm.initCfg input) t).state = none := by
  rw [(sim_configs tm input hs t).state]
  simp

/-- The space used by a computation does not grow any more once the machine has halted. -/
lemma spaceUsed_le_of_halted {cfg : Cfg k Symbol State input} {T : ℕ}
    (h : (tm.configs cfg T).state = none) (t : ℕ) :
    tm.spaceUsed cfg t ≤ tm.spaceUsed cfg T := by
  rcases Nat.le_total t T with hle | hle
  · exact tm.spaceUsed_mono cfg hle
  -- After step `T` the configuration never changes, so no new cells are visited.
  refine Finset.sum_le_sum fun i _ => Finset.card_le_card fun z hz => ?_
  obtain ⟨t', ht', rfl⟩ := tm.mem_visitedByTapeHead.mp hz
  rcases Nat.le_total t' T with ht | ht
  · exact tm.mem_visitedByTapeHead.mpr ⟨t', by omega, rfl⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [tm.configs_add, tm.configs_of_halts _ h]
    exact tm.mem_visitedByTapeHead_self cfg T i

/-- **Constant space needs no work tapes**: if `tm` computes `output` from `input` in `t` steps and
never uses more than `s` cells of work-tape space, then the machine `tm.zeroTapeSim s` without work
tapes computes the same output in the same number of steps, using zero space. -/
theorem ComputesInTimeAndSpace.zeroTapeSim {output : List Symbol} {t s' : ℕ}
    (h : tm.ComputesInTimeAndSpace input output t s')
    (hs : ∀ t', tm.spaceUsed (tm.initCfg input) t' ≤ s) :
    (tm.zeroTapeSim s).ComputesInTimeAndSpace input output t 0 := by
  obtain ⟨hhalt, houtput, -⟩ := h
  exact ⟨(sim_state_isNone tm input hs t).mpr hhalt,
    (sim_outputString tm input hs t).trans houtput,
    spaceUsed_zero_tapes_eq_zero _ t rfl⟩

/-- If a machine computes a function within a constant space bound `c`, then the machine
`tm.zeroTapeSim c` without work tapes computes the same function within the same time bound, using
zero space. -/
theorem ComputesFunInTimeAndSpace.zeroTapeSim {IOSymbol : Type*}
    {f : List IOSymbol → List IOSymbol} {toMachineSymbol : IOSymbol ↪ Symbol} {t sf : ℕ → ℕ}
    {c : ℕ} (h : tm.ComputesFunInTimeAndSpace f toMachineSymbol t sf) (hc : ∀ n, sf n ≤ c) :
    (tm.zeroTapeSim c).ComputesFunInTimeAndSpace f toMachineSymbol t (fun _ => 0) := by
  intro input
  obtain ⟨t', ht', s', hs', hcomputes⟩ := h input
  -- The space bound at the halting step bounds the space usage at every step.
  have hbound : ∀ τ, tm.spaceUsed (tm.initCfg (input.map toMachineSymbol)) τ ≤ c := fun τ =>
    (spaceUsed_le_of_halted hcomputes.1 τ).trans
      (hcomputes.2.2 ▸ hs'.trans (hc input.length))
  exact ⟨t', ht', 0, Nat.zero_le _, hcomputes.zeroTapeSim hbound⟩

/-- **Constant space is the same as no work tapes**: a function is computed within a constant space
bound by some multi-tape machine if and only if it is computed by a machine without work tapes
(which necessarily uses zero space), with the same time bound. -/
theorem exists_zeroTape_computesFun_iff {Symbol IOSymbol : Type} [Finite Symbol]
    {f : List IOSymbol → List IOSymbol} {toMachineSymbol : IOSymbol ↪ Symbol} {t : ℕ → ℕ} :
    (∃ (State' : Type) (_ : Finite State') (tm' : MultiTapeTM 0 Symbol State'),
        tm'.ComputesFunInTimeAndSpace f toMachineSymbol t (fun _ => 0)) ↔
      (∃ (c k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Symbol State)
        (sf : ℕ → ℕ), (∀ n, sf n ≤ c) ∧ tm.ComputesFunInTimeAndSpace f toMachineSymbol t sf) := by
  constructor
  · rintro ⟨State', _, tm', h⟩
    exact ⟨0, 0, State', inferInstance, tm', fun _ => 0, fun _ => le_rfl, h⟩
  · rintro ⟨c, k, State, _, tm, sf, hc, h⟩
    have : Fintype Symbol := Fintype.ofFinite Symbol
    have : Fintype State := Fintype.ofFinite State
    exact ⟨ConstSpaceState Symbol State k c, inferInstance, tm.zeroTapeSim c, h.zeroTapeSim hc⟩

end Turing.MultiTapeTM
