/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.Prog
public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi


/-! # RoseTreeMachine V4 — simulation theorems (statements only)

This file collects the cross-model simulation statements relating the functional language
`Prog`, its first-order fragment `InPlace`, and multi-tape Turing machines. All statements are
currently `sorry`-ed; they record the intended theorems and their resource overheads.

Each statement is phrased with the `…ComputableInTimeAndSpace` predicates, so the only remaining
quantifier is the existentially quantified constant `a` carrying the (constant-factor or
provisional polynomial) overhead.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

open Classical in
/-- The indicator function of a language. -/
noncomputable def indicator (L : Language Bool) : List Bool → List Bool
  | x => if x ∈ L then [true] else [false]


/-- A boolean function is computable by some multi-tape Turing machine within the given time and
space bounds. -/
def TMComputableInTimeAndSpace (f : List Bool → List Bool) (t s : ℕ → ℕ) : Prop :=
  ∃ (k : ℕ) (tm : MultiTapeTM k Bool), tm.ComputesFunInTimeAndSpace f t s

/-- A boolean function is computable by some `Prog` within the given time and space bounds. -/
def ProgComputableInTimeAndSpace (f : List Bool → List Bool) (t s : ℕ → ℕ) : Prop :=
  ∃ (p : Prog), p.ComputesBoolFunInTimeAndSpace f t s

/-- A boolean function is computable by some *in-place* `Prog` within the given time and space
bounds. -/
def InPlaceProgComputableInTimeAndSpace (f : List Bool → List Bool) (t s : ℕ → ℕ) : Prop :=
  ∃ (p : Prog), InPlace p ∧ p.ComputesBoolFunInTimeAndSpace f t s

/-- **In-place `Prog` → Turing machine.** An in-place program is implemented by a multi-tape
Turing machine with only constant-factor time and space overhead.

The linear *space* bound `a * s` reflects a constant-factor tape encoding of the rose-tree data.
The linear *time* bound `a * t` is the strong part of the statement: the `Prog` cost model
charges nothing for environment manipulation (variable access is charged by value size, binding
`σ ++ [v]` is free), so achieving a *linear* — rather than e.g. `a * (t * s)` — time overhead
relies on the tape encoding supporting O(1)-amortized variable addressing and environment
extension. -/
lemma inPlace_prog_to_tm
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : InPlaceProgComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ), TMComputableInTimeAndSpace f (fun n => a * t n) (fun n => a * s n) := by
  sorry

/-- **`Prog` → in-place `Prog`.** Every program is simulated by an in-place program computing the
same function (defunctionalisation: the explicit-stack machine of `StackSim` realised as a single
`while_` loop).

Provisional overhead: making environment threading explicit multiplies time by (at most) the
space, hence `a * (t * s)`; the space bound `a * s` assumes a shared-environment encoding that
avoids duplicating the environment into every stack frame. -/
lemma prog_to_inPlace
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : ProgComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ),
      InPlaceProgComputableInTimeAndSpace f (fun n => a * (t n * s n)) (fun n => a * s n) := by
  sorry

/-- **`Prog` → Turing machine.** Corollary of `prog_to_inPlace` followed by `inPlace_prog_to_tm`:
every program is implemented by a multi-tape Turing machine. The overhead is inherited from the
`Prog → InPlace` step. -/
lemma prog_to_tm
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : ProgComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ), TMComputableInTimeAndSpace f (fun n => a * (t n * s n)) (fun n => a * s n) := by
  sorry

/-- **Turing machine → in-place `Prog`.** The reverse direction (the universal-machine
construction of `UniversalTM`): every multi-tape Turing machine is simulated by an in-place
program.

Provisional overhead: each Turing-machine step is realised by scanning the encoded tape
configuration, costing time proportional to the space, hence `a * (t * s)`; space stays within a
constant factor, `a * s`. -/
lemma tm_to_inPlace_prog
    (f : List Bool → List Bool) (t s : ℕ → ℕ)
    (h_comp : TMComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ),
      InPlaceProgComputableInTimeAndSpace f (fun n => a * (t n * s n)) (fun n => a * s n) := by
  sorry

/-! ## Encoding multi-tape Turing machines and their configurations into `Data`

To phrase a *single, universal* simulator program we have to feed both the machine and its
configuration to the `Prog` as `Data`. The following `DataEncode` instances reify every component
of a multi-tape Turing machine — directions, tapes, transition outputs, configurations — and the
machine itself (its transition function reified as a finite lookup table). -/

/-- A `Fin n`-indexed tuple is encoded through its `List.ofFn` representation. -/
instance {n : ℕ} {α : Type} [DataEncode α] : DataEncode (Fin n → α) where
  encode f := DataEncode.encode (List.ofFn f)
  h_inj := by
    intro f g h
    have : List.ofFn f = List.ofFn g := DataEncode.h_inj h
    exact List.ofFn_inj.mp this

/-- Encoding of a direction, reusing the `Bool` encoding. -/
instance : DataEncode Dir where
  encode := fun
    | Dir.left => DataEncode.encode true
    | Dir.right => DataEncode.encode false
  h_inj := by intro a b h; cases a <;> cases b <;> simp_all [DataEncode.encode]

/-- A stack tape is encoded through its underlying list. -/
instance {Symbol : Type} [DataEncode Symbol] : DataEncode (Turing.StackTape Symbol) where
  encode t := DataEncode.encode t.toList
  h_inj := by intro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h; grind [DataEncode.h_inj h]

/-- A bidirectional tape is encoded by its head symbol and its two stacks. -/
instance {Symbol : Type} [DataEncode Symbol] : DataEncode (Turing.BiTape Symbol) where
  encode t := DataEncode.encode (t.head, t.left, t.right)
  h_inj := by intro ⟨h₁, l₁, r₁⟩ ⟨h₂, l₂, r₂⟩ h; grind [DataEncode.h_inj h]

/-- A transition output is encoded by tupling its four fields. -/
instance {k : ℕ} {State : Type} [DataEncode State] :
    DataEncode (TransitionOut k Bool State) where
  encode o := DataEncode.encode (o.inputMove, o.stmts, o.outS, o.q')
  h_inj := by
    intro ⟨i₁, s₁, o₁, q₁⟩ ⟨i₂, s₂, o₂, q₂⟩ h
    have heq := DataEncode.h_inj h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha, hb, hc, hd⟩ := heq
    subst ha; subst hb; subst hc; subst hd; rfl

/-- A configuration is encoded by tupling its fields; the input head position is encoded by its
underlying natural number (the input list, also part of the tuple, recovers its `Fin` type). -/
instance {k : ℕ} {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DataEncode Symbol]
    (tm : MultiTapeTM k Symbol) [DataEncode tm.State] : DataEncode tm.Cfg where
  encode cfg :=
    DataEncode.encode (cfg.state, cfg.input, (cfg.inputPos.val : ℕ), cfg.workTapes, cfg.output)
  h_inj := by
    intro ⟨s₁, inp₁, pos₁, w₁, out₁⟩ ⟨s₂, inp₂, pos₂, w₂, out₂⟩ h
    have heq := DataEncode.h_inj h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hs, hinp, hpos, hw, hout⟩ := heq
    subst hs; subst hinp; subst hw; subst hout
    have : pos₁ = pos₂ := Fin.ext hpos
    subst this; rfl

/-- Encode a multi-tape Turing machine over `Bool` as `Data`: its initial state together with its
transition function reified as a finite lookup table over the (finite) domain of state, input
symbol and tuple of work-tape head symbols. -/
noncomputable def encodeMachine {k : ℕ} (tm : MultiTapeTM k Bool) [DataEncode tm.State] : Data :=
  letI : Fintype tm.State := tm.stateFintype
  letI : Fintype (tm.State × Option Bool × (Fin k → Option Bool)) := inferInstance
  DataEncode.encode
    (tm.q₀,
      (Finset.univ : Finset (tm.State × Option Bool × (Fin k → Option Bool))).toList.map
        (fun d => (d, tm.tr d.1 d.2.1 d.2.2)))

/-- **Universal step simulator.** There is a single `Prog` that, given the encoding of *any*
multi-tape Turing machine over `Bool`, an input word and a step count `t`, outputs the encoding of
the machine's configuration after exactly `t` steps (`none` once the machine has halted) together
with the amount of space it has used up to that step. -/
theorem exists_universal_step_simulator :
    ∃ (sim : Prog),
      ∀ {k : ℕ} (tm : MultiTapeTM k Bool) [DataEncode tm.State]
        (input : List Bool) (t : ℕ),
        ∃ (time space : ℕ),
          sim.ComputesInTimeAndSpace
            (Data.l [encodeMachine tm, DataEncode.encode input, DataEncode.encode t])
            (DataEncode.encode
              (tm.configs (tm.initCfg input) t, tm.spaceUsed (tm.initCfg input) t))
            time space := by
  sorry

/-- **State-set normalisation.** Every multi-tape Turing machine is equivalent to one whose state
set is a canonical `Fin s`: there is a machine using `Fin s` as its state set that computes the
same functions within exactly the same time and space bounds. (Take `s` to be the cardinality of
the original state set and transport the transition function along the resulting equivalence.) -/
theorem exists_fin_state_tm {k : ℕ} {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (tm : MultiTapeTM k Symbol) :
    ∃ (s : ℕ) (tm' : MultiTapeTM k Symbol), tm'.State = Fin s ∧
      ∀ (f : List Symbol → List Symbol) (t sp : ℕ → ℕ),
        tm.ComputesFunInTimeAndSpace f t sp ↔ tm'.ComputesFunInTimeAndSpace f t sp := by
  sorry


def SpaceConstructible (s : ℕ → ℕ) : Prop :=
  ∃ t a, TMComputableInTimeAndSpace (fun x => List.replicate x.length true) t (fun n => a * (s n))

def LittleO (f g : ℕ → ℕ) : Prop :=
  ∀ c > 0, ∃ N, ∀ n ≥ N, c * f n < g n

def DSpace (s : ℕ → ℕ) : Set (Language Bool) :=
    { L | ∃ t, TMComputableInTimeAndSpace (indicator L) t s}

/-! ### Abstracting away the encoding: enumerations and a budgeted evaluator

For the diagonalization it is cleaner to forget the concrete machine encoding and work with an
abstract *enumeration* of string functions indexed by bit strings, together with a single
budgeted *evaluator* that simulates the index on its input within an `s`-bounded budget. Both are
realised by the concrete `encodeMachine` / `exists_bounded_simulator` machinery above, but the
hierarchy theorem only needs the two abstract facts below. -/

/-- An enumeration of string functions indexed by bit strings: `enum i` is the (total) function
computed by the machine encoded by `i`, taking the fixed value `[]` on inputs where that machine
diverges. -/
abbrev Enumeration := List Bool → List Bool → List Bool

/-- An enumeration is *complete with infinite repetition* if every Turing-computable string
function appears as `enum i` for indices `i` of unbounded length (equivalently, infinitely often).
Padding the machine encoding provides the arbitrarily long indices. -/
def CompleteWithInfiniteIndices (enum : Enumeration) : Prop :=
  ∀ (f : List Bool → List Bool) (t s : ℕ → ℕ),
    TMComputableInTimeAndSpace f t s →
    ∀ N, ∃ i, N ≤ i.length ∧ enum i = f

/-- **Effective enumeration.** There is an enumeration of string functions in which every
Turing-computable function appears at arbitrarily long indices. -/
theorem exists_complete_enumeration :
    ∃ (enum : Enumeration), CompleteWithInfiniteIndices enum := by
  sorry

/-- **Budgeted universal evaluator.** For a space-constructible `s` and any enumeration `enum`,
there is an evaluator `eval` such that

* its diagonal `i ↦ eval i i` is computable in space `s` (constant factors absorbed by tape
  compression, so flipping it stays in `DSpace s`), and
* `eval i x = enum i x` whenever the machine `i` runs on `x` within the `2 ^ s(|i|)` time and
  `s(|i|)` space budget — i.e. whenever the enumerated function's own bounds fit the budget at that
  input (otherwise `eval` may fall back to a fixed value).

This is the abstract repackaging of `exists_bounded_simulator`. -/
theorem exists_bounded_evaluator (s : ℕ → ℕ) (hs : SpaceConstructible s) (enum : Enumeration) :
    ∃ (eval : Enumeration) (t : ℕ → ℕ),
      TMComputableInTimeAndSpace (fun i => eval i i) t s ∧
      ∀ (i x : List Bool) (t' s' : ℕ → ℕ),
        TMComputableInTimeAndSpace (enum i) t' s' →
        t' x.length ≤ 2 ^ s i.length → s' x.length ≤ s i.length →
        eval i x = enum i x := by
  sorry

open Classical in
/-- The intended output of the bounded simulator on machine `tm`, input `input` and threshold `σ`:
the machine's output if it halts within `2 ^ σ` steps while staying within `σ` space, and the
fixed datum `Data.l []` otherwise. -/
noncomputable def boundedSimResult {k : ℕ} (tm : MultiTapeTM k Bool) (input : List Bool)
    (σ : ℕ) : Data :=
  if h : ∃ (output : List Bool) (τ s' : ℕ),
      τ ≤ 2 ^ σ ∧ s' ≤ σ ∧ tm.ComputesInTimeAndSpace input output τ s' then
    DataEncode.encode h.choose
  else
    Data.l []

/-- **Bounded universal simulator.** If `s` is space-constructible then there is a single `Prog`
that, on input `(x, y)` with `x` the encoding of any multi-tape Turing machine over `Bool` and `y`
an input word, simulates the machine for at most `2 ^ s(|x|)` steps while tracking its space: if
the machine exceeds `s(|x|)` space or fails to halt within the step budget it returns the fixed
output `Data.l []`, otherwise it returns the machine's result. The simulator itself runs in space
`O(s(|x|))`.

This is provable from `exists_universal_step_simulator` together with space-constructibility of
`s` (used to materialise the `s(|x|)` thresholds) and the configuration-counting bound
`steps ≤ 2 ^ O(space)`. -/
theorem exists_bounded_simulator (s : ℕ → ℕ) (hs : SpaceConstructible s) :
    ∃ (bounded : Prog) (a : ℕ),
      ∀ {k : ℕ} (tm : MultiTapeTM k Bool) [DataEncode tm.State] (input : List Bool),
        ∃ (t' s' : ℕ),
          s' ≤ a * s (encodeMachine tm).size + a ∧
          bounded.ComputesInTimeAndSpace
            (Data.l [encodeMachine tm, DataEncode.encode input])
            (boundedSimResult tm input (s (encodeMachine tm).size))
            t' s' := by
  sorry

/-- **Post-processing a decision.** Flipping the `[true]`/`[false]` decision read off a space-`s`
computation stays in space `s` (the flip inspects only whether the output is `[true]`, costing
`O(1)` extra space, absorbed by tape compression). -/
lemma flip_decision_in_space {g : List Bool → List Bool} {t s : ℕ → ℕ}
    (hg : TMComputableInTimeAndSpace g t s) :
    ∃ t', TMComputableInTimeAndSpace
      (fun x => if g x = [true] then [false] else [true]) t' s := by
  sorry

/-- **Configuration counting.** A computation that always halts within space `s` also halts within
`2 ^ (a * s + a)` steps for some constant `a`: a halting machine cannot repeat a configuration, and
there are at most `2 ^ O(space)` configurations. -/
lemma time_le_exp_space {f : List Bool → List Bool} {t s : ℕ → ℕ}
    (h : TMComputableInTimeAndSpace f t s) :
    ∃ (a : ℕ), TMComputableInTimeAndSpace f (fun n => 2 ^ (a * s n + a)) s := by
  sorry

theorem space_hierarchy
   (s₁ : ℕ → ℕ)
   (h_s₁ : SpaceConstructible s₁)
   (h_ge : ∀ n, s₁ n ≥ n) -- TODO our restriction restriction, usually log
   (s₂ : ℕ → ℕ)
   (h_s₂ : SpaceConstructible s₂)
   (h_lo : LittleO s₂ s₁) :
   ∃ L, L ∈ (DSpace s₁) ∧ L ∉ DSpace s₂ := by
  -- An enumeration in which every TM-computable function occurs at arbitrarily long indices, and a
  -- budgeted evaluator whose diagonal lives in `DSpace s₁`.
  obtain ⟨enum, h_complete⟩ := exists_complete_enumeration
  obtain ⟨eval, t_diag, h_diag_space, h_faithful⟩ := exists_bounded_evaluator s₁ h_s₁ enum
  -- The diagonalizer flips the simulated self-application, and its language `L_D`.
  set D : List Bool → List Bool := fun x => if eval x x = [true] then [false] else [true]
    with hD_def
  set L_D : Language Bool := {x | eval x x ≠ [true]} with hL_def
  have h_ind : indicator L_D = D := by
    funext x
    simp only [indicator, hD_def, hL_def, Set.mem_setOf_eq]
    by_cases hx : eval x x = [true] <;> simp [hx]
  refine ⟨L_D, ?_, ?_⟩
  · -- `L_D ∈ DSpace s₁`: the flipped diagonal is computable in space `s₁`.
    obtain ⟨t', ht'⟩ := flip_decision_in_space h_diag_space
    exact ⟨t', by rw [h_ind, hD_def]; exact ht'⟩
  · -- `L_D ∉ DSpace s₂`: otherwise diagonalization contradicts itself.
    rintro ⟨t₂, h₂⟩
    rw [h_ind] at h₂
    -- Replace the given time bound by the exponential-in-space one (config counting).
    obtain ⟨a, hexp⟩ := time_le_exp_space h₂
    -- `s₂ = o(s₁)` with slack `a + 1` provides the budget, for inputs at least `N` long.
    obtain ⟨N, hN⟩ := h_lo (a + 1) (Nat.succ_pos a)
    -- A long enough index `i` with `enum i = D`.
    obtain ⟨i, hi_len, hi_enum⟩ :=
      h_complete D (fun n => 2 ^ (a * s₂ n + a)) s₂ hexp (max N (a * a + a))
    have hmN : N ≤ i.length := le_trans (le_max_left _ _) hi_len
    have hmaa : a * a + a ≤ i.length := le_trans (le_max_right _ _) hi_len
    have hstrict : (a + 1) * s₂ i.length < s₁ i.length := hN i.length hmN
    have e : (a + 1) * s₂ i.length = s₂ i.length + a * s₂ i.length := by ring
    -- The space budget fits.
    have hspace : s₂ i.length ≤ s₁ i.length := by omega
    -- The time budget fits.
    have htime_exp : a * s₂ i.length + a ≤ s₁ i.length := by
      rcases le_or_lt a (s₂ i.length) with hle | hlt
      · omega
      · have hmul : a * s₂ i.length ≤ a * a := Nat.mul_le_mul (le_refl a) (le_of_lt hlt)
        have hge : i.length ≤ s₁ i.length := h_ge i.length
        omega
    have htime : (2 : ℕ) ^ (a * s₂ i.length + a) ≤ 2 ^ s₁ i.length :=
      Nat.pow_le_pow_right (by norm_num) htime_exp
    -- Faithfulness: the evaluator reproduces `enum i i = D i`.
    have hfaith : eval i i = enum i i :=
      h_faithful i i (fun n => 2 ^ (a * s₂ n + a)) s₂ (by rw [hi_enum]; exact hexp) htime hspace
    rw [hi_enum] at hfaith
    -- `D i = if eval i i = [true] then [false] else [true]`, but `eval i i = D i`: contradiction.
    have hDi : D i = if eval i i = [true] then [false] else [true] := by simp only [hD_def]
    rw [hfaith] at hDi
    by_cases hc : D i = [true]
    · rw [if_pos hc, hc] at hDi; exact absurd hDi (by decide)
    · rw [if_neg hc] at hDi; exact hc hDi
end V4

end RoseTreeMachine

end Turing
