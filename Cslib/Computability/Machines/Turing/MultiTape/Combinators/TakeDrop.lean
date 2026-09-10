/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of `take` and `drop`

Two single-purpose streaming machines with no work tapes:

* `dropMachine n` skips the first `n` input symbols and then copies the rest to the output tape;
* `takeMachine n` copies the first `n` input symbols to the output tape and then halts.

Both run in one step per input symbol and use no space. They are the tools that, together with
concatenation, let a one-bit tag be stripped from an encoding: `drop 1` recovers the argument after
a tag, `take 1` reads the tag.

The results are stated at the level of an *encoding change*: `id : α → α` is computable from an
encoding `encFrom` to an encoding `encTo` whenever `encTo a` is `(encFrom a).drop n` (respectively
`(encFrom a).take n`).

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_drop`: dropping a fixed prefix is computable.
* `Turing.MultiTapeTM.computableInTimeAndSpace_take`: taking a fixed prefix is computable.
-/

namespace Turing.MultiTapeTM

variable {α : Type*} {input : List Bool}

/-! ### Dropping a fixed prefix -/

/-- The drop machine: no work tapes, states `Fin (n + 1)` counting the symbols skipped so far. In a
state below `n` it skips the current symbol (move right, emit nothing); in the top state `n` it
copies the current symbol to the output and moves right; on the blank at the right end it halts. -/
def dropMachine (n : ℕ) : MultiTapeTM 0 Bool (Fin (n + 1)) where
  q₀ := ⟨0, by omega⟩
  tr q s _ :=
    match s with
    | some b =>
        if h : q.val < n then
          { inputTape := 1, workTapes := fun i => i.elim0, output := none,
            state := some ⟨q.val + 1, by omega⟩ }
        else
          { inputTape := 1, workTapes := fun i => i.elim0, output := some b, state := some q }
    | none => { inputTape := 0, workTapes := fun i => i.elim0, output := none, state := none }

namespace Drop

/-- A configuration of the drop machine: the state, the input head position and the output. -/
def cfg (n : ℕ) (input : List Bool) (q : Option (Fin (n + 1))) (p : Fin (input.length + 2))
    (out : List Bool) : Cfg 0 Bool (Fin (n + 1)) input :=
  ⟨q, p, fun _ _ => none, fun _ => 0, out⟩

variable {n : ℕ}

/-- A skip step: below the top state, over an input symbol, the machine moves right and advances the
counter without emitting. -/
lemma step_skip {i : ℕ} (hi : i < n) (hj : i < input.length) (out : List Bool) :
    (dropMachine n).step (cfg n input (some ⟨i, by omega⟩) ⟨i + 1, by omega⟩ out) =
      cfg n input (some ⟨i + 1, by omega⟩) ⟨i + 2, by omega⟩ out := by
  have hsym := inputSymbolInner (cfg := cfg n input (some ⟨i, by omega⟩) ⟨i + 1, by omega⟩ out)
    i (by simp only [cfg]; omega) hj
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  simp only [dropMachine, hi, ↓reduceDIte]
  refine Cfg.ext_zero_tapes rfl (Fin.ext ?_) (by simp [Action.apply])
  simp [Action.apply, moveInputPos]
  grind

/-- A copy step: in the top state, over an input symbol, the machine emits it and moves right. -/
lemma step_copy {j : ℕ} (hj : j < input.length) (out : List Bool) :
    (dropMachine n).step (cfg n input (some ⟨n, by omega⟩) ⟨j + 1, by omega⟩ out) =
      cfg n input (some ⟨n, by omega⟩) ⟨j + 2, by omega⟩ (out ++ (input[j]?).toList) := by
  have hsym := inputSymbolInner (cfg := cfg n input (some ⟨n, by omega⟩) ⟨j + 1, by omega⟩ out)
    j (by simp only [cfg]; omega) hj
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  simp only [dropMachine, lt_irrefl, ↓reduceDIte]
  refine Cfg.ext_zero_tapes rfl ?_ ?_
  · apply Fin.ext; simp [Action.apply, moveInputPos]; grind
  · simp [Action.apply, List.getElem?_eq_getElem hj]

/-- On the blank at the right end of the input, the machine halts in place, wherever the head is
parked at that boundary. -/
lemma step_halt {q : Fin (n + 1)} {p : Fin (input.length + 2)} (hp : p.val = input.length + 1)
    (out : List Bool) :
    (dropMachine n).step (cfg n input (some q) p out) = cfg n input none p out := by
  have hsym : (cfg n input (some q) p out).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr hp)
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  exact Cfg.ext_zero_tapes rfl (by simp [dropMachine, Action.apply]) (by simp [dropMachine,
    Action.apply])

/-- The skip phase: after `i ≤ min n input.length` steps the machine has skipped the first `i`
symbols and is over the `i`-th input cell in state `⟨i⟩`, with empty output. -/
lemma runFrom_skip (i : ℕ) (hin : i ≤ n) (hil : i ≤ input.length) :
    (dropMachine n).runFrom ((dropMachine n).initCfg input) i =
      cfg n input (some ⟨i, by omega⟩) ⟨i + 1, by omega⟩ [] := by
  induction i with
  | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
  | succ i ih =>
    rw [runFrom_succ_eq_step', ih (by omega) (by omega), step_skip (by omega) (by omega)]

/-- The copy phase: from the top state at input cell `n`, after `j` steps the machine has copied
`(input.drop n).take j`. -/
lemma runFrom_copy (j : ℕ) (hj : n + j ≤ input.length) :
    (dropMachine n).runFrom (cfg n input (some ⟨n, by omega⟩) ⟨n + 1, by omega⟩ []) j =
      cfg n input (some ⟨n, by omega⟩) ⟨n + j + 1, by omega⟩ ((input.drop n).take j) := by
  induction j with
  | zero => simp only [Nat.add_zero, List.take_zero]; rfl
  | succ j ih =>
    rw [runFrom_succ_eq_step', ih (by omega), step_copy (j := n + j) (by omega)]
    simp only [cfg]
    refine Cfg.ext_zero_tapes rfl rfl ?_
    rw [List.take_add_one, List.getElem?_drop]

/-- The full run halts, in `input.length + 1` steps, with `input.drop n` on the output tape. -/
lemma runFrom_full (n : ℕ) (input : List Bool) :
    (dropMachine n).runFrom ((dropMachine n).initCfg input) (input.length + 1) =
      cfg n input none ⟨input.length + 1, by omega⟩ (input.drop n) := by
  by_cases hle : n ≤ input.length
  · -- skip `n`, copy `length - n`, then one halt step
    have hcopy := runFrom_copy (input := input) (n := n) (input.length - n) (by omega)
    conv_lhs => rw [show input.length + 1 = n + ((input.length - n) + 1) from by omega]
    rw [runFrom_add, runFrom_skip n le_rfl hle, runFrom_add, hcopy, runFrom_succ_eq_step',
      runFrom_zero,
      step_halt (show (⟨n + (input.length - n) + 1, by omega⟩ : Fin (input.length + 2)).val =
        input.length + 1 from by simp; omega)]
    simp only [cfg]
    refine Cfg.ext_zero_tapes rfl (Fin.ext ?_) ?_
    · change n + (input.length - n) + 1 = input.length + 1
      omega
    · change (input.drop n).take (input.length - n) = input.drop n
      rw [show input.length - n = (input.drop n).length from by rw [List.length_drop],
        List.take_length]
  · -- the input is exhausted during the skip phase and the machine halts blank
    rw [runFrom_succ_eq_step', runFrom_skip input.length (by omega) le_rfl, step_halt rfl]
    simp only [cfg]
    refine Cfg.ext_zero_tapes rfl rfl ?_
    rw [List.drop_eq_nil_of_le (by omega)]

/-- **The drop machine outputs `input.drop n`**, in `input.length + 1` steps and no space. -/
theorem computesInTimeAndSpace (n : ℕ) (input : List Bool) :
    ComputesInTimeAndSpace (dropMachine n) input (input.drop n) (input.length + 1) 0 :=
  ⟨by rw [runFrom_full]; rfl, by rw [runFrom_full]; rfl,
    (dropMachine n).spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

end Drop

/-- **Dropping a fixed prefix is computable.** If `encTo a` is `(encFrom a).drop n` for every `a`,
then the identity is computable from `encFrom` to `encTo`, in one step per input symbol and no
space. -/
public theorem computableInTimeAndSpace_drop {encFrom encTo : α ↪ List Bool} (n : ℕ)
    (h : ∀ a, encTo a = (encFrom a).drop n) :
    ComputableInTimeAndSpace (id : α → α) encFrom encTo
      (fun a => (encFrom a).length + 1) (fun _ => 0) :=
  ⟨0, Fin (n + 1), inferInstance, dropMachine n, fun a =>
    ⟨(encFrom a).length + 1, le_rfl, 0, le_rfl, by
      rw [show encTo (id a) = (encFrom a).drop n from h a]
      exact Drop.computesInTimeAndSpace n (encFrom a)⟩⟩

/-! ### Taking a fixed prefix -/

/-- The take machine: no work tapes, states `Fin (n + 1)` counting the symbols copied so far. Below
the top state `n`, over an input symbol, it copies it to the output and moves right; on reaching the
top state, or the blank at the right end, it halts. -/
def takeMachine (n : ℕ) : MultiTapeTM 0 Bool (Fin (n + 1)) where
  q₀ := ⟨0, by omega⟩
  tr q s _ :=
    match s with
    | some b =>
        if h : q.val < n then
          { inputTape := 1, workTapes := fun i => i.elim0, output := some b,
            state := some ⟨q.val + 1, by omega⟩ }
        else
          { inputTape := 0, workTapes := fun i => i.elim0, output := none, state := none }
    | none => { inputTape := 0, workTapes := fun i => i.elim0, output := none, state := none }

namespace Take

/-- A configuration of the take machine. -/
def cfg (n : ℕ) (input : List Bool) (q : Option (Fin (n + 1))) (p : Fin (input.length + 2))
    (out : List Bool) : Cfg 0 Bool (Fin (n + 1)) input :=
  ⟨q, p, fun _ _ => none, fun _ => 0, out⟩

variable {n : ℕ}

/-- A copy step: below the top state, over an input symbol, emit it and move right. -/
lemma step_copy {i : ℕ} (hi : i < n) (hj : i < input.length) (out : List Bool) :
    (takeMachine n).step (cfg n input (some ⟨i, by omega⟩) ⟨i + 1, by omega⟩ out) =
      cfg n input (some ⟨i + 1, by omega⟩) ⟨i + 2, by omega⟩ (out ++ (input[i]?).toList) := by
  have hsym := inputSymbolInner (cfg := cfg n input (some ⟨i, by omega⟩) ⟨i + 1, by omega⟩ out)
    i (by simp only [cfg]; omega) hj
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  simp only [takeMachine, hi, ↓reduceDIte]
  refine Cfg.ext_zero_tapes rfl (Fin.ext ?_) ?_
  · simp [Action.apply, moveInputPos]; grind
  · simp [Action.apply, List.getElem?_eq_getElem hj]

/-- In the top state the machine halts in place, whatever it reads. -/
lemma step_halt_top {p : Fin (input.length + 2)} (out : List Bool) :
    (takeMachine n).step (cfg n input (some ⟨n, by omega⟩) p out) = cfg n input none p out := by
  unfold step
  simp only [cfg]
  cases hsym : (⟨some (⟨n, by omega⟩ : Fin (n + 1)), p, fun _ _ => none, fun _ => 0, out⟩ :
      Cfg 0 Bool (Fin (n + 1)) input).inputSymbol with
  | none =>
    simp only [takeMachine]
    exact Cfg.ext_zero_tapes rfl (by simp [Action.apply, moveInputPos_zero])
      (by simp [Action.apply])
  | some b =>
    simp only [takeMachine, lt_irrefl, ↓reduceDIte]
    exact Cfg.ext_zero_tapes rfl (by simp [Action.apply, moveInputPos_zero])
      (by simp [Action.apply])

/-- On the blank at the right end the machine halts. -/
lemma step_halt_blank {q : Fin (n + 1)} {p : Fin (input.length + 2)} (hp : p.val = input.length + 1)
    (out : List Bool) :
    (takeMachine n).step (cfg n input (some q) p out) = cfg n input none p out := by
  have hsym : (cfg n input (some q) p out).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr hp)
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  exact Cfg.ext_zero_tapes rfl (by simp [takeMachine, Action.apply]) (by simp [takeMachine,
    Action.apply])

/-- The copy phase: after `i ≤ min n input.length` steps the machine has copied the first `i`
symbols and sits over cell `i` in state `⟨i⟩`. -/
lemma runFrom_copy (i : ℕ) (hin : i ≤ n) (hil : i ≤ input.length) :
    (takeMachine n).runFrom ((takeMachine n).initCfg input) i =
      cfg n input (some ⟨i, by omega⟩) ⟨i + 1, by omega⟩ (input.take i) := by
  induction i with
  | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
  | succ i ih =>
    rw [runFrom_succ_eq_step', ih (by omega) (by omega), step_copy (by omega) (by omega)]
    simp only [cfg]
    refine Cfg.ext_zero_tapes rfl rfl ?_
    change input.take i ++ (input[i]?).toList = input.take (i + 1)
    rw [List.take_add_one]

/-- The full run halts, in `input.length + 1` steps, with `input.take n` on the output tape (the
input head is parked wherever the machine stopped, so the position is left existential). -/
lemma runFrom_full (n : ℕ) (input : List Bool) :
    ∃ p, (takeMachine n).runFrom ((takeMachine n).initCfg input) (input.length + 1) =
      cfg n input none p (input.take n) := by
  by_cases hle : n ≤ input.length
  · -- copy `n` symbols, then halt in the top state (position `n + 1`)
    refine ⟨⟨n + 1, by omega⟩, ?_⟩
    conv_lhs => rw [show input.length + 1 = n + 1 + (input.length - n) from by omega]
    rw [runFrom_add, runFrom_add, runFrom_copy n le_rfl hle, runFrom_succ_eq_step',
      runFrom_zero, step_halt_top, runFrom_of_halt _ (by simp [cfg])]
  · -- the input is exhausted first, and the machine halts blank (position `length + 1`)
    refine ⟨⟨input.length + 1, by omega⟩, ?_⟩
    rw [runFrom_succ_eq_step', runFrom_copy input.length (by omega) le_rfl, step_halt_blank rfl]
    simp only [cfg]
    refine Cfg.ext_zero_tapes rfl rfl ?_
    change input.take input.length = input.take n
    rw [List.take_length, List.take_of_length_le (by omega)]

/-- **The take machine outputs `input.take n`**, in `input.length + 1` steps and no space. -/
theorem computesInTimeAndSpace (n : ℕ) (input : List Bool) :
    ComputesInTimeAndSpace (takeMachine n) input (input.take n) (input.length + 1) 0 := by
  obtain ⟨p, hp⟩ := runFrom_full n input
  exact ⟨by rw [hp]; rfl, by rw [hp]; rfl, (takeMachine n).spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

end Take

/-- **Taking a fixed prefix is computable.** If `encTo a` is `(encFrom a).take n` for every `a`,
then the identity is computable from `encFrom` to `encTo`, in one step per input symbol and no
space. -/
public theorem computableInTimeAndSpace_take {encFrom encTo : α ↪ List Bool} (n : ℕ)
    (h : ∀ a, encTo a = (encFrom a).take n) :
    ComputableInTimeAndSpace (id : α → α) encFrom encTo
      (fun a => (encFrom a).length + 1) (fun _ => 0) :=
  ⟨0, Fin (n + 1), inferInstance, takeMachine n, fun a =>
    ⟨(encFrom a).length + 1, le_rfl, 0, le_rfl, by
      rw [show encTo (id a) = (encFrom a).take n from h a]
      exact Take.computesInTimeAndSpace n (encFrom a)⟩⟩

end Turing.MultiTapeTM
