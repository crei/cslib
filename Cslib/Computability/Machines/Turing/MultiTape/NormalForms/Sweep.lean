/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Sweeping a footprinted tape pair clean

The machine of this file erases one work tape whose garbage may contain embedded blanks — so no
scan of the tape itself can find its extent — guided by the *footprint* tape produced by
`Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Instrument`: a contiguous block of
marks over the visited interval, with a distinguished anchor at cell `0`.

The protocol erases outside-in towards the anchor and consumes it last, which is what lets both
heads end at cell `0` with everything blank, without any counting:

1. `goRight`: walk right over the marks to the right end of the footprint;
2. `toAnchor`: sweep left, erasing garbage and marks, until the anchor — which is kept, while the
   garbage under it is erased;
3. `sweepLeft`: continue sweeping left over the remaining marks to the left end;
4. `seek`: walk right over the now-blank cells; the first nonblank cell is the anchor, i.e.
   cell `0`: erase it and halt.

Both heads move in lockstep throughout, so they home together, and the excursion never leaves the
footprint interval widened by one cell on each side — which is what bounds the sweep's space by
the instrumented run's own.
-/

namespace Turing.MultiTapeTM

namespace Sweep

/-- The four phases of the sweep. -/
private inductive SweepState | goRight | toAnchor | sweepLeft | seek
deriving DecidableEq

private instance : Finite SweepState :=
  Finite.of_injective
    (fun s => match s with
      | .goRight => (0 : Fin 4) | .toAnchor => 1 | .sweepLeft => 2 | .seek => 3)
    (fun a b h => by cases a <;> cases b <;> simp_all)

variable {K : ℕ} (i fp : Fin K)

/-- An action of the sweep: optional writes on the pair, the same move for both heads, everything
else untouched. -/
private def act (wi wf : Option (Option Bool)) (m : SignType) (q : Option SweepState) :
    Action K Bool SweepState where
  inputTape := 0
  workTapes l := if l = i then (wi, m) else if l = fp then (wf, m) else (none, 0)
  output := none
  state := q

/-- The sweep machine. It reads only the footprint tape. -/
private def sweep : MultiTapeTM K Bool SweepState where
  q₀ := .goRight
  tr q _ work :=
    match q, work fp with
    | .goRight, some _ => act i fp none none 1 (some .goRight)
    | .goRight, none => act i fp none none (-1) (some .toAnchor)
    | .toAnchor, some false => act i fp (some none) (some none) (-1) (some .toAnchor)
    | .toAnchor, some true => act i fp (some none) none (-1) (some .sweepLeft)
    | .toAnchor, none => act i fp none none 0 none
    | .sweepLeft, some _ => act i fp (some none) (some none) (-1) (some .sweepLeft)
    | .sweepLeft, none => act i fp none none 1 (some .seek)
    | .seek, none => act i fp none none 1 (some .seek)
    | .seek, some _ => act i fp none (some none) 0 none

variable {input : List Bool}

/-- The configurations the sweep passes through: both heads at `p`, the pair holding `Ti` and
`Tf`, everything else frozen from `base`. -/
private def cfg (base : Cfg K Bool SweepState input) (q : Option SweepState) (p : ℤ)
    (Ti Tf : ℤ → Option Bool) : Cfg K Bool SweepState input :=
  ⟨q, base.inputPos,
    Function.update (Function.update base.workTapes i Ti) fp Tf,
    Function.update (Function.update base.workTapePos i p) fp p,
    base.output⟩

variable {i fp} (hifp : i ≠ fp)

private lemma cfg_workTapes_fp (base : Cfg K Bool SweepState input) (q p Ti Tf) :
    (cfg i fp base q p Ti Tf).workTapes fp = Tf := by
  simp [cfg]

private lemma cfg_workTapePos_fp (base : Cfg K Bool SweepState input) (q p Ti Tf) :
    (cfg i fp base q p Ti Tf).workTapePos fp = p := by
  simp [cfg]

/-- The effect of an optional write at position `p`. -/
private def applyWrite (T : ℤ → Option Bool) (p : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => T
  | some s => Function.update T p s

@[simp] private lemma applyWrite_none (T : ℤ → Option Bool) (p : ℤ) :
    applyWrite T p none = T := rfl

@[simp] private lemma applyWrite_some (T : ℤ → Option Bool) (p : ℤ) (s : Option Bool) :
    applyWrite T p (some s) = Function.update T p s := rfl

include hifp in
/-- One step of the sweep from a sweep configuration, given what the transition does. -/
private lemma step_cfg (base : Cfg K Bool SweepState input) (q : SweepState) (p : ℤ)
    (Ti Tf : ℤ → Option Bool) (wi wf : Option (Option Bool)) (m : SignType)
    (q' : Option SweepState)
    (htr : ∀ inp work, work fp = Tf p →
      (sweep i fp).tr q inp work = act i fp wi wf m q') :
    (sweep i fp).step (cfg i fp base (some q) p Ti Tf) =
      cfg i fp base q' (p + m) (applyWrite Ti p wi) (applyWrite Tf p wf) := by
  have hq : (cfg i fp base (some q) p Ti Tf).state = some q := rfl
  have hwork : (cfg i fp base (some q) p Ti Tf).workTapeSymbols fp = Tf p := by
    simp [Cfg.workTapeSymbols, cfg_workTapes_fp, cfg_workTapePos_fp]
  simp only [step, hq]
  rw [htr _ _ hwork]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [Action.apply, act, cfg]
  · funext l z
    by_cases hl : l = fp
    · subst hl
      rcases wf with _ | s <;>
        simp [Action.apply, act, cfg, Ne.symm hifp, applyWrite]
    · by_cases hli : l = i
      · subst hli
        rcases wi with _ | s <;>
          simp [Action.apply, act, cfg, hifp, applyWrite]
      · simp [Action.apply, act, cfg, hl, hli]
  · funext l
    by_cases hl : l = fp
    · subst hl
      simp [Action.apply, act, cfg, Ne.symm hifp]
    · by_cases hli : l = i
      · subst hli
        simp [Action.apply, act, cfg, hifp]
      · simp [Action.apply, act, cfg, hl, hli]
  · simp [Action.apply, act, cfg]

section Run

variable (l r : ℤ)

/-- The footprint over the interval `[l, r]`: the anchor at `0`, marks elsewhere. -/
private def F : ℤ → Option Bool := fun z =>
  if z = 0 then some true else if l ≤ z ∧ z ≤ r then some false else none

/-- A tape erased strictly above `q`. -/
private def eraseAbove (T : ℤ → Option Bool) (q : ℤ) : ℤ → Option Bool := fun z =>
  if q < z then none else T z

/-- The footprint after the left sweep has reached position `q`: everything at `q + 1` and above
erased except the anchor. -/
private def eraseKeepAnchor (T : ℤ → Option Bool) (q : ℤ) : ℤ → Option Bool := fun z =>
  if q < z ∧ z ≠ 0 then none else T z

variable (base : Cfg K Bool SweepState input) (G : ℤ → Option Bool)

private lemma cast_one : ((1 : SignType) : ℤ) = 1 := rfl
private lemma cast_neg_one : ((-1 : SignType) : ℤ) = -1 := rfl
private lemma cast_zero : ((0 : SignType) : ℤ) = 0 := rfl

include hifp in
/-- Phase 1: walk right over the marks. -/
private lemma run_goRight (p : ℤ) (hlp : l ≤ p) (d : ℕ) (hd : p + d ≤ r + 1) :
    (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r)) d =
      cfg i fp base (some .goRight) (p + d) G (F l r) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [runFrom_succ_eq_step', ih (by omega)]
    have hbound : l ≤ p + (d : ℤ) ∧ p + (d : ℤ) ≤ r := by omega
    have hread : F l r (p + d) ≠ none := by
      simp only [F]
      by_cases h0 : p + (d : ℤ) = 0 <;> simp [h0, hbound]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hread
    rw [step_cfg hifp base .goRight (p + d) G (F l r) none none 1 (some .goRight)
      (fun inp work hw => by simp only [sweep]; rw [hw, hb])]
    rw [show p + (d : ℤ) + ((1 : SignType) : ℤ) = p + ((d + 1 : ℕ) : ℤ) from by
      rw [cast_one]; omega]
    simp

include hifp in
/-- The turn at the right end of the footprint. -/
private lemma step_turn (_hl0 : l ≤ 0) (hr : 0 ≤ r) :
    (sweep i fp).step (cfg i fp base (some .goRight) (r + 1) G (F l r)) =
      cfg i fp base (some .toAnchor) r G (F l r) := by
  have hread : F l r (r + 1) = none := by
    have h1 : ¬ (r + 1 = 0) := by omega
    have h2 : ¬ (l ≤ r + 1 ∧ r + 1 ≤ r) := by omega
    simp [F, h1]
  rw [step_cfg hifp base .goRight (r + 1) G (F l r) none none (-1) (some .toAnchor)
    (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
  rw [show r + 1 + ((-1 : SignType) : ℤ) = r from by rw [cast_neg_one]; omega]
  simp

/-- Blanking the boundary cell of an erased-above tape pushes the boundary down. -/
private lemma update_eraseAbove (T : ℤ → Option Bool) (q : ℤ) :
    Function.update (eraseAbove T q) q none = eraseAbove T (q - 1) := by
  funext z
  by_cases hz : z = q
  · subst hz; simp [eraseAbove]
  · rw [Function.update_of_ne hz]
    have h : q - 1 < z ↔ q < z := by omega
    simp [eraseAbove, h]

/-- The same, one side of the anchor. -/
private lemma update_eraseKeepAnchor (T : ℤ → Option Bool) (q : ℤ) (hq : q ≠ 0) :
    Function.update (eraseKeepAnchor T q) q none = eraseKeepAnchor T (q - 1) := by
  funext z
  by_cases hz : z = q
  · subst hz; simp [eraseKeepAnchor, hq]
  · rw [Function.update_of_ne hz]
    have h : (q - 1 < z ∧ z ≠ 0) ↔ (q < z ∧ z ≠ 0) ∨ z = q ∧ z ≠ 0 := by omega
    by_cases h0 : z = 0
    · simp [eraseKeepAnchor, h0]
    · simp only [eraseKeepAnchor, h0, and_true, ne_eq, not_false_iff]
      have : (q - 1 < z) ↔ (q < z) := by omega
      simp [this]

/-- After erasing down to the anchor, the footprint is the anchor-keeping erasure from `-1`. -/
private lemma eraseAbove_zero_eq (T : ℤ → Option Bool) :
    eraseAbove T 0 = eraseKeepAnchor T (-1) := by
  funext z
  rcases lt_trichotomy z 0 with h | h | h
  · have h1 : ¬ (0 < z) := by omega
    have h2 : ¬ (-1 < z ∧ z ≠ 0) := by omega
    simp [eraseAbove, eraseKeepAnchor, h1, h2]
  · subst h
    simp [eraseAbove, eraseKeepAnchor]
  · have h1 : 0 < z := h
    have h2 : -1 < z ∧ z ≠ 0 := by omega
    simp [eraseAbove, eraseKeepAnchor, h1, h2]

include hifp in
/-- Phase 2: sweep left from the right end down to the anchor, erasing both tapes. -/
private lemma run_toAnchor (hl0 : l ≤ 0) (_h0r : 0 ≤ r) (d : ℕ) (hd : (d : ℤ) ≤ r) :
    (sweep i fp).runFrom
        (cfg i fp base (some .toAnchor) r (eraseAbove G r) (eraseAbove (F l r) r)) d =
      cfg i fp base (some .toAnchor) (r - d) (eraseAbove G (r - d))
        (eraseAbove (F l r) (r - d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [runFrom_succ_eq_step', ih (by omega)]
    have hq : (1 : ℤ) ≤ r - d := by omega
    have hread : eraseAbove (F l r) (r - d) (r - d) = some false := by
      have h0 : ¬ (r - (d : ℤ) = 0) := by omega
      have hin : l ≤ r - (d : ℤ) ∧ r - (d : ℤ) ≤ r := by omega
      simp [eraseAbove, F, h0, hin]
    rw [step_cfg hifp base .toAnchor (r - d) (eraseAbove G (r - d)) (eraseAbove (F l r) (r - d))
      (some none) (some none) (-1) (some .toAnchor)
      (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
    rw [show r - (d : ℤ) + ((-1 : SignType) : ℤ) = r - ((d + 1 : ℕ) : ℤ) from by
      rw [cast_neg_one]; omega]
    rw [applyWrite_some, applyWrite_some, update_eraseAbove, update_eraseAbove,
      show r - (d : ℤ) - 1 = r - ((d + 1 : ℕ) : ℤ) from by omega]

include hifp in
/-- The anchor step: erase the garbage under the anchor, keep the anchor, turn left. -/
private lemma step_anchor (_hl0 : l ≤ 0) (_h0r : 0 ≤ r) :
    (sweep i fp).step
        (cfg i fp base (some .toAnchor) 0 (eraseAbove G 0) (eraseAbove (F l r) 0)) =
      cfg i fp base (some .sweepLeft) (-1) (eraseAbove G (-1))
        (eraseKeepAnchor (F l r) (-1)) := by
  have hread : eraseAbove (F l r) 0 0 = some true := by simp [eraseAbove, F]
  rw [step_cfg hifp base .toAnchor 0 (eraseAbove G 0) (eraseAbove (F l r) 0)
    (some none) none (-1) (some .sweepLeft)
    (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
  rw [show (0 : ℤ) + ((-1 : SignType) : ℤ) = -1 from by rw [cast_neg_one]; omega]
  rw [applyWrite_some, applyWrite_none,
    show Function.update (eraseAbove G 0) 0 none = eraseAbove G (-1) from by
      have h := update_eraseAbove G 0
      simpa using h,
    eraseAbove_zero_eq (F l r)]

include hifp in
/-- Phase 3: sweep left below the anchor, erasing both tapes. -/
private lemma run_sweepLeft (_hl0 : l ≤ 0) (h0r : 0 ≤ r) (d : ℕ) (hd : (d : ℤ) ≤ -l) :
    (sweep i fp).runFrom
        (cfg i fp base (some .sweepLeft) (-1) (eraseAbove G (-1))
          (eraseKeepAnchor (F l r) (-1))) d =
      cfg i fp base (some .sweepLeft) (-1 - d) (eraseAbove G (-1 - d))
        (eraseKeepAnchor (F l r) (-1 - d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [runFrom_succ_eq_step', ih (by omega)]
    have hq : l ≤ -1 - (d : ℤ) ∧ -1 - (d : ℤ) ≤ -1 := by omega
    have hread : eraseKeepAnchor (F l r) (-1 - d) (-1 - d) = some false := by
      have h0 : ¬ (-1 - (d : ℤ) = 0) := by omega
      have hc : ¬ (-1 - (d : ℤ) < -1 - (d : ℤ) ∧ -1 - (d : ℤ) ≠ 0) := by omega
      have hin : l ≤ -1 - (d : ℤ) ∧ -1 - (d : ℤ) ≤ r := by omega
      simp [eraseKeepAnchor, F, h0, hin]
    rw [step_cfg hifp base .sweepLeft (-1 - d) (eraseAbove G (-1 - d))
      (eraseKeepAnchor (F l r) (-1 - d)) (some none) (some none) (-1) (some .sweepLeft)
      (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
    rw [show (-1 : ℤ) - (d : ℤ) + ((-1 : SignType) : ℤ) = -1 - ((d + 1 : ℕ) : ℤ) from by
      rw [cast_neg_one]; omega]
    rw [applyWrite_some, applyWrite_some, update_eraseAbove,
      update_eraseKeepAnchor (F l r) _ (by omega),
      show (-1 : ℤ) - (d : ℤ) - 1 = -1 - ((d + 1 : ℕ) : ℤ) from by omega]

include hifp in
/-- The turn at the left end of the footprint. -/
private lemma step_turnLeft (hl0 : l ≤ 0) :
    (sweep i fp).step
        (cfg i fp base (some .sweepLeft) (l - 1) (eraseAbove G (l - 1))
          (eraseKeepAnchor (F l r) (l - 1))) =
      cfg i fp base (some .seek) l (eraseAbove G (l - 1)) (eraseKeepAnchor (F l r) (l - 1)) := by
  have hread : eraseKeepAnchor (F l r) (l - 1) (l - 1) = none := by
    have hc : ¬ (l - 1 < l - 1 ∧ l - 1 ≠ 0) := by omega
    have h0 : ¬ (l - 1 = 0) := by omega
    have hin : ¬ (l ≤ l - 1 ∧ l - 1 ≤ r) := by omega
    simp [eraseKeepAnchor, F, h0]
  rw [step_cfg hifp base .sweepLeft (l - 1) (eraseAbove G (l - 1))
    (eraseKeepAnchor (F l r) (l - 1)) none none 1 (some .seek)
    (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
  rw [show l - 1 + ((1 : SignType) : ℤ) = l from by rw [cast_one]; omega]
  simp

include hifp in
/-- Phase 4: walk right over the erased cells towards the anchor. -/
private lemma run_seek (_hl0 : l ≤ 0) (d : ℕ) (hd : (d : ℤ) ≤ -l) :
    (sweep i fp).runFrom
        (cfg i fp base (some .seek) l (eraseAbove G (l - 1))
          (eraseKeepAnchor (F l r) (l - 1))) d =
      cfg i fp base (some .seek) (l + d) (eraseAbove G (l - 1))
        (eraseKeepAnchor (F l r) (l - 1)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [runFrom_succ_eq_step', ih (by omega)]
    have hread : eraseKeepAnchor (F l r) (l - 1) (l + d) = none := by
      have hc : l - 1 < l + (d : ℤ) ∧ l + (d : ℤ) ≠ 0 := by omega
      simp [eraseKeepAnchor, hc]
    rw [step_cfg hifp base .seek (l + d) (eraseAbove G (l - 1))
      (eraseKeepAnchor (F l r) (l - 1)) none none 1 (some .seek)
      (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
    rw [show l + (d : ℤ) + ((1 : SignType) : ℤ) = l + ((d + 1 : ℕ) : ℤ) from by
      rw [cast_one]; omega]
    simp

include hifp in
/-- The halting step: erase the anchor, stay at `0`. -/
private lemma step_final (_hl0 : l ≤ 0) :
    (sweep i fp).step
        (cfg i fp base (some .seek) 0 (eraseAbove G (l - 1))
          (eraseKeepAnchor (F l r) (l - 1))) =
      cfg i fp base none 0 (eraseAbove G (l - 1))
        (Function.update (eraseKeepAnchor (F l r) (l - 1)) 0 none) := by
  have hread : eraseKeepAnchor (F l r) (l - 1) 0 = some true := by
    have hc : ¬ (l - 1 < (0 : ℤ) ∧ (0 : ℤ) ≠ 0) := by omega
    simp [eraseKeepAnchor, F]
  rw [step_cfg hifp base .seek 0 (eraseAbove G (l - 1))
    (eraseKeepAnchor (F l r) (l - 1)) none (some none) 0 none
    (fun inp work hw => by simp only [sweep]; rw [hw, hread])]
  rw [show (0 : ℤ) + ((0 : SignType) : ℤ) = 0 from by rw [cast_zero]; omega]
  simp

/-- After the sweep, the garbage tape is blank. -/
private lemma eraseAbove_final (hG : ∀ z, z < l ∨ r < z → G z = none) :
    eraseAbove G (l - 1) = fun _ => none := by
  funext z
  by_cases h : l - 1 < z
  · simp [eraseAbove, h]
  · simp [eraseAbove, h, hG z (Or.inl (by omega))]

/-- After the sweep, the footprint is blank. -/
private lemma eraseKeepAnchor_final (_hl0 : l ≤ 0) :
    Function.update (eraseKeepAnchor (F l r) (l - 1)) 0 none = fun _ => none := by
  funext z
  by_cases h0 : z = 0
  · subst h0; simp
  · rw [Function.update_of_ne h0]
    by_cases h : l - 1 < z
    · simp [eraseKeepAnchor, h, h0]
    · have hF : F l r z = none := by
        have hin : ¬ (l ≤ z ∧ z ≤ r) := by omega
        simp [F, h0, hin]
      simp [eraseKeepAnchor, hF]

/-- The number of steps of the full sweep, started at position `p`. -/
private def steps (l r p : ℤ) : ℕ :=
  (r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1 + (-l).toNat + 1

include hifp in
/-- The garbage tape is blank above `r` and the footprint is exactly `F`: the sweep erases
everything and homes both heads. -/
private lemma run_full (hl0 : l ≤ 0) (h0r : 0 ≤ r) (p : ℤ) (hlp : l ≤ p) (hpr : p ≤ r)
    (hG : ∀ z, z < l ∨ r < z → G z = none) :
    (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r)) (steps l r p) =
      cfg i fp base none 0 (fun _ => none) (fun _ => none) := by
  have hGr : eraseAbove G r = G := by
    funext z
    by_cases h : r < z
    · simp [eraseAbove, h, hG z (Or.inr h)]
    · simp [eraseAbove, h]
  have hFr : eraseAbove (F l r) r = F l r := by
    funext z
    by_cases h : r < z
    · have h0 : ¬ (z = 0) := by omega
      have hin : ¬ (l ≤ z ∧ z ≤ r) := by omega
      simp [eraseAbove, F, h, h0, hin]
    · simp [eraseAbove, h]
  -- segment 1: to the right end
  have e₁ : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat) = cfg i fp base (some .goRight) (r + 1) G (F l r) := by
    rw [run_goRight hifp l r base G p hlp ((r + 1 - p).toNat) (by omega),
      show p + ((r + 1 - p).toNat : ℤ) = r + 1 from by omega]
  -- segment 2: turn, then down to the anchor
  have e₂ : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1 + r.toNat) =
      cfg i fp base (some .toAnchor) 0 (eraseAbove G 0) (eraseAbove (F l r) 0) := by
    rw [runFrom_add, runFrom_add, e₁, runFrom_succ_eq_step', runFrom_zero,
      step_turn hifp l r base G hl0 h0r]
    have h := run_toAnchor hifp l r base G hl0 h0r r.toNat (by omega)
    rw [hGr, hFr, show r - (r.toNat : ℤ) = 0 from by omega] at h
    exact h
  -- segment 3: the anchor step, then down to the left end
  have e₃ : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat) =
      cfg i fp base (some .sweepLeft) (l - 1) (eraseAbove G (l - 1))
        (eraseKeepAnchor (F l r) (l - 1)) := by
    rw [runFrom_add, runFrom_add, e₂, runFrom_succ_eq_step', runFrom_zero,
      step_anchor hifp l r base G hl0 h0r,
      run_sweepLeft hifp l r base G hl0 h0r (-l).toNat (by omega),
      show (-1 : ℤ) - ((-l).toNat : ℤ) = l - 1 from by omega]
  -- segment 4: turn at the left end
  have e₄ : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1) =
      cfg i fp base (some .seek) l (eraseAbove G (l - 1)) (eraseKeepAnchor (F l r) (l - 1)) := by
    rw [runFrom_add, e₃, runFrom_succ_eq_step', runFrom_zero,
      step_turnLeft hifp l r base G hl0]
  -- segment 5: up to the anchor
  have e₅ : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1 + (-l).toNat) =
      cfg i fp base (some .seek) 0 (eraseAbove G (l - 1))
        (eraseKeepAnchor (F l r) (l - 1)) := by
    rw [runFrom_add, e₄]
    have h := run_seek hifp l r base G hl0 (-l).toNat (by omega)
    rw [show l + ((-l).toNat : ℤ) = 0 from by omega] at h
    exact h
  -- the halting step
  rw [show steps l r p = (r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1 + (-l).toNat + 1
      from rfl,
    runFrom_add, e₅, runFrom_succ_eq_step', runFrom_zero, step_final hifp l r base G hl0,
    eraseAbove_final l r G hG, eraseKeepAnchor_final l r hl0]

include hifp in
/-- The configuration at every moment of the sweep: some sweep configuration, with the heads never
leaving the footprint interval widened by one cell, and live before the last step. -/
private lemma run_shape (hl0 : l ≤ 0) (h0r : 0 ≤ r) (p : ℤ) (hlp : l ≤ p) (hpr : p ≤ r)
    (hG : ∀ z, z < l ∨ r < z → G z = none) (m : ℕ) (hm : m ≤ steps l r p) :
    ∃ (q : Option SweepState) (pos : ℤ) (Ti Tf : ℤ → Option Bool),
      (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r)) m =
        cfg i fp base q pos Ti Tf ∧
      l - 1 ≤ pos ∧ pos ≤ r + 1 ∧ (m < steps l r p → q ≠ none) := by
  have hGr : eraseAbove G r = G := by
    funext z
    by_cases h : r < z
    · simp [eraseAbove, h, hG z (Or.inr h)]
    · simp [eraseAbove, h]
  have hFr : eraseAbove (F l r) r = F l r := by
    funext z
    by_cases h : r < z
    · have h0 : ¬ (z = 0) := by omega
      have hin : ¬ (l ≤ z ∧ z ≤ r) := by omega
      simp [eraseAbove, F, h, h0, hin]
    · simp [eraseAbove, h]
  -- the endpoints of the four walking segments
  have chainA : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat) = cfg i fp base (some .goRight) (r + 1) G (F l r) := by
    rw [run_goRight hifp l r base G p hlp ((r + 1 - p).toNat) (by omega),
      show p + ((r + 1 - p).toNat : ℤ) = r + 1 from by omega]
  have chainB : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1) =
      cfg i fp base (some .toAnchor) r (eraseAbove G r) (eraseAbove (F l r) r) := by
    rw [runFrom_add, chainA, runFrom_succ_eq_step', runFrom_zero,
      step_turn hifp l r base G hl0 h0r, hGr, hFr]
  have chainC : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1 + r.toNat + 1) =
      cfg i fp base (some .sweepLeft) (-1) (eraseAbove G (-1))
        (eraseKeepAnchor (F l r) (-1)) := by
    rw [runFrom_add, runFrom_add, chainB,
      run_toAnchor hifp l r base G hl0 h0r r.toNat (by omega),
      show r - (r.toNat : ℤ) = 0 from by omega, runFrom_succ_eq_step', runFrom_zero,
      step_anchor hifp l r base G hl0 h0r]
  have chainD : (sweep i fp).runFrom (cfg i fp base (some .goRight) p G (F l r))
      ((r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1) =
      cfg i fp base (some .seek) l (eraseAbove G (l - 1))
        (eraseKeepAnchor (F l r) (l - 1)) := by
    rw [runFrom_add, runFrom_add, chainC,
      run_sweepLeft hifp l r base G hl0 h0r (-l).toNat (by omega),
      show (-1 : ℤ) - ((-l).toNat : ℤ) = l - 1 from by omega, runFrom_succ_eq_step',
      runFrom_zero, step_turnLeft hifp l r base G hl0]
  have hs : steps l r p =
      (r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1 + (-l).toNat + 1 := rfl
  -- case analysis on the segment `m` falls in
  rcases Nat.lt_or_ge m ((r + 1 - p).toNat + 1) with h₁ | h₁
  · -- walking right
    refine ⟨some .goRight, p + (m : ℤ), G, F l r,
      run_goRight hifp l r base G p hlp m (by omega), by omega, by omega, fun _ => by simp⟩
  rcases Nat.lt_or_ge m ((r + 1 - p).toNat + 1 + r.toNat + 1) with h₂ | h₂
  · -- descending to the anchor
    obtain ⟨d, hd, rfl⟩ : ∃ d : ℕ, (d : ℤ) ≤ r ∧ m = (r + 1 - p).toNat + 1 + d :=
      ⟨m - ((r + 1 - p).toNat + 1), by omega, by omega⟩
    rw [runFrom_add, chainB, run_toAnchor hifp l r base G hl0 h0r d hd]
    exact ⟨_, _, _, _, rfl, by omega, by omega, fun _ => by simp⟩
  rcases Nat.lt_or_ge m ((r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1) with h₃ | h₃
  · -- descending below the anchor
    obtain ⟨d, hd, rfl⟩ : ∃ d : ℕ, (d : ℤ) ≤ -l ∧
        m = (r + 1 - p).toNat + 1 + r.toNat + 1 + d :=
      ⟨m - ((r + 1 - p).toNat + 1 + r.toNat + 1), by omega, by omega⟩
    rw [runFrom_add, chainC, run_sweepLeft hifp l r base G hl0 h0r d hd]
    exact ⟨_, _, _, _, rfl, by omega, by omega, fun _ => by simp⟩
  rcases Nat.lt_or_ge m (steps l r p) with h₄ | h₄
  · -- ascending to the anchor
    obtain ⟨d, hd, rfl⟩ : ∃ d : ℕ, (d : ℤ) ≤ -l ∧
        m = (r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1 + d :=
      ⟨m - ((r + 1 - p).toNat + 1 + r.toNat + 1 + (-l).toNat + 1), by omega, by omega⟩
    rw [runFrom_add, chainD, run_seek hifp l r base G hl0 d hd]
    exact ⟨_, _, _, _, rfl, by omega, by omega, fun _ => by simp⟩
  · -- the halting configuration
    have hm' : m = steps l r p := by omega
    subst hm'
    exact ⟨none, 0, fun _ => none, fun _ => none,
      run_full hifp l r base G hl0 h0r p hlp hpr hG, by omega, by omega, fun h => absurd h
        (by omega)⟩

include hifp in
private lemma cfg_workTapePos_i (q p Ti Tf) :
    (cfg i fp base q p Ti Tf).workTapePos i = p := by
  simp only [cfg]
  rw [Function.update_of_ne hifp, Function.update_self]

private lemma cfg_workTapePos_other (l' : Fin K) (hi : l' ≠ i) (hfp : l' ≠ fp) (q p Ti Tf) :
    (cfg i fp base q p Ti Tf).workTapePos l' = base.workTapePos l' := by
  simp only [cfg]
  rw [Function.update_of_ne hfp, Function.update_of_ne hi]

end Run

end Sweep

open Sweep in
/-- **Sweeping a footprinted pair clean.** Given a footprint over `[l, r]` with the anchor at `0`
on tape `fp`, and garbage confined to `[l, r]` on tape `i` — possibly with blanks inside, so that
no scan of tape `i` itself could find its extent — the sweep machine erases both tapes completely
and homes both heads to `0`, in time linear in the footprint interval and space exceeding it only
by a constant, touching nothing else. -/
public theorem exists_sweepPair {K : ℕ} (i fp : Fin K) (hifp : i ≠ fp) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM K Bool State),
      ∀ (input : List Bool) (c : Cfg K Bool State input) (l r p : ℤ),
        c.state = some tm.q₀ → l ≤ 0 → 0 ≤ r → l ≤ p → p ≤ r →
        c.workTapePos i = p → c.workTapePos fp = p →
        (∀ z, c.workTapes fp z = if z = 0 then some true
          else if l ≤ z ∧ z ≤ r then some false else none) →
        (∀ z, z < l ∨ r < z → c.workTapes i z = none) →
        ∃ u ≤ 4 * (r - l).toNat + 8,
          (∀ m < u, (tm.runFrom c m).state ≠ none) ∧
          tm.runFrom c u = ⟨none, c.inputPos,
            Function.update (Function.update c.workTapes i fun _ => none) fp fun _ => none,
            Function.update (Function.update c.workTapePos i 0) fp 0,
            c.output⟩ ∧
          tm.spaceUsed c u ≤ 2 * (r - l).toNat + 4 + K := by
  refine ⟨SweepState, inferInstance, sweep i fp,
    fun input c l r p hq hl0 h0r hlp hpr hpi hpf hF hG => ?_⟩
  -- the start is a sweep configuration over the given data
  have hFfun : c.workTapes fp = F l r := funext fun z => hF z
  have hc : c = cfg i fp c (some .goRight) p (c.workTapes i) (F l r) := by
    refine Cfg.ext hq rfl ?_ ?_ rfl
    · rw [← hFfun]
      simp [cfg, Function.update_eq_self]
    · simp only [cfg]
      funext l'
      by_cases h1 : l' = fp
      · subst h1; rw [Function.update_self]; exact hpf
      · rw [Function.update_of_ne h1]
        by_cases h2 : l' = i
        · subst h2; rw [Function.update_self]; exact hpi
        · rw [Function.update_of_ne h2]
  -- the run, read back on `c`
  have hrun : ∀ m ≤ steps l r p, ∃ (q' : Option SweepState) (pos : ℤ)
      (Ti Tf : ℤ → Option Bool),
      (sweep i fp).runFrom c m = cfg i fp c q' pos Ti Tf ∧
      l - 1 ≤ pos ∧ pos ≤ r + 1 ∧ (m < steps l r p → q' ≠ none) := by
    intro m hm
    obtain ⟨q', pos, Ti, Tf, heq, h1, h2, h3⟩ :=
      run_shape hifp l r c (c.workTapes i) hl0 h0r p hlp hpr hG m hm
    rw [← hc] at heq
    exact ⟨q', pos, Ti, Tf, heq, h1, h2, h3⟩
  have hfull : (sweep i fp).runFrom c (steps l r p) =
      cfg i fp c none 0 (fun _ => none) (fun _ => none) := by
    have h := run_full hifp l r c (c.workTapes i) hl0 h0r p hlp hpr hG
    rwa [← hc] at h
  refine ⟨steps l r p, by simp only [steps]; omega, ?_, ?_, ?_⟩
  · -- activity
    intro m hm
    obtain ⟨q', pos, Ti, Tf, heq, -, -, hq'⟩ := hrun m (by omega)
    rw [heq]
    simpa [cfg] using hq' hm
  · -- the halting configuration
    rw [hfull]
    rfl
  · -- the space bound
    have hB : ∀ l' : Fin K, l' = i ∨ l' = fp →
        (sweep i fp).spaceUsedByTape c (steps l r p) l' ≤ (r - l).toNat + 3 := by
      intro l' hl'
      have hsub : (sweep i fp).visitedByTapeHead c (steps l r p) l' ⊆
          Finset.Icc (l - 1) (r + 1) := by
        intro z hz
        obtain ⟨m, hm, rfl⟩ := mem_visitedByTapeHead.mp hz
        obtain ⟨q', pos, Ti, Tf, heq, hlo, hhi, -⟩ := hrun m (by omega)
        rw [heq]
        rcases hl' with rfl | rfl
        · rw [cfg_workTapePos_i hifp]
          exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
        · rw [cfg_workTapePos_fp]
          exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      calc (sweep i fp).spaceUsedByTape c (steps l r p) l'
          ≤ (Finset.Icc (l - 1) (r + 1)).card := Finset.card_le_card hsub
        _ = (r + 1 + 1 - (l - 1)).toNat := Int.card_Icc _ _
        _ ≤ (r - l).toNat + 3 := by omega
    have h1 : ∀ l' : Fin K, l' ≠ i → l' ≠ fp →
        (sweep i fp).spaceUsedByTape c (steps l r p) l' ≤ 1 := by
      intro l' hi' hfp'
      have hsub : (sweep i fp).visitedByTapeHead c (steps l r p) l' ⊆
          {c.workTapePos l'} := by
        intro z hz
        obtain ⟨m, hm, rfl⟩ := mem_visitedByTapeHead.mp hz
        obtain ⟨q', pos, Ti, Tf, heq, -, -, -⟩ := hrun m (by omega)
        rw [heq, cfg_workTapePos_other c l' hi' hfp']
        exact Finset.mem_singleton_self _
      calc (sweep i fp).spaceUsedByTape c (steps l r p) l'
          ≤ ({c.workTapePos l'} : Finset ℤ).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    have hfpmem : fp ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hifp, Finset.mem_univ _⟩
    have hK : 2 ≤ K := by
      rcases K with _ | _ | K
      · exact i.elim0
      · exact absurd (Fin.ext (by omega : i.val = fp.val)) hifp
      · omega
    calc (sweep i fp).spaceUsed c (steps l r p)
        = (sweep i fp).spaceUsedByTape c (steps l r p) i +
            ∑ l' ∈ Finset.univ.erase i, (sweep i fp).spaceUsedByTape c (steps l r p) l' :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      _ = (sweep i fp).spaceUsedByTape c (steps l r p) i +
            ((sweep i fp).spaceUsedByTape c (steps l r p) fp +
              ∑ l' ∈ (Finset.univ.erase i).erase fp,
                (sweep i fp).spaceUsedByTape c (steps l r p) l') := by
          rw [Finset.add_sum_erase _ _ hfpmem]
      _ ≤ ((r - l).toNat + 3) + (((r - l).toNat + 3) + (K - 2) * 1) := by
          have hcard : ((Finset.univ.erase i).erase fp).card = K - 1 - 1 := by
            rw [Finset.card_erase_of_mem hfpmem, Finset.card_erase_of_mem (Finset.mem_univ i)]
            simp
          refine Nat.add_le_add (hB i (Or.inl rfl)) (Nat.add_le_add (hB fp (Or.inr rfl)) ?_)
          calc ∑ l' ∈ (Finset.univ.erase i).erase fp,
                (sweep i fp).spaceUsedByTape c (steps l r p) l'
              ≤ ((Finset.univ.erase i).erase fp).card • 1 :=
                Finset.sum_le_card_nsmul _ _ 1 fun l' hl' => h1 l'
                  (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl'))
                  (Finset.ne_of_mem_erase hl')
            _ = (K - 2) * 1 := by rw [hcard]; simp; omega
      _ ≤ 2 * (r - l).toNat + 4 + K := by omega

end Turing.MultiTapeTM
