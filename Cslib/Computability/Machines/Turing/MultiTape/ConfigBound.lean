/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option

/-!
# A bound on the number of reachable configurations in bounded space

For a deterministic multi-tape Turing machine that uses at most `s` cells of work-tape space, the
number of distinct configurations it can be in is bounded by an explicit function of `s` (and the
machine's parameters). This is the counting fact underlying, for instance, the collapse of very
small space classes and the inclusion `PSPACE ⊆ EXP`.

We record everything about a configuration that can influence future behaviour *except* the
write-only output (which only grows and never affects the transition function). We provide two
versions:

* `MultiTapeTM.card_image_storage_le` bounds the number of *storage configurations* — the control
  state together with the work-tape contents and head positions, ignoring even the read-only input
  head — by `storageBound k sym state s`.
* `MultiTapeTM.card_image_config_le` additionally tracks the input head position, giving the bound
  `(n + 2) * storageBound k sym state s` on the number of full configurations of an input of
  length `n`.

## Design

The key geometric facts (`MultiTapeTM.headPos_natAbs_le_space` and `MultiTapeTM.content_natAbs_le`)
are that, starting from the all-blank tapes with every head at `0` and moving by at most one cell
per step, a computation that has visited at most `s` work-tape cells keeps every head position and
every non-blank cell within the window `[-s, s]`. Hence a storage configuration reachable within
space `s` is determined by finite data over that window, giving the bound. Both counting theorems
share this geometry and the window encoding `MultiTapeTM.encStorage`, so the same machinery serves
the full-configuration bound needed for time-bounding space-bounded machines.
-/

@[expose] public section

open Cslib

namespace Turing.MultiTapeTM

variable {k sym state : ℕ}

def storageBound (k sym state s : ℕ) : ℕ :=
  (state + 1) * ((sym + 1) ^ (2 * s + 1) * (2 * s + 1)) ^ k

def Cfg.storage {k : ℕ} {Sym St : Type*} (c : Cfg k Sym St) :
    Option St × (Fin k → ℤ → Option Sym) × (Fin k → ℤ) :=
  (c.state, c.workTapes, c.workTapePos)

/-- head position at step `t` on tape `i` -/
def headPos (tm : MultiTapeTM k (Fin sym) (Fin state)) (input : List (Fin sym))
    (i : Fin k) (t : ℕ) : ℤ := (tm.configs (tm.initCfg input) t).workTapePos i

def visited (tm : MultiTapeTM k (Fin sym) (Fin state)) (input : List (Fin sym))
    (i : Fin k) (t : ℕ) : Finset ℤ := (Finset.range (t+1)).image (fun t' => headPos tm input i t')

variable (tm : MultiTapeTM k (Fin sym) (Fin state)) (input : List (Fin sym)) (i : Fin k)

lemma headPos_zero : headPos tm input i 0 = 0 := rfl

lemma headPos_step_le (t : ℕ) : |headPos tm input i (t+1) - headPos tm input i t| ≤ 1 := by
  have := workTapePos_step_le (tm := tm) (tm.configs (tm.initCfg input) t) i
  simpa [headPos, configs, Function.iterate_succ_apply'] using this

lemma mem_visited_self (t : ℕ) : headPos tm input i t ∈ visited tm input i t := by
  simp only [visited, Finset.mem_image, Finset.mem_range]
  exact ⟨t, by omega, rfl⟩

lemma visited_mono {t t' : ℕ} (h : t ≤ t') : visited tm input i t ⊆ visited tm input i t' := by
  intro z hz
  simp only [visited, Finset.mem_image, Finset.mem_range] at hz ⊢
  obtain ⟨t'', ht'', rfl⟩ := hz
  exact ⟨t'', by omega, rfl⟩

/-- Discrete intermediate value: every integer between `0` and the head position at step `t` has
been visited by step `t`. -/
lemma Icc_subset_visited (t : ℕ) :
    Finset.Icc (min 0 (headPos tm input i t)) (max 0 (headPos tm input i t))
      ⊆ visited tm input i t := by
  induction t with
  | zero => simpa [headPos_zero] using mem_visited_self tm input i 0
  | succ t ih =>
    intro z hz
    simp only [Finset.mem_Icc] at hz
    have hstep := headPos_step_le tm input i t
    by_cases hin : min 0 (headPos tm input i t) ≤ z ∧ z ≤ max 0 (headPos tm input i t)
    · exact visited_mono tm input i (Nat.le_succ t) (ih (Finset.mem_Icc.mpr hin))
    · have : z = headPos tm input i (t+1) := by
        rw [abs_le] at hstep; omega
      rw [this]; exact mem_visited_self tm input i (t+1)


lemma headPos_card (t : ℕ) : (headPos tm input i t).natAbs + 1 ≤ (visited tm input i t).card := by
  have hsub := Icc_subset_visited tm input i t
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  omega

lemma spaceUsedByTape_eq_card_visited (T : ℕ) :
    tm.spaceUsedByTape (tm.initCfg input) T i = (visited tm input i T).card := by
  unfold spaceUsedByTape visited headPos
  congr 1

lemma headPos_natAbs_le_space (T s : ℕ) (hs : tm.spaceUsed (tm.initCfg input) T ≤ s)
    {t : ℕ} (ht : t ≤ T) : (headPos tm input i t).natAbs ≤ s := by
  have h1 := headPos_card tm input i t
  have h2 : (visited tm input i t).card ≤ (visited tm input i T).card :=
    Finset.card_le_card (visited_mono tm input i ht)
  have h3 : (visited tm input i T).card = tm.spaceUsedByTape (tm.initCfg input) T i :=
    (spaceUsedByTape_eq_card_visited tm input i T).symm
  have h4 : tm.spaceUsedByTape (tm.initCfg input) T i ≤ tm.spaceUsed (tm.initCfg input) T :=
    Finset.single_le_sum (f := fun i => tm.spaceUsedByTape (tm.initCfg input) T i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega


lemma step_workTapes_mem (c : Cfg k (Fin sym) (Fin state)) (j : Fin k) (z : ℤ)
    (h : (tm.step c).workTapes j z ≠ none) :
    z = c.workTapePos j ∨ c.workTapes j z ≠ none := by
  rw [step] at h
  cases hst : c.state with
  | none => simp only [hst] at h; right; exact h
  | some q =>
    simp only [hst] at h
    rcases hw : ((tm.tr q c.inputSymbol c.workTapeSymbols).workActions j).1 with _ | sy
    · right; simpa only [hw] using h
    · by_cases hz : z = c.workTapePos j
      · exact Or.inl hz
      · right; simp only [hw, Function.update_of_ne hz] at h; exact h

lemma content_visited (t : ℕ) (z : ℤ)
    (h : (tm.configs (tm.initCfg input) t).workTapes i z ≠ none) : z ∈ visited tm input i t := by
  induction t with
  | zero => exfalso; simp [configs, initCfg] at h
  | succ t ih =>
    have hst : tm.configs (tm.initCfg input) (t+1)
        = tm.step (tm.configs (tm.initCfg input) t) := by
      rw [configs, configs, Function.iterate_succ_apply']
    rw [hst] at h
    rcases step_workTapes_mem tm _ i z h with hz | hz
    · rw [hz]; exact visited_mono tm input i (Nat.le_succ t) (mem_visited_self tm input i t)
    · exact visited_mono tm input i (Nat.le_succ t) (ih hz)

lemma content_natAbs_le (T s : ℕ) (hs : tm.spaceUsed (tm.initCfg input) T ≤ s)
    {t : ℕ} (ht : t ≤ T) (z : ℤ)
    (h : (tm.configs (tm.initCfg input) t).workTapes i z ≠ none) : z.natAbs ≤ s := by
  have hzV := content_visited tm input i t z h
  simp only [visited, Finset.mem_image, Finset.mem_range] at hzV
  obtain ⟨t', ht', rfl⟩ := hzV
  exact headPos_natAbs_le_space tm input i T s hs (by omega)



/-- The finite "window" type into which storage configurations of space `≤ s` are encoded. -/
abbrev Win (k sym state s : ℕ) : Type :=
  Option (Fin state) × (Fin k → ↥(Finset.Icc (-(s:ℤ)) s) → Option (Fin sym)) ×
    (Fin k → ↥(Finset.Icc (-(s:ℤ)) s))

/-- A storage tuple lies in the window of width `s`: all head positions and all non-blank cells
have absolute value `≤ s`. -/
def WindowP (k sym state s : ℕ)
    (x : Option (Fin state) × (Fin k → ℤ → Option (Fin sym)) × (Fin k → ℤ)) : Prop :=
  (∀ j, (x.2.2 j).natAbs ≤ s) ∧ (∀ j z, x.2.1 j z ≠ none → z.natAbs ≤ s)

/-- Encoding of a storage tuple into the finite window type. -/
noncomputable def encStorage (k sym state s : ℕ)
    (x : Option (Fin state) × (Fin k → ℤ → Option (Fin sym)) × (Fin k → ℤ)) :
    Win k sym state s :=
  (x.1, (fun j z => x.2.1 j z.1),
    fun j => if h : x.2.2 j ∈ Finset.Icc (-(s:ℤ)) s then ⟨x.2.2 j, h⟩ else ⟨0, by simp⟩)

lemma mem_Icc_of_natAbs_le {s : ℕ} {z : ℤ} (h : z.natAbs ≤ s) :
    z ∈ Finset.Icc (-(s:ℤ)) s := by
  simp only [Finset.mem_Icc]; omega

/-- The encoding is injective on storage tuples satisfying the window predicate. -/
lemma encStorage_injOn (k sym state s : ℕ) :
    Set.InjOn (encStorage k sym state s) {x | WindowP k sym state s x} := by
  rintro x ⟨hxp, hxc⟩ y ⟨hyp, hyc⟩ hxy
  simp only [encStorage, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2, h3⟩ := hxy
  refine Prod.ext h1 (Prod.ext ?_ ?_)
  · funext j w
    by_cases hw : w ∈ Finset.Icc (-(s:ℤ)) s
    · simpa using congrFun (congrFun h2 j) ⟨w, hw⟩
    · have hwabs : s < w.natAbs := by simp only [Finset.mem_Icc, not_and, not_le] at hw; omega
      have cx : x.2.1 j w = none := by by_contra hc; exact absurd (hxc j w hc) (by omega)
      have cy : y.2.1 j w = none := by by_contra hc; exact absurd (hyc j w hc) (by omega)
      rw [cx, cy]
  · funext j
    have hj := congrFun h3 j
    rw [dif_pos (mem_Icc_of_natAbs_le (hxp j)), dif_pos (mem_Icc_of_natAbs_le (hyp j))] at hj
    exact Subtype.ext_iff.mp hj

lemma card_Win (k sym state s : ℕ) :
    Fintype.card (Win k sym state s) = storageBound k sym state s := by
  have hI : (Finset.Icc (-(s:ℤ)) s).card = 2 * s + 1 := by rw [Int.card_Icc]; omega
  simp only [Win, Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_coe, hI, storageBound]
  rw [← mul_pow]


lemma storage_windowP (tm : MultiTapeTM k (Fin sym) (Fin state)) (input : List (Fin sym))
    (T s : ℕ) (hs : tm.spaceUsed (tm.initCfg input) T ≤ s) {t : ℕ} (ht : t ≤ T) :
    WindowP k sym state s (tm.configs (tm.initCfg input) t).storage := by
  refine ⟨fun j => ?_, fun j z hz => ?_⟩
  · exact headPos_natAbs_le_space tm input j T s hs ht
  · exact content_natAbs_le tm input j T s hs ht z hz

open scoped Classical in
theorem card_image_storage_le (tm : MultiTapeTM k (Fin sym) (Fin state))
    (input : List (Fin sym)) (T s : ℕ) (hs : tm.spaceUsed (tm.initCfg input) T ≤ s) :
    ((Finset.range (T + 1)).image
      (fun t => (tm.configs (tm.initCfg input) t).storage)).card ≤ storageBound k sym state s := by
  classical
  rw [← card_Win k sym state s, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (encStorage k sym state s)
    (fun x _ => Finset.mem_univ _) ?_
  refine Set.InjOn.mono ?_ (encStorage_injOn k sym state s)
  intro x hx
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact storage_windowP tm input T s hs (by omega)


lemma step_input (tm : MultiTapeTM k (Fin sym) (Fin state)) (c : Cfg k (Fin sym) (Fin state)) :
    (tm.step c).input = c.input := by
  rw [step]; cases c.state <;> rfl

lemma configs_input (tm : MultiTapeTM k (Fin sym) (Fin state)) (input : List (Fin sym)) (t : ℕ) :
    (tm.configs (tm.initCfg input) t).input = input := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hstep : tm.configs (tm.initCfg input) (t + 1)
        = tm.step (tm.configs (tm.initCfg input) t) := by
      rw [configs, configs, Function.iterate_succ_apply']
    rw [hstep, step_input, ih]

open scoped Classical in
theorem card_image_config_le (tm : MultiTapeTM k (Fin sym) (Fin state))
    (input : List (Fin sym)) (T s : ℕ) (hs : tm.spaceUsed (tm.initCfg input) T ≤ s) :
    ((Finset.range (T + 1)).image (fun t =>
      ((tm.configs (tm.initCfg input) t).inputPos.val,
       (tm.configs (tm.initCfg input) t).storage))).card
      ≤ (input.length + 2) * storageBound k sym state s := by
  classical
  have hcard : (Finset.range (input.length + 2) ×ˢ
      (Finset.univ : Finset (Win k sym state s))).card
      = (input.length + 2) * storageBound k sym state s := by
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, card_Win]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun x => (x.1, encStorage k sym state s x.2)) ?_ ?_
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    have hlt := (tm.configs (tm.initCfg input) t).inputPos.isLt
    have hlen : (tm.configs (tm.initCfg input) t).input.length = input.length := by
      rw [configs_input]
    omega
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx hy
    obtain ⟨tx, htx, rfl⟩ := hx
    obtain ⟨ty, hty, rfl⟩ := hy
    simp only [Prod.mk.injEq] at hxy
    have hst := encStorage_injOn k sym state s
      (storage_windowP tm input T s hs (show tx ≤ T by omega))
      (storage_windowP tm input T s hs (show ty ≤ T by omega)) hxy.2
    exact Prod.ext hxy.1 hst

end Turing.MultiTapeTM
