/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeView

/-!
# The span of a head walk is bounded by the space it uses

`Extent` measures a zipper by the *span* of the positions its head has covered, while
`MultiTapeTM.spaceUsedByTape` measures a computation by the *number of distinct cells* the head
visited. This file shows the former is bounded by the latter, which is what turns an
`Extent`-based size bound into a bound in the simulated machine's space.

The two agree because a head moves by at most one cell per step (`workTapePos_step_le`), so the
set of visited positions is an interval: a discrete intermediate value theorem. Without that, a
walk could in principle jump and cover a wide span while visiting few cells.

The first two results are about arbitrary integer walks and have nothing to do with machines;
`span_le_spaceUsedByTape` specialises them to `MultiTapeTM`.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

namespace Simulation

/-- **Discrete intermediate value theorem**, increasing form: a walk taking steps of size at most
one attains every value between its endpoints. -/
lemma exists_eq_of_step {f : ℕ → ℤ} (hstep : ∀ j, |f (j + 1) - f j| ≤ 1) :
    ∀ (b a : ℕ), a ≤ b → ∀ y : ℤ, f a ≤ y → y ≤ f b → ∃ j, a ≤ j ∧ j ≤ b ∧ f j = y := by
  intro b
  induction b with
  | zero =>
    intro a hab y h1 h2
    have ha : a = 0 := by omega
    subst ha
    exact ⟨0, le_refl _, le_refl _, by omega⟩
  | succ b ih =>
    intro a hab y h1 h2
    by_cases hcase : y ≤ f b
    · rcases Nat.lt_or_ge a (b + 1) with h | h
      · obtain ⟨j, hj1, hj2, hj3⟩ := ih a (by omega) y h1 hcase
        exact ⟨j, hj1, by omega, hj3⟩
      · have ha : a = b + 1 := by omega
        subst ha
        exact ⟨b + 1, le_refl _, le_refl _, by omega⟩
    · obtain ⟨hs1, hs2⟩ := abs_le.mp (hstep b)
      exact ⟨b + 1, hab, le_refl _, by omega⟩

/-- **Discrete intermediate value theorem**, either direction. -/
lemma exists_eq_between {f : ℕ → ℤ} (hstep : ∀ j, |f (j + 1) - f j| ≤ 1)
    {a b : ℕ} (hab : a ≤ b) {y : ℤ}
    (h1 : min (f a) (f b) ≤ y) (h2 : y ≤ max (f a) (f b)) :
    ∃ j, a ≤ j ∧ j ≤ b ∧ f j = y := by
  rcases le_total (f a) (f b) with hf | hf
  · rw [min_eq_left hf] at h1
    rw [max_eq_right hf] at h2
    exact exists_eq_of_step hstep b a hab y h1 h2
  · rw [min_eq_right hf] at h1
    rw [max_eq_left hf] at h2
    have hstep' : ∀ j, |(fun j => -f j) (j + 1) - (fun j => -f j) j| ≤ 1 := by
      intro j
      change |(-f (j + 1)) - (-f j)| ≤ 1
      have hr : (-f (j + 1)) - (-f j) = -(f (j + 1) - f j) := by ring
      rw [hr, abs_neg]
      exact hstep j
    have h1' : (fun j => -f j) a ≤ -y := by change -f a ≤ -y; omega
    have h2' : -y ≤ (fun j => -f j) b := by change -y ≤ -f b; omega
    obtain ⟨j, hj1, hj2, hj3⟩ :=
      exists_eq_of_step (f := fun j => -f j) hstep' b a hab (-y) h1' h2'
    refine ⟨j, hj1, hj2, ?_⟩
    have hj : -f j = -y := hj3
    omega

/-- **The span between any two visited positions is bounded by the number of positions visited.**
This is the abstract form of "a zipper is no bigger than the space used". -/
lemma card_image_ge {f : ℕ → ℤ} (hstep : ∀ j, |f (j + 1) - f j| ≤ 1) (n : ℕ) {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) :
    (f b - f a).natAbs + 1 ≤ ((Finset.range (n + 1)).image f).card := by
  have hsub : Finset.Icc (min (f a) (f b)) (max (f a) (f b))
      ⊆ (Finset.range (n + 1)).image f := by
    intro y hy
    simp only [Finset.mem_Icc] at hy
    rcases le_total a b with h | h
    · obtain ⟨j, _, hj2, hj3⟩ := exists_eq_between hstep h hy.1 hy.2
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), hj3⟩
    · have h1' : min (f b) (f a) ≤ y := by rw [min_comm]; exact hy.1
      have h2' : y ≤ max (f b) (f a) := by rw [max_comm]; exact hy.2
      obtain ⟨j, _, hj2, hj3⟩ := exists_eq_between hstep h h1' h2'
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), hj3⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  omega

/-- **The bridge to cslib's space measure.** For any two moments in a computation, the distance
the head travelled between them is bounded by the number of cells it visited — so an
`Extent`-based size bound is a bound in the simulated machine's *space*, not its running time. -/
lemma span_le_spaceUsedByTape {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k)
    {a b : ℕ} (ha : a ≤ t) (hb : b ≤ t) :
    ((tm.runFrom cfg b).workTapePos i - (tm.runFrom cfg a).workTapePos i).natAbs + 1
      ≤ tm.spaceUsedByTape cfg t i := by
  have hstep : ∀ j : ℕ,
      |(fun j => (tm.runFrom cfg j).workTapePos i) (j + 1)
        - (fun j => (tm.runFrom cfg j).workTapePos i) j| ≤ 1 := by
    intro j
    change |(tm.runFrom cfg (j + 1)).workTapePos i - (tm.runFrom cfg j).workTapePos i| ≤ 1
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact MultiTapeTM.workTapePos_step_le _ i
  unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
  exact card_image_ge (f := fun j => (tm.runFrom cfg j).workTapePos i) hstep t ha hb

end Simulation

end MultiTapeTM

end Turing
