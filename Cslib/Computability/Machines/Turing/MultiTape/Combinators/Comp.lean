/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import Mathlib.Tactic.Ring

/-!
# Composing tidy computations

`tm₂.comp tm₁ mark` runs `tm₁` with its output written to a work tape, then runs `tm₂` reading its
input from that tape, and finally clears the tape. If both machines compute tidily, so does the
composition. Its time is the sum of the two times plus a term linear in the length of the
intermediate word; so is its space, since the intermediate word is kept on a work tape.

## Main definitions

* `Turing.MultiTapeTM.comp`: the composed machine.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.comp`: tidy computations compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp`: tidily computable functions compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp'`: the same, with the length of the
  intermediate word bounded by the time of the inner function.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.comp`: the same for bounds `t` and `s`
  of the input length, shared by both functions, given a bound `l` on the length of the
  intermediate word.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp`: hence `f ∘ g`
  is computable in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp`:
  the same for bounds of the input length.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- `tm₂` after `tm₁`, both with their work tapes padded to `max k₁ k₂`: run `tm₁` with its output
written to the work tape `Fin.natAdd (max k₁ k₂) 0`, run `tm₂` reading its input from that tape
(using `mark` on the last work tape to flag the left end of the input), then clear that tape. -/
public noncomputable def comp (tm₂ : MultiTapeTM k₂ Symbol S₂) (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (mark : Symbol) : MultiTapeTM (max k₁ k₂ + 2) Symbol
      ((S₁ ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ S₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      ((clearWork Symbol).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0))))

/-- Clearing the only non-blank work tape leaves all work tapes blank. -/
public theorem transformsTapes_clearWork_only {k : ℕ} (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i))
      (fun _ ws => ws = Function.update (fun _ => []) i w)
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = []) (3 * (w.length + 1)) (w.length + 1 + k) :=
  (transformsTapes_clearWork_tapeEmb i w).imp (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl

/-- If `tm₁` computes `w` from `x` tidily and `tm₂` computes `y` from `w` tidily, then
`tm₂.comp tm₁ mark` computes `y` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.comp {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x w y : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x w t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace w y t₂ s₂) (mark : Symbol) :
    (tm₂.comp tm₁ mark).ComputesTidilyInTimeAndSpace x y (t₁ + t₂ + 4 * w.length + 9)
      (s₁ + s₂ + 5 * w.length + (6 * max k₁ k₂ + 17)) := by
  set m := max k₁ k₂
  -- the work tape holding the intermediate word `w`
  set mid : Fin (m + 2) := Fin.natAdd m 0
  have hmid : Fin.append (fun _ : Fin m => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) mid w := by
    rw [← Fin.append_const (m := m) (n := 2) [], ← Fin.append_update_right]
    congr 1
    simp [funext_iff, Fin.forall_fin_two]
  -- phase 1: `tm₁` writes `w` to `mid`
  have hQ₁ (ws' : Fin (m + 1 + 1) → List Symbol)
      (hv : (fun j => ws' (Fin.castSuccEmb j)) = Function.update (fun _ => []) (Fin.last m) w)
      (hx : ∀ l ∉ Set.range Fin.castSuccEmb, ws' l = []) :
      ws' = Function.update (fun _ => []) mid w := by
    funext l
    induction l using Fin.lastCases with
    | last =>
      rw [hx _ fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj]
      simp [mid, Fin.ext_iff]
    | cast j =>
      rw [show ws' j.castSucc = _ from congrFun hv j]
      simp [mid, Function.update_apply, Fin.ext_iff]
  have hp₁ := ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
    Fin.castSuccEmb).imp (P' := fun inp ws => inp = x ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) mid w ∧ e = [])
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ ws' _ ⟨_, hws⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨hQ₁ ws' hv fun l hl => (hx l hl).trans
      (congrFun hws l), he⟩) le_rfl le_rfl
  -- phase 2: `tm₂` reads `w` from `mid` and emits `y`
  obtain ⟨hrun₂, hspace₂⟩ :=
    computesTidily_iff.mp (h₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))
  have hp₂ := (transformsTapes_inputFromWord_of_runFrom mark hrun₂ hspace₂).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) mid w)
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) mid w ∧ e = y)
    (fun _ _ hws => hws.trans hmid.symm) (fun _ _ _ _ _ ⟨hws', he⟩ => ⟨hws'.trans hmid, he⟩)
    le_rfl le_rfl
  -- phase 3: clear `mid`
  have hp₃ := transformsTapes_clearWork_only (Symbol := Symbol) mid w
  exact (hp₁.seq_eq (hp₂.seq_eq hp₃)).imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨hws, he⟩ => ⟨hws, by simp [he]⟩) (by omega) (by omega)

/-- If `g` and `f` are tidily computable, so is `f ∘ g`, in the sum of their times and spaces plus
a term linear in the length of the intermediate word `encMid (g a)`. -/
public theorem ComputableTidilyInTimeAndSpace.comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₁ a + t₂ (g a) + c * ((encMid (g a)).length + 1))
      (fun a => s₁ a + s₂ (g a) + c * ((encMid (g a)).length + 1)) := by
  obtain ⟨k₁, S₁, _, tm₁, h₁⟩ := hg
  obtain ⟨k₂, S₂, _, tm₂, h₂⟩ := hf
  refine ⟨6 * max k₁ k₂ + 17, _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => ((h₁ a).comp (h₂ (g a)) true).mono ?_ ?_⟩ <;> dsimp only <;> ring_nf <;> omega

/-- If `g` and `f` are tidily computable, so is `f ∘ g`: the intermediate word is no longer than
the time of `g`. -/
public theorem ComputableTidilyInTimeAndSpace.comp' {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₂ (g a) + c * (t₁ a + 1)) (fun a => s₁ a + s₂ (g a) + c * (t₁ a + 1)) := by
  obtain ⟨c, h⟩ := hf.comp hg
  obtain ⟨_, _, _, _, h₁⟩ := hg
  refine ⟨c + 1, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have hlen : (encMid (g a)).length ≤ t₁ a := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c (Nat.add_le_add_right hlen 1)
    rw [Nat.add_one_mul]
    omega

/-- If `g` and `f` are tidily computable in time `t` and space `s` of the length of their input, for
monotone `t` and `s`, and the output of `g` on inputs of length `n` has length at most `l n`, then
`f ∘ g` is tidily computable with bounds depending on `t (l n)`, `s (l n)` and `l n`. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.comp {α β γ : Type*} {g : α → β}
    {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {l t s : ℕ → ℕ} (ht : Monotone t) (hs : Monotone s)
    (hl : ∀ a, (encMid (g a)).length ≤ l (encIn a).length)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f encMid encOut t s)
    (hg : ComputableTidilyInTimeAndSpaceOfLength g encIn encMid t s) :
    ∃ c, ComputableTidilyInTimeAndSpaceOfLength (f ∘ g) encIn encOut
      (fun n => t n + t (l n) + c * (l n + 1)) (fun n => s n + s (l n) + c * (l n + 1)) := by
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp hf hg
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;> dsimp only <;> gcongr
  exacts [ht (hl a), hl a, hs (hl a), hl a]

/-- If `g` and `f` are tidily computable, then `f ∘ g` is computable. -/
public theorem ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp {α β γ : Type*}
    {g : α → β} {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₂ (g a) + c * (t₁ a + 1)) (fun a => s₁ a + s₂ (g a) + c * (t₁ a + 1)) :=
  let ⟨c, h⟩ := hf.comp' hg
  ⟨c, h.computableInTimeAndSpace⟩

/-- If `g` and `f` are tidily computable in time `t` and space `s` of the length of their input, for
monotone `t` and `s`, and the output of `g` on inputs of length `n` has length at most `l n`, then
`f ∘ g` is computable. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp
    {α β γ : Type*} {g : α → β} {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {l t s : ℕ → ℕ} (ht : Monotone t) (hs : Monotone s)
    (hl : ∀ a, (encMid (g a)).length ≤ l (encIn a).length)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f encMid encOut t s)
    (hg : ComputableTidilyInTimeAndSpaceOfLength g encIn encMid t s) :
    ∃ c, ComputableInTimeAndSpaceOfLength (f ∘ g) encIn encOut
      (fun n => t n + t (l n) + c * (l n + 1)) (fun n => s n + s (l n) + c * (l n + 1)) :=
  let ⟨c, h⟩ := comp ht hs hl hf hg
  ⟨c, ComputableTidilyInTimeAndSpace.computableInTimeAndSpace h⟩

end Turing.MultiTapeTM
