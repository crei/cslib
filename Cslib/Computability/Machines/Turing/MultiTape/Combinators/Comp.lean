/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Adapters

/-!
# Complexity of function composition

If `f` and `gg` are computable in time and space, then so is `gg ∘ f`. The two function machines are
placed by the general tape-transformer adapters on a shared work-tape layout — `f` reads the real
input and writes a scratch tape, `gg` reads that tape and writes another — and the result is emitted
as the output. All the tape bookkeeping is hidden inside the adapters, so the proof only has to name
the single handoff tape between the two machines.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_comp`: the complexity of `gg ∘ f`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type*}

/-- **Complexity of a composition.** If `f` and `gg` are computable, so is `gg ∘ f`. The two
function machines are placed by the general adapters on a shared layout: `f` reads the real input
and writes tape `o1`, `gg` reads `o1` and writes tape `o`, and the result is emitted from `o`. All
the tape bookkeeping is hidden inside `exists_transformsTapes_ofComputable{,Input}`; here only the
handoff `o1` between the two machines and the final emit remain. -/
public theorem computableInTimeAndSpace_comp
    {f : α → β} {gg : β → γ} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {tf sf : α → ℕ} {tg sg : β → ℕ}
    (hf : ComputableInTimeAndSpace f encA encB tf sf)
    (hg : ComputableInTimeAndSpace gg encB encC tg sg) :
    ∃ c, ComputableInTimeAndSpace (gg ∘ f) encA encC
      (fun a => c * (tf a + tg (f a) + (encB (f a)).length + 1))
      (fun a => c * (sf a + sg (f a) + (encB (f a)).length + (encC (gg (f a))).length + 1)) := by
  classical
  -- `f` reads the real input and leaves `encB (f a)` on tape `o1`; `gg` reads `o1` and leaves
  -- `encC (gg x)` on tape `o`. The general adapters hide their scratch tapes.
  obtain ⟨m_f, c_f, hf'⟩ := exists_transformsTapes_ofComputableInput hf
  obtain ⟨m_g, c_g, hg'⟩ := exists_transformsTapes_ofComputable hg
  set k := m_f + m_g + 2 with hk
  let o1 : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  have ho1o : o1 ≠ o := by
    apply Fin.ne_of_val_ne; simp
  obtain ⟨S_f, hS_f, M_f, hM_f⟩ :=
    hf' k o1 ∅ (by simp) (by simp only [Finset.card_empty]; omega)
  obtain ⟨S_g, hS_g, M_g, hM_g⟩ :=
    hg' k o1 o ∅ ho1o (by simp) (by simp) (by simp only [Finset.card_empty]; omega)
  have hfin_f := hS_f
  have hfin_g := hS_g
  -- The composite tape transformer: run `M_f`, then `M_g` reading `M_f`'s output tape `o1`.
  have hMc : ∀ a, TransformsTapes (M_f.seq M_g)
      (fun input ws => input = encA a ∧ ∀ l, ws l = [])
      (fun _ _ ws' => ws' o = encC (gg (f a)))
      (c_f * (tf a + 1) + c_g * (tg (f a) + 1))
      ((c_f * (sf a + (encB (f a)).length + 1) + k) +
        (c_g * (sg (f a) + (encB (f a)).length + (encC (gg (f a))).length + 1) + k)) := by
    intro a
    refine (transformsTapes_seq (h₀ := hM_f a) (h₁ := hM_g (f a)) ?_).imp ?_ ?_ le_rfl le_rfl
    · -- handoff: after `M_f`, `M_g`'s precondition holds on tape `o1`
      rintro input ws ws' ⟨rfl, hblank⟩ hQf
      refine ⟨?_, ?_⟩
      · rw [hQf, Function.update_self]
      · intro l hl _
        rw [hQf, Function.update_of_ne hl]
        exact hblank l (by simp)
    · -- precondition: an all-blank input satisfies `M_f`'s (empty-`keep`) precondition
      rintro input ws ⟨rfl, hblank⟩
      exact ⟨rfl, fun l _ => hblank l⟩
    · -- postcondition: read the result off `M_g`'s output tape `o`
      rintro input ws ws'' _ ⟨ws', _, hQg⟩
      rw [hQg, Function.update_self]
  -- Emit tape `o` as the real output, turning the transformer into a computation.
  obtain ⟨c, hc⟩ :=
    computableInTimeAndSpace_of_transformsTapes (gg := gg ∘ f) o hMc
  -- Relax the bounds to the stated linear form.
  refine ⟨c * (c_f + c_g + 2 * k + 2), hc.mono (fun a => ?_) (fun a => ?_)⟩
  · -- Time.
    have hlc : (encC (gg (f a))).length ≤ tg (f a) := hg.length_encOut_le (f a)
    set T := tf a + tg (f a) + (encB (f a)).length + 1 with hT
    have e1 : c_f * (tf a + 1) ≤ c_f * T := Nat.mul_le_mul_left _ (by omega)
    have e2 : c_g * (tg (f a) + 1) ≤ c_g * T := Nat.mul_le_mul_left _ (by omega)
    have hexp : (c_f + c_g + 2 * k + 2) * T =
        c_f * T + c_g * T + 2 * k * T + 2 * T := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    have e4 : (encC (gg (f a))).length + 1 ≤ 2 * T := by omega
    have hmul : c * (c_f * (tf a + 1) + c_g * (tg (f a) + 1) + (encC (gg (f a))).length + 1)
        ≤ c * ((c_f + c_g + 2 * k + 2) * T) := Nat.mul_le_mul_left _ (by omega)
    calc c * (c_f * (tf a + 1) + c_g * (tg (f a) + 1) + (encC (gg (f a))).length + 1)
        ≤ c * ((c_f + c_g + 2 * k + 2) * T) := hmul
      _ = c * (c_f + c_g + 2 * k + 2) * T := (Nat.mul_assoc _ _ _).symm
  · -- Space.
    set PS := sf a + sg (f a) + (encB (f a)).length + (encC (gg (f a))).length + 1 with hPS
    have f1 : c_f * (sf a + (encB (f a)).length + 1) ≤ c_f * PS :=
      Nat.mul_le_mul_left _ (by omega)
    have f2 : c_g * (sg (f a) + (encB (f a)).length + (encC (gg (f a))).length + 1) ≤ c_g * PS :=
      Nat.mul_le_mul_left _ (by omega)
    have q1 : 2 * k ≤ 2 * k * PS := Nat.le_mul_of_pos_right _ (by omega)
    have e4 : (encC (gg (f a))).length + 1 ≤ 2 * PS := by omega
    have hexpS : (c_f + c_g + 2 * k + 2) * PS =
        c_f * PS + c_g * PS + 2 * k * PS + 2 * PS := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    have hmul : c * ((c_f * (sf a + (encB (f a)).length + 1) + k) +
          (c_g * (sg (f a) + (encB (f a)).length + (encC (gg (f a))).length + 1) + k) +
          (encC (gg (f a))).length + 1)
        ≤ c * ((c_f + c_g + 2 * k + 2) * PS) := Nat.mul_le_mul_left _ (by omega)
    calc c * ((c_f * (sf a + (encB (f a)).length + 1) + k) +
          (c_g * (sg (f a) + (encB (f a)).length + (encC (gg (f a))).length + 1) + k) +
          (encC (gg (f a))).length + 1)
        ≤ c * ((c_f + c_g + 2 * k + 2) * PS) := hmul
      _ = c * (c_f + c_g + 2 * k + 2) * PS := (Nat.mul_assoc _ _ _).symm


end Turing.MultiTapeTM
