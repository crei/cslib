/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeExtension

public import Mathlib.Logic.Equiv.Fintype

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

variable [Inhabited α] [Fintype α]

variable {k : ℕ}

--- Permute tapes according to a bijection
public def MultiTapeTM.permute_tapes
  (tm : MultiTapeTM k α) (σ : Equiv.Perm (Fin k)) : MultiTapeTM k α where
  Λ := tm.Λ
  q₀ := tm.q₀
  M := fun q syms => match tm.M q (syms ∘ σ) with
    | (stmts, q') => (stmts ∘ σ.symm, q')

--- General theorem: permuting tapes commutes with evaluation
@[simp, grind =]
public theorem MultiTapeTM.permute_tapes_eval
  (tm : MultiTapeTM k α) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → BiTape α) :
  (tm.permute_tapes σ).eval tapes =
    (tm.eval (tapes ∘ σ)).map (fun tapes' => tapes' ∘ σ.symm) := by
  sorry

/--
Change the order of the tapes of a Turing machine.
Example: For a 2-tape Turing machine tm,
tm.with_tapes [2, 4] is a 5-tape Turing machine whose tape 2 is
the original machine's tape 0 and whose tape 4 is the original
machine's tape 1
Note that `seq` should not have repetitions.
TODO maybe `seq` should be an injection from Fin k₁ to Fin k₂, then it would be `#v[2, 4].get`.
-/
public def MultiTapeTM.with_tapes {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
  (tm : MultiTapeTM k₁ α) (seq : Vector (Fin k₂) k₁) : MultiTapeTM k₂ α :=
  (seq.mapFinIdx fun i t _ => ((⟨i, by omega⟩ : Fin k₂), t)
    ).foldl (fun tm (a, b) => tm.permute_tapes (Equiv.swap a b)) (tm.extend h_le)

--- Semantics of tm.with_tapes when tm is a 1-tape Turing machine.
@[simp, grind =]
public theorem MultiTapeTM.with_tapes_eval_1
  {j : Fin k.succ}
  (tm : MultiTapeTM 1 α)
  (tapes : Fin k.succ → BiTape α) :
  (tm.with_tapes #v[j] (h_le := by omega)).eval tapes =
    (tm.eval (fun _ => tapes j)).map
    (fun tapes' t => if t = j then tapes' 0 else tapes t) := by
  unfold MultiTapeTM.with_tapes
  have h_tapes :
    ((fun tapes'' : Fin k.succ → BiTape α => tapes'' ∘ Equiv.swap 0 j) ∘
    (fun (tapes'' : Fin 1 → BiTape α) i =>
      if h : i = 0 then tapes'' ⟨i, by simp [h]⟩ else tapes (Equiv.swap 0 j i))) =
    fun tapes' => (fun t => if t = j then tapes' 0 else tapes t) := by
    grind
  simp [Part.map_map, h_tapes]

public noncomputable def inj_to_perm {k₁ k₂ : ℕ} (f : Fin k₁ → Fin k₂) (h_inj : f.Injective) :
  Equiv.Perm (Fin k₂) :=
  let f' : {i : Fin k₂ // i < k₁} → Fin k₂ := fun ⟨i, _⟩ => f ⟨i, by omega⟩
  have h_f'_inj : f'.Injective := by sorry
  (Equiv.ofInjective f' h_f'_inj).extendSubtype

--- This is a different version of `with_tapes` that uses an injection instead of
--- a generic list. The hope is that it is easier to prove a theorem about `eval` using this.
public noncomputable def MultiTapeTM.with_tapes' {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
  (tm : MultiTapeTM k₁ α) (f : Fin k₁ → Fin k₂) (h_inj : f.Injective) : MultiTapeTM k₂ α :=
  (tm.extend h_le).permute_tapes (inj_to_perm f h_inj)

public theorem MultiTapeTM.with_tapes'_eval
  {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
  (tm : MultiTapeTM k₁ α) (f : Fin k₁ → Fin k₂) {h_inj : f.Injective}
  (tapes : Fin k₂ → BiTape α) :
  (tm.with_tapes' f h_inj (h_le := h_le)).eval tapes =
    (tm.eval (tapes ∘ f)).map
      (fun tapes' => fun t => if h : ∃ i, f i = t then tapes' h.choose else tapes t) := by
  simp [with_tapes', inj_to_perm]
  sorry

-- TODO continue here: This seems to work fine for copy, as long as we do not have
-- any preconditions.
-- Try to extend this to "loop" and "add" (also try to remove the preconditions).

end Turing
