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

public noncomputable def inj_to_perm {k₁ k₂ : ℕ} (f : Fin k₁ → Fin k₂) (h_inj : f.Injective) :
  Equiv.Perm (Fin k₂) :=
  let f' : {i : Fin k₂ // i < k₁} → Fin k₂ := fun ⟨i, _⟩ => f ⟨i, by omega⟩
  have h_f'_inj : f'.Injective := by sorry
  (Equiv.ofInjective f' h_f'_inj).extendSubtype

/--
Change the order of the tapes of a Turing machine.
Example: For a 2-tape Turing machine tm,
`tm.with_tapes [2, 4].get (by grind)` is a 5-tape Turing machine whose tape 2 is
the original machine's tape 0 and whose tape 4 is the original
machine's tape 1
Note that `f` is a function to `Fin k₂`, which means that integer literals
automatically wrap. You have to be careful to make sure that the target machine
has the right amount of tapes.
-/
public noncomputable def MultiTapeTM.with_tapes {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
  (tm : MultiTapeTM k₁ α) (f : Fin k₁ → Fin k₂) (h_inj : f.Injective) : MultiTapeTM k₂ α :=
  (tm.extend h_le).permute_tapes (inj_to_perm f h_inj)

@[simp, grind=]
public theorem MultiTapeTM.with_tapes_eval
  {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂}
  {tm : MultiTapeTM k₁ α} {f : Fin k₁ → Fin k₂} {h_inj : f.Injective}
  {tapes : Fin k₂ → BiTape α} :
  (tm.with_tapes' f h_inj (h_le := h_le)).eval tapes =
    (tm.eval (tapes ∘ f)).map
      (fun tapes' => fun t => if h : ∃ i, f i = t then tapes' h.choose else tapes t) := by
  simp [with_tapes', inj_to_perm]
  sorry

end Turing
