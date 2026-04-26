/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

namespace Turing

public instance : Fintype Char := by
  have h_zero_valid : Nat.isValidChar 0 := by decide
  exact Fintype.ofSurjective
    (fun n : Fin 0x110000 =>
      if h : Nat.isValidChar n.val
      then (⟨⟨⟨n.val, by omega⟩⟩, h⟩ : Char)
      else (⟨⟨⟨0, by omega⟩⟩, h_zero_valid⟩ : Char))
    (fun c => by
      refine ⟨⟨c.val.toNat, ?_⟩, ?_⟩
      · have := c.valid; simp at this; omega
      · simp only [dif_pos c.valid]; ext; simp)

/-- Dyadic encoding of natural numbers. -/
@[expose]
public def dyadic (n : ℕ) : List Char :=
  if n = 0 then []
  else if Even n then
    dyadic (n / 2 - 1) ++ ['2']
  else
    dyadic ((n - 1) / 2) ++ ['1']

/-- Dyadic decoding of natural numbers. -/
@[expose]
public def dyadic_inv (l : List Char) : Option ℕ :=
  l.foldlM (fun acc c =>
    if c = '1' then some (2 * acc + 1)
    else if c = '2' then some (2 * acc + 2)
    else none) 0

@[simp, grind =]
public lemma dyadic_inv_zero : dyadic_inv [] = .some 0 := by
  unfold dyadic_inv; rfl

private lemma dyadic_inv_append_singleton (init : List Char) (c : Char) :
    dyadic_inv (init ++ [c]) =
      (dyadic_inv init).bind (fun acc =>
        if c = '1' then some (2 * acc + 1)
        else if c = '2' then some (2 * acc + 2) else none) := by
  simp [dyadic_inv, List.foldlM_append]

/-- `dyadic` is a right-inverse to `dyadic_inv` on lists of `'1'` and `'2'`. -/
public lemma dyadic_dyadic_inv (l : List Char) (n : ℕ)
    (h_chars : ∀ c ∈ l, c = '1' ∨ c = '2')
    (h : dyadic_inv l = some n) : dyadic n = l := by
  induction l using List.reverseRecOn generalizing n with
  | nil =>
    simp [dyadic_inv] at h; subst h
    simp [dyadic]
  | append_singleton init c ih =>
    have h_c : c = '1' ∨ c = '2' := h_chars c (by simp)
    have h_init_chars : ∀ d ∈ init, d = '1' ∨ d = '2' := fun d hd =>
      h_chars d (List.mem_append.mpr (Or.inl hd))
    rw [dyadic_inv_append_singleton] at h
    obtain ⟨m, hm, hstep⟩ := Option.bind_eq_some_iff.mp h
    have hd_init : dyadic m = init := ih m h_init_chars hm
    rcases h_c with rfl | rfl
    · -- c = '1' case: n = 2 * m + 1
      simp only [if_true, Option.some.injEq] at hstep
      subst hstep
      have h_odd : ¬ Even (2 * m + 1) := by
        rw [Nat.not_even_iff_odd]; exact ⟨m, by omega⟩
      have h_nz : 2 * m + 1 ≠ 0 := by omega
      conv_lhs => rw [dyadic]
      simp only [if_neg h_nz, if_neg h_odd]
      rw [show (2 * m + 1 - 1) / 2 = m by omega, hd_init]
    · -- c = '2' case: n = 2 * m + 2
      have h21 : ('2' : Char) ≠ '1' := by decide
      simp only [if_neg h21, if_true, Option.some.injEq] at hstep
      subst hstep
      have h_even : Even (2 * m + 2) := ⟨m + 1, by omega⟩
      have h_nz : 2 * m + 2 ≠ 0 := by omega
      conv_lhs => rw [dyadic]
      simp only [if_neg h_nz, if_pos h_even]
      rw [show (2 * m + 2) / 2 - 1 = m by omega, hd_init]

@[simp, grind =]
public lemma dyadic_inv_dyadic (n : ℕ) : dyadic_inv (dyadic n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold dyadic
    split
    · subst_vars; simp [dyadic_inv]
    · next h_nz =>
      split <;> rename_i h_parity <;>
        simp only [dyadic_inv, List.foldlM_append, Option.bind_eq_bind] <;>
        rw [show List.foldlM _ 0 _ = dyadic_inv (dyadic _) from rfl,
            ih _ (by omega)] <;>
        simp
      · obtain ⟨m, hm⟩ := h_parity; omega
      · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp h_parity; omega

public lemma dyadic_mem_chars {c : Char} {n : ℕ} (h : c ∈ dyadic n) :
    c = '1' ∨ c = '2' := by
  induction n using Nat.strongRecOn with
  | _ n ih => grind [dyadic]

end Turing
