/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Part
public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic.DeriveFintype
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

open Cslib Relation

namespace Complexity

structure Result where
  output : ℕ
  time : ℕ
  space : ℕ

class MachineModel (Machine : Type*) where
  run (m : Machine) (x : ℕ) : Part Result

namespace MachineModel

variable {Machine : Type*} [MachineModel Machine]

def TimeAndSpaceComputable (Machine : Type*) [MachineModel Machine] (f t s : ℕ → ℕ) : Prop :=
  -- TODO we should split the optimal space and the optimal time machine.
  ∃ (m : Machine) (a : ℕ), ∀ x, ∃ t' s',
    run m x = Part.some ⟨f x, t', s'⟩ ∧
    t' ≤ a * t x.log2 + a ∧
    s' ≤ a * s x.log2 + a

local notation "ComplexityOf" => TimeAndSpaceComputable Machine

structure SaneModel where
  h_id : ComplexityOf id id 0 -- TODO could also make identitiy linear.
  h_comp : ∀ f g t₁ t₂ s₁ s₂, ComplexityOf f t₁ s₁ → ComplexityOf g t₂ s₂ →
      ComplexityOf (g ∘ f)
      (t₁ + t₂)
      -- TODO + or max is the same.
      (fun n => (s₁ n) + (s₂ (t₁ n)) + (t₁ n).log2)
  pairing : ℕ → ℕ → ℕ
  fst : ℕ → ℕ
  snd : ℕ → ℕ
  h_pairing₁ : ∀ x, pairing (fst x) (snd x) = x
  h_pairing₂ : ∀ x y, fst (pairing x y) = x
  h_pairing₃ : ∀ x y, snd (pairing x y) = y
  h_pairingC : ∀ f g, ComplexityOf f t₁ s₁ → ComplexityOf g t₂ s₂ →
      ComplexityOf (fun x => pairing (f x) (g x))
      (fun n => t₁ n + t₂ n)
      (fun n => max (s₁ n) (s₂ n))
  h_fstC : ComplexityOf fst id 0
  h_sndC : ComplexityOf snd id 0
  h_constant : ∀ c, ComplexityOf (fun _ => c) id 0
  h_add : ComplexityOf (fun x => fst x + snd x) id Nat.log2
  h_mul : ComplexityOf (fun x => fst x * snd x) (fun n => n ^ 2) Nat.log2

open Classical in
noncomputable def simulation (m : Machine) (input steps : ℕ) : ℕ × ℕ × ℕ :=
  if h : (run m input).Dom then
    let r := (run m input).get h
    if r.time ≤ steps then
      (1, r.output, r.space)
    else
      (0, 0, 0)
  else
    (0, 0, 0)

structure EfficientUniversalEnumeration (Machine) [MachineModel Machine] where
  model : SaneModel (Machine := Machine)
  /-- An enumeration of machines. -/
  machines : ℕ → Machine
  /-- Every machine appears infinitely often in the enumeration. -/
  h_surj : ∀ (m : Machine) n, ∃ n' ≥ n, machines n' = m
  /-- There is a universal machine. -/
  univ : Machine
  h_univ : ComplexityOf
    (fun x =>
      let machine := model.fst x
      let input := model.fst (model.snd x)
      let steps := model.snd (model.snd x)
      let (halt, out, space) := simulation (machines machine) input steps
      pairing halt (pairing out space))

-- TODO now we need to state that the time is `t log t` in steps plus a factor
-- that depends on the machine, i.e. the machine size should not go into the
-- log, but this is not really possible with our current model.

end Complexity
