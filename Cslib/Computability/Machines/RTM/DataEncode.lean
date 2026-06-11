/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Data
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.List.Basic

/-!
# Encodings into `Data`

This file defines the class that is used to encode arbitrary data structures into `Data`,
so that RTMs (rose tree machines) can operate on them.

Instances are provided for convenience for `Data` itself, `Bool`, `List α`, `Option α`, `α × β`,
and `ℕ` (binary encoding via `List Bool`)

-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-- Encoding of types into `Data`. -/
class DataEncode (α : Type) where
  encode : α → Data
  h_inj : encode.Injective

instance : DataEncode Data where
  encode b := b
  h_inj := by intros a b h_eq; grind

instance : DataEncode Bool where
  encode b := if b then Data.l [ Data.l [] ] else Data.l []
  h_inj := by intros a b h_eq; grind

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  h_inj := by
    intro a b h
    exact List.map_injective_iff.mpr DataEncode.h_inj (Data.l.inj h)

@[simp, scoped grind =]
lemma DataEncode_list_nil {α : Type} [DataEncode α] :
  DataEncode.encode ([] : List α) = Data.l [] := by
  simp [DataEncode.encode]

@[simp, scoped grind =]
lemma DataEncode_list_eq_nil_iff_nil {α : Type} [DataEncode α] (xs : List α) :
  DataEncode.encode xs = Data.empty ↔ xs = [] := by
  simp [DataEncode.encode]

@[simp, scoped grind =]
lemma DataEncode_list_tail {α : Type} [DataEncode α] (xs : List α) :
  (DataEncode.encode xs).asList.tail = (DataEncode.encode xs.tail).asList := by
  simp [DataEncode.encode]

instance (α : Type) [DataEncode α] : DataEncode (Option α) where
  encode := fun
    | none => Data.l []
    | some x => Data.l [DataEncode.encode x]
  h_inj := by
    intro a b h
    grind [DataEncode.h_inj]

@[simp]
lemma DataEncode_Option_empty {α : Type} [DataEncode α] (x : Option α) :
  (DataEncode.encode x == Data.empty) = x.isNone := by
  cases x <;> simp [DataEncode.encode, Data.empty]

instance (α β : Type) [DataEncode α] [DataEncode β] : DataEncode (α × β) where
  encode := fun (a, b) => Data.l [DataEncode.encode a, DataEncode.encode b]
  h_inj := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    grind [DataEncode.h_inj]

lemma DataEncode_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
  DataEncode.encode (a, b) = Data.l [DataEncode.encode a, DataEncode.encode b] := by
  simp [DataEncode.encode]

instance : DataEncode ℕ where
  encode x := DataEncode.encode (Nat.bits x)
  h_inj := by
    intro a b h
    have hb : a.bits = b.bits := DataEncode.h_inj h
    have hrec : ∀ n : ℕ, n.bits.foldr (fun b acc => Nat.bit b acc) 0 = n := by
      intro n
      induction n using Nat.binaryRec' with
      | zero => simp
      | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simp [ih]
    have := congrArg (List.foldr (fun b acc => Nat.bit b acc) 0) hb
    simpa [hrec] using this

end RoseTreeMachine

end Turing
