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
  decode : Data → Option α
  encodek : ∀ a, decode (encode a) = some a

instance : DataEncode Data where
  encode b := b
  decode b := some b
  encodek _ := rfl

instance : DataEncode Bool where
  encode b := if b then Data.l [ Data.l [] ] else Data.l []
  decode d := match d with
    | Data.l [ Data.l [] ] => some true
    | Data.l [ ] => some false
    | _ => none
  encodek _ := by grind

/-- `encode` is injective, derived from `encodek`. -/
lemma DataEncode.h_inj {α : Type} [DataEncode α] :
    Function.Injective (DataEncode.encode (α := α)) := by
  intro a b h
  have ha : DataEncode.decode (DataEncode.encode a) = some b := by
    rw [h]; exact DataEncode.encodek b
  rw [DataEncode.encodek] at ha
  exact Option.some.inj ha

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  decode d := d.asList.mapM DataEncode.decode
  encodek xs := by
    change (xs.map DataEncode.encode).mapM DataEncode.decode = some xs
    induction xs with
    | nil => rfl
    | cons h t ih => simp [List.mapM_cons, DataEncode.encodek, ih]

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
  decode := fun
    | Data.l [] => some none
    | Data.l [e] => (DataEncode.decode e).map some
    | _ => none
  encodek := fun a => by cases a <;> simp [DataEncode.encodek]

@[simp]
lemma DataEncode_Option_empty {α : Type} [DataEncode α] (x : Option α) :
  (DataEncode.encode x == Data.empty) = x.isNone := by
  cases x <;> simp [DataEncode.encode, Data.empty]

instance (α β : Type) [DataEncode α] [DataEncode β] : DataEncode (α × β) where
  encode := fun (a, b) => Data.l [DataEncode.encode a, DataEncode.encode b]
  decode := fun
    | Data.l [ea, eb] => match DataEncode.decode ea, DataEncode.decode eb with
        | some a, some b => some (a, b)
        | _, _ => none
    | _ => none
  encodek := fun (a, b) => by simp [DataEncode.encodek]

lemma DataEncode_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
  DataEncode.encode (a, b) = Data.l [DataEncode.encode a, DataEncode.encode b] := by
  simp [DataEncode.encode]

instance : DataEncode ℕ where
  encode x := DataEncode.encode (Nat.bits x)
  decode d := (DataEncode.decode d : Option (List Bool)).map
    (fun bits => bits.foldr (fun b acc => Nat.bit b acc) 0)
  encodek x := by
    have hrec : ∀ n : ℕ, n.bits.foldr (fun b acc => Nat.bit b acc) 0 = n := by
      intro n
      induction n using Nat.binaryRec' with
      | zero => simp
      | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simp [ih]
    change ((DataEncode.decode (DataEncode.encode (Nat.bits x)) :
      Option (List Bool)).map _) = some x
    rw [DataEncode.encodek]
    simp [hrec]

end RoseTreeMachine

end Turing
