/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Data
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Sign.Defs

/-!
# Encoding Lean types into rose trees

`DataEncode α` injects `α` into `Data`; the instances are compositional, so the encoded size of a
structured value decomposes into the sizes of its parts. Those decomposition lemmas are what every
complexity proof downstream reasons with — nothing after this file should need to unfold
`DataEncode.encode` or `Data.size` again.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

/-! ## 2. Encoding Lean types into rose trees -/

/-- An encoding of the type `α` into rose trees.

Injectivity is required, but no decoding function and no round-trip property: a machine is always
handed the encoding of an actual value of `α` (see the discussion of
`DataComputableInTimeAndSpace`).

The `depth` bound is **not** cosmetic. The structural primitives — `Bounds.fst`, `Bounds.snd`,
`Bounds.headD`, `Bounds.tail` — claim to use *no work tape at all*. Each of them has to skip over a
subtree to find its matching close bracket, which a machine does by scanning while counting
nesting depth. That counter is free only if the depth it can reach is bounded by a constant of the
type; if encodings could be arbitrarily deep the counter would grow with the input and those
`space := 0` claims would be false.

This is exactly why there is no `DataEncode Data` instance: encoding `Data` as itself admits trees
of unbounded depth, so it would silently invalidate every primitive. Every instance below is
shallow — a list of `α` is one level deeper than `α`, and so on. -/
class DataEncode (α : Type) where
  /-- The encoding function. -/
  encode : α → Data
  /-- Distinct values have distinct encodings. -/
  h_inj : Function.Injective encode
  /-- A bound on the nesting depth of encodings, depending on `α` alone. -/
  depth : ℕ
  /-- Encodings really are that shallow. -/
  h_depth : ∀ a, (encode a).depth ≤ depth

instance : DataEncode Bool where
  encode b := if b then Data.l [Data.l []] else Data.l []
  h_inj := by intro a b h; cases a <;> cases b <;> simp_all
  depth := 2
  h_depth b := by
    cases b
    · change (Data.l ([] : List Data)).depth ≤ 2
      simp [Data.depth]
    · change (Data.l [Data.l []]).depth ≤ 2
      simp [Data.depth]

instance : DataEncode Unit where
  encode _ := Data.l []
  h_inj := fun a b _ => Subsingleton.elim a b
  depth := 1
  h_depth _ := by
    simp [Data.depth]

@[simp]
lemma DataEncode.size_unit (u : Unit) : (DataEncode.encode u).size = 2 := by
  cases u
  change (Data.l []).size = 2
  simp [Data.size]

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  h_inj := by
    intro a b h
    exact List.map_injective_iff.mpr DataEncode.h_inj (Data.l.inj h)
  depth := 1 + DataEncode.depth (α := α)
  h_depth xs := by
    rw [Data.depth, List.map_map]
    have := foldr_max_le xs (Data.depth ∘ DataEncode.encode) (DataEncode.depth (α := α))
      (fun x _ => DataEncode.h_depth x)
    omega

instance (α β : Type) [DataEncode α] [DataEncode β] : DataEncode (α × β) where
  encode := fun (a, b) => Data.l [DataEncode.encode a, DataEncode.encode b]
  h_inj := by
    intro p q h
    obtain ⟨a₁, b₁⟩ := p
    obtain ⟨a₂, b₂⟩ := q
    simp only [Data.l.injEq, List.cons.injEq, and_true] at h
    simp [DataEncode.h_inj h.1, DataEncode.h_inj h.2]
  depth := 1 + max (DataEncode.depth (α := α)) (DataEncode.depth (α := β))
  h_depth p := by
    obtain ⟨a, b⟩ := p
    change (Data.l [DataEncode.encode a, DataEncode.encode b]).depth ≤ _
    have h1 := DataEncode.h_depth a
    have h2 := DataEncode.h_depth b
    rw [Data.depth]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega

instance (α : Type) [DataEncode α] : DataEncode (Option α) where
  encode
    | none => Data.l []
    | some x => Data.l [DataEncode.encode x]
  h_inj := by
    intro a b h
    cases a <;> cases b <;> simp_all [DataEncode.h_inj.eq_iff]
  depth := 1 + DataEncode.depth (α := α)
  h_depth o := by
    cases o with
    | none =>
      change (Data.l ([] : List Data)).depth ≤ _
      simp [Data.depth]
    | some x =>
      change (Data.l [DataEncode.encode x]).depth ≤ _
      have := DataEncode.h_depth x
      rw [Data.depth]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      omega

/-- One node per bit of a natural number.

The two bit values are deliberately encoded by *different trees of the same size*, so that
`(DataEncode.encode n).size` depends only on the number of bits of `n` and is therefore
**monotone in `n`** (`DataEncode.size_nat_mono`). Routing `ℕ` through `DataEncode (List Bool)`
instead would not be monotone, because `encode true` and `encode false` have different sizes:
`(encode 7).size > (encode 8).size`, which makes every size-bookkeeping argument about counters
unnecessarily painful. The price is a constant factor, which none of the statements here can
observe. -/
def Data.ofBit (b : Bool) : Data :=
  if b then Data.l [Data.l [], Data.l []] else Data.l [Data.l [Data.l []]]

@[simp]
lemma Data.size_ofBit (b : Bool) : (Data.ofBit b).size = 6 := by
  cases b <;> simp [Data.ofBit, Data.size]

/-- Read a little-endian bit list back as a natural number. This is a left inverse of
`Nat.bits` (`natOfBits_bits`), which is what makes `Nat.bits` injective, and it is the
"read the answer off the tape" step of the arithmetic examples. -/
def natOfBits (bs : List Bool) : ℕ := bs.foldr (fun b acc => Nat.bit b acc) 0

@[simp]
lemma natOfBits_nil : natOfBits [] = 0 := rfl

@[simp]
lemma natOfBits_cons (b : Bool) (bs : List Bool) :
    natOfBits (b :: bs) = Nat.bit b (natOfBits bs) := rfl

/-- `Nat.bit` in arithmetic form. -/
lemma natBit_eq_two_mul_add (b : Bool) (n : ℕ) :
    Nat.bit b n = 2 * n + cond b 1 0 := by
  cases b <;> simp [Nat.bit]

/-- Appending trailing zeros does not change the value of a bit list. -/
@[simp]
lemma natOfBits_append_replicate_false (bs : List Bool) (k : ℕ) :
    natOfBits (bs ++ List.replicate k false) = natOfBits bs := by
  induction bs with
  | nil =>
    simp only [List.nil_append]
    induction k with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, ih, natBit_eq_two_mul_add]
  | cons b bs ih => simp [ih]

/-- A bit list of length `k` denotes a number below `2 ^ k`. -/
lemma natOfBits_lt (bs : List Bool) : natOfBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [natOfBits_cons, natBit_eq_two_mul_add, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- Multiplying adds at most the two bit lengths. -/
lemma natSize_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

/-- A power of two has bit length one more than its exponent. -/
lemma natSize_two_pow_le (j : ℕ) : (2 ^ j).size ≤ j + 1 := by
  rw [Nat.size_le]
  exact Nat.pow_lt_pow_right (by omega) (by omega)

/-- `natOfBits` is a left inverse of `Nat.bits`. -/
lemma natOfBits_bits (n : ℕ) : natOfBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simp [ih]

lemma Data.ofBit_injective : Function.Injective Data.ofBit := by
  intro x y h
  cases x <;> cases y <;> simp_all [Data.ofBit]

instance : DataEncode ℕ where
  encode n := Data.l (n.bits.map Data.ofBit)
  h_inj := by
    intro a b h
    have hb : a.bits = b.bits :=
      List.map_injective_iff.mpr Data.ofBit_injective (Data.l.inj h)
    -- `Nat.bits` has a left inverse (`natOfBits`), hence is injective.
    rw [← natOfBits_bits a, ← natOfBits_bits b, hb]
  depth := 4
  h_depth n := by
    rw [Data.depth, List.map_map]
    have hb : ∀ b : Bool, (Data.depth ∘ Data.ofBit) b ≤ 3 := by
      intro b
      cases b <;> simp [Data.ofBit, Data.depth]
    have := foldr_max_le n.bits (Data.depth ∘ Data.ofBit) 3 (fun b _ => hb b)
    omega

instance (n : ℕ) : DataEncode (Fin n) where
  encode i := DataEncode.encode i.val
  h_inj := fun _ _ h => Fin.ext (DataEncode.h_inj h)
  depth := DataEncode.depth (α := ℕ)
  h_depth i := DataEncode.h_depth i.val

/-- The three head movements of a `MultiTapeTM`, as `none` / `some false` / `some true`. -/
def signToOptBool : SignType → Option Bool
  | .zero => none
  | .neg => some false
  | .pos => some true

lemma signToOptBool_injective : Function.Injective signToOptBool := by
  intro a b h
  cases a <;> cases b <;> simp_all [signToOptBool]

instance : DataEncode SignType where
  encode m := DataEncode.encode (signToOptBool m)
  h_inj := fun _ _ h => signToOptBool_injective (DataEncode.h_inj h)
  depth := DataEncode.depth (α := Option Bool)
  h_depth m := DataEncode.h_depth (signToOptBool m)

/-! ### Encoded sizes

The size lemmas below are what complexity proofs actually reason with; nothing downstream should
need to unfold `DataEncode.encode` or `Data.size` again.
-/

/-- The encoded size of a list is two (for the node itself) plus the encoded sizes of its
elements. -/
lemma DataEncode.size_list {α : Type} [DataEncode α] (xs : List α) :
    (DataEncode.encode xs).size = 2 + (xs.map fun x => (DataEncode.encode x).size).sum := by
  change (Data.l (xs.map DataEncode.encode)).size = _
  simp [Data.size, List.map_map, Function.comp_def]

/-- The encoded size of a pair is the sum of the encoded sizes plus the two parentheses of the
pair node itself. This is the size at which the bounds of `step` have to be evaluated. -/
lemma DataEncode.size_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
    (DataEncode.encode (a, b)).size =
      (DataEncode.encode a).size + (DataEncode.encode b).size + 2 := by
  change (Data.l [DataEncode.encode a, DataEncode.encode b]).size = _
  simp [Data.size]
  omega

/-- A cons cell costs exactly the sum of its parts: the list node's own two cells are already
paid for by the encoding of the tail. Equivalently, it is two cells cheaper than the pair
`(x, xs)` it is built from — consing deletes one bracket. -/
lemma DataEncode.size_cons {α : Type} [DataEncode α] (x : α) (xs : List α) :
    (DataEncode.encode (x :: xs)).size
      = (DataEncode.encode x).size + (DataEncode.encode xs).size := by
  rw [DataEncode.size_list, DataEncode.size_list]
  simp only [List.map_cons, List.sum_cons]
  omega

@[simp]
lemma DataEncode.size_nil {α : Type} [DataEncode α] :
    (DataEncode.encode ([] : List α)).size = 2 := by
  change (Data.l []).size = 2
  simp [Data.size]

@[simp]
lemma DataEncode.size_none {α : Type} [DataEncode α] :
    (DataEncode.encode (none : Option α)).size = 2 := by
  change (Data.l []).size = 2
  simp [Data.size]

@[simp]
lemma DataEncode.size_some {α : Type} [DataEncode α] (x : α) :
    (DataEncode.encode (some x)).size = (DataEncode.encode x).size + 2 := by
  change (Data.l [DataEncode.encode x]).size = _
  simp [Data.size]
  omega

/-- Dropping the head never grows the encoding. -/
lemma DataEncode.size_tail_le {α : Type} [DataEncode α] (xs : List α) :
    (DataEncode.encode xs.tail).size ≤ (DataEncode.encode xs).size := by
  cases xs with
  | nil => simp
  | cons x xs =>
    have h := DataEncode.size_cons x xs
    have h2 := Data.two_le_size (DataEncode.encode x)
    simpa using by omega

/-- Every element of a list is a subtree of the encoding of that list, so its encoded size is
bounded by the encoded size of the list. -/
lemma DataEncode.size_mem_le {α : Type} [DataEncode α] {xs : List α} {x : α} (h : x ∈ xs) :
    (DataEncode.encode x).size ≤ (DataEncode.encode xs).size := by
  have hle : (DataEncode.encode x).size ≤ (xs.map fun y => (DataEncode.encode y).size).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem h)
  rw [DataEncode.size_list]
  omega

/-- Every element of a list contributes at least two to the encoded size of the list, so the
length of a list is bounded by its encoded size. This is what bounds the number of iterations
of a fold. -/
lemma DataEncode.length_le_size {α : Type} [DataEncode α] (xs : List α) :
    xs.length ≤ (DataEncode.encode xs).size := by
  have h := le_sum_map xs (fun x => (DataEncode.encode x).size) 2
    (fun x _ => Data.two_le_size _)
  rw [DataEncode.size_list]
  omega

/-- A uniform bound on the encoded sizes of the elements bounds the encoded size of the list. -/
lemma DataEncode.size_list_le {α : Type} [DataEncode α] (xs : List α) (b : ℕ)
    (h : ∀ x ∈ xs, (DataEncode.encode x).size ≤ b) :
    (DataEncode.encode xs).size ≤ 2 + b * xs.length := by
  have := sum_map_le xs (fun x => (DataEncode.encode x).size) b h
  rw [DataEncode.size_list]
  omega

@[simp]
lemma DataEncode.size_bool (b : Bool) : (DataEncode.encode b).size ≤ 4 := by
  cases b <;> change (Data.l _).size ≤ 4 <;> simp [Data.size]

/-- A bit list occupies at most `2 + 4 * length` cells. -/
lemma DataEncode.size_bits_le (bs : List Bool) :
    (DataEncode.encode bs).size ≤ 2 + 4 * bs.length :=
  DataEncode.size_list_le bs 4 (fun b _ => DataEncode.size_bool b)

/-- The encoded size of a natural number is determined by its bit length. -/
lemma DataEncode.size_nat (n : ℕ) : (DataEncode.encode n).size = 2 + 6 * n.size := by
  have hsz : (Data.l (n.bits.map Data.ofBit)).size
      = 2 + ((n.bits.map Data.ofBit).map Data.size).sum := by
    simp [Data.size]
  change (Data.l (n.bits.map Data.ofBit)).size = _
  rw [hsz, List.map_map,
    sum_map_const n.bits (Data.size ∘ Data.ofBit) 6 (fun b => Data.size_ofBit b),
    Nat.size_eq_bits_len]

/-- The bit length of a natural number is bounded by its encoded size. -/
lemma DataEncode.bits_length_le (n : ℕ) : n.bits.length ≤ (DataEncode.encode n).size := by
  rw [DataEncode.size_nat, Nat.size_eq_bits_len]
  omega

/-- The encoded size of a natural number is monotone. This is the whole point of `Data.ofBit`. -/
lemma DataEncode.size_nat_mono {m n : ℕ} (h : m ≤ n) :
    (DataEncode.encode m).size ≤ (DataEncode.encode n).size := by
  have := Nat.size_le_size h
  rw [DataEncode.size_nat, DataEncode.size_nat]
  omega

private lemma natSize_succ_le (i : ℕ) : (i + 1).size ≤ i.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have h : i < 2 ^ i.size := Nat.lt_size_self i
  have h2 : 0 < 2 ^ i.size := Nat.two_pow_pos i.size
  generalize 2 ^ i.size = X at h h2 ⊢
  omega

/-- Incrementing a natural number costs at most one extra node in the encoding. -/
lemma DataEncode.size_nat_succ (i : ℕ) :
    (DataEncode.encode (i + 1)).size ≤ (DataEncode.encode i).size + 6 := by
  have := natSize_succ_le i
  rw [DataEncode.size_nat, DataEncode.size_nat]
  omega

end RoseTreeMachine

end Turing
