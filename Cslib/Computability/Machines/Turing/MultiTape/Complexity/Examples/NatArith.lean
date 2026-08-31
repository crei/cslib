/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold

/-!
# Examples: `Nat.succ` and `Nat.add`

Both are folds over `Nat.bits`, which is little-endian, so `List.foldl` visits the least
significant bit first — exactly the order carry propagation needs. Both produce a bit list and read
it back with `natOfBits`, which avoids having to prove that the output is canonical.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

/-- Flush a pending carry onto the emitted bits and read them back as a number. Shared by the
two arithmetic examples: both fold a carry along the bits and finish the same way. -/
def flushCarry (acc : Bool × List Bool) : ℕ :=
  natOfBits (acc.2 ++ cond acc.1 [true] [])

/-! ## 2. `Nat.succ`

Incrementing a binary numeral is carry propagation, and `Nat.bits` is little-endian, so
`List.foldl` over it visits the bits in exactly the order the carry travels.

The accumulator is the pending carry together with the output bits emitted so far. The step is the
half adder `(c, out) b ↦ (c && b, out ++ [c ^^ b])`; at the end `flushCarry` flushes a surviving
carry and reads the bits back as a number.
-/

namespace NatSucc

/-- The list the increment folds over: the bits of the input, least significant first. -/
def succList (n : ℕ) : List Bool := n.bits

/-- The initial accumulator: carry one, nothing emitted yet. -/
def succInit (_ : ℕ) : Bool × List Bool := (true, [])

/-- Half adder: emit `c ^^ b` and carry `c && b`. -/
def succStep (acc : Bool × List Bool) (b : Bool) : Bool × List Bool :=
  (acc.1 && b, acc.2 ++ [Bool.xor acc.1 b])

/-- Closed form of the increment: the outgoing carry together with the emitted bits. -/
def incSpec (c : Bool) : List Bool → Bool × List Bool
  | [] => (c, [])
  | b :: bs =>
    let r := incSpec (c && b) bs
    (r.1, Bool.xor c b :: r.2)

lemma foldl_succStep (bs : List Bool) (c : Bool) (out : List Bool) :
    bs.foldl succStep (c, out) = ((incSpec c bs).1, out ++ (incSpec c bs).2) := by
  induction bs generalizing c out with
  | nil => simp [incSpec]
  | cons b bs ih => simp [succStep, incSpec, ih]

lemma incSpec_length (c : Bool) (bs : List Bool) : (incSpec c bs).2.length = bs.length := by
  induction bs generalizing c with
  | nil => simp [incSpec]
  | cons b bs ih => simp [incSpec, ih]

/-- **The carry fold is correct**: flushing the carry yields the value plus the incoming carry. -/
lemma natOfBits_incSpec (c : Bool) (bs : List Bool) :
    natOfBits ((incSpec c bs).2 ++ cond (incSpec c bs).1 [true] [])
      = natOfBits bs + cond c 1 0 := by
  induction bs generalizing c with
  | nil => cases c <;> simp [incSpec, Nat.bit_eq_two_mul_add]
  | cons b bs ih =>
    have h := ih (c && b)
    simp only [incSpec, List.cons_append, natOfBits_cons, Nat.bit_eq_two_mul_add]
    rw [h]
    cases c <;> cases b
    all_goals simp
    all_goals omega

/-- **The fold computes `Nat.succ`.** -/
lemma flushCarry_foldFun (n : ℕ) :
    flushCarry (foldFun succList succInit succStep n) = n + 1 := by
  have hf : foldFun succList succInit succStep n = n.bits.foldl succStep (true, []) := rfl
  rw [hf, foldl_succStep]
  simp only [flushCarry, List.nil_append]
  rw [natOfBits_incSpec, natOfBits_bits]
  simp

/-! ### Size bookkeeping -/

lemma succListSize (n : ℕ) :
    (DataEncode.encode (succList n)).size ≤ (DataEncode.encode n).size := by
  have h1 := DataEncode.size_bits_le n.bits
  have h2 : (DataEncode.encode n).size = 2 + 6 * n.size := DataEncode.size_nat n
  have h3 : n.bits.length = n.size := Nat.size_eq_bits_len n
  simp only [succList]
  omega

/-- **The accumulator stays linear**: it holds one carry bit and one emitted bit per bit consumed,
and the input has at most `(encode n).size` bits. -/
lemma succAccSize (n j : ℕ) :
    (DataEncode.encode (foldAcc succList succInit succStep n j)).size
      ≤ 4 * (DataEncode.encode n).size + 8 := by
  have hacc : foldAcc succList succInit succStep n j
      = ((incSpec true (n.bits.take j)).1, [] ++ (incSpec true (n.bits.take j)).2) := by
    simp only [foldAcc, succList, succInit]
    exact foldl_succStep _ _ _
  rw [hacc, DataEncode.size_pair]
  have hc : (DataEncode.encode (incSpec true (n.bits.take j)).1).size ≤ 4 :=
    DataEncode.size_bool _
  have hlen : ([] ++ (incSpec true (n.bits.take j)).2).length ≤ n.bits.length := by
    simp only [List.nil_append, incSpec_length, List.length_take]
    omega
  have hout := DataEncode.size_bits_le ([] ++ (incSpec true (n.bits.take j)).2)
  have h2 : (DataEncode.encode n).size = 2 + 6 * n.size := DataEncode.size_nat n
  have h3 : n.bits.length = n.size := Nat.size_eq_bits_len n
  omega

lemma succFoldOutSize (n : ℕ) :
    (DataEncode.encode (foldFun succList succInit succStep n)).size
      ≤ 4 * (DataEncode.encode n).size + 8 := by
  rw [← foldAcc_length succList succInit succStep n]
  exact succAccSize n _

/-- **`Nat.succ` runs in polynomial time and linear space.** -/
theorem succ_polyTimeLinSpace
    (h_list : PolyTimeLinSpace succList)
    (h_init : PolyTimeLinSpace succInit)
    (h_step : PolyTimeLinSpace (Function.uncurry succStep))
    (h_finish : PolyTimeLinSpace flushCarry) :
    PolyTimeLinSpace Nat.succ := by
  have h_fold := foldl_computableUpTo succList succInit succStep
    (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n)
    (fun n => 4 * n + 8) (fun n => n)
    h_list h_init h_step monotone_id monotone_id succListSize succAccSize
  have h_comp := ComputableUpTo.comp (S_f := fun n => 4 * n + 8) h_fold h_finish
    monotone_id monotone_id succFoldOutSize
  have h_eq : flushCarry ∘ foldFun succList succInit succStep = Nat.succ :=
    funext flushCarry_foldFun
  rw [h_eq] at h_comp
  refine h_comp.absorb 6 2 34 (fun n => ?_) (fun n => ?_)
  · have hexp : (n + n + 2) ^ 2 = 4 * n * n + 8 * n + 4 := by ring
    rw [hexp]
    nlinarith
  · omega

end NatSucc

/-! ## 3. `Nat.add`

A ripple-carry adder. The list folded over is the two bit lists zipped, each padded with zeros to
their common length, so one `foldl` step is one full adder.

The correctness invariant is stated with `natOfBits` on both sides, which is what makes it a
routine induction: no reasoning about canonical forms is needed, only that the emitted bits carry
the right *value*.
-/

namespace NatAdd

/-- The sum bit of a full adder. -/
def sumBit (c x y : Bool) : Bool := Bool.xor (Bool.xor c x) y

/-- The carry-out of a full adder. -/
def carryOut (c x y : Bool) : Bool := (x && y) || (c && Bool.xor x y)

/-- Pad a bit list with zeros to length at least `k`. -/
def padTo (bs : List Bool) (k : ℕ) : List Bool := bs ++ List.replicate (k - bs.length) false

@[simp]
lemma padTo_length (bs : List Bool) (k : ℕ) : (padTo bs k).length = max bs.length k := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

@[simp]
lemma natOfBits_padTo (bs : List Bool) (k : ℕ) : natOfBits (padTo bs k) = natOfBits bs := by
  simp [padTo]

/-- The list the adder folds over: the two bit lists, zero-padded to a common length and zipped. -/
def addList (p : ℕ × ℕ) : List (Bool × Bool) :=
  (padTo p.1.bits (max p.1.bits.length p.2.bits.length)).zip
    (padTo p.2.bits (max p.1.bits.length p.2.bits.length))

/-- The initial accumulator: no carry in, nothing emitted yet. -/
def addInit (_ : ℕ × ℕ) : Bool × List Bool := (false, [])

/-- One full-adder step. -/
def addStep (acc : Bool × List Bool) (xy : Bool × Bool) : Bool × List Bool :=
  (carryOut acc.1 xy.1 xy.2, acc.2 ++ [sumBit acc.1 xy.1 xy.2])

/-- Closed form of the adder: the outgoing carry together with the emitted bits. -/
def addSpec (c : Bool) : List (Bool × Bool) → Bool × List Bool
  | [] => (c, [])
  | xy :: ps =>
    let r := addSpec (carryOut c xy.1 xy.2) ps
    (r.1, sumBit c xy.1 xy.2 :: r.2)

lemma foldl_addStep (ps : List (Bool × Bool)) (c : Bool) (out : List Bool) :
    ps.foldl addStep (c, out) = ((addSpec c ps).1, out ++ (addSpec c ps).2) := by
  induction ps generalizing c out with
  | nil => simp [addSpec]
  | cons xy ps ih => simp [addStep, addSpec, ih]

lemma addSpec_length (c : Bool) (ps : List (Bool × Bool)) :
    (addSpec c ps).2.length = ps.length := by
  induction ps generalizing c with
  | nil => simp [addSpec]
  | cons xy ps ih => simp [addSpec, ih]

/-- **The ripple-carry invariant.** -/
lemma natOfBits_addSpec (c : Bool) (ps : List (Bool × Bool)) :
    natOfBits ((addSpec c ps).2 ++ cond (addSpec c ps).1 [true] [])
      = natOfBits (ps.map Prod.fst) + natOfBits (ps.map Prod.snd) + cond c 1 0 := by
  induction ps generalizing c with
  | nil => cases c <;> simp [addSpec, Nat.bit_eq_two_mul_add]
  | cons xy ps ih =>
    obtain ⟨x, y⟩ := xy
    have h := ih (carryOut c x y)
    simp only [addSpec, List.cons_append, List.map_cons, natOfBits_cons,
      Nat.bit_eq_two_mul_add]
    rw [h]
    cases c <;> cases x <;> cases y <;> simp [sumBit, carryOut] <;> omega

/-! ### Reading the two summands back off the padded, zipped list -/

lemma map_fst_addList (p : ℕ × ℕ) :
    (addList p).map Prod.fst = padTo p.1.bits (max p.1.bits.length p.2.bits.length) :=
  List.map_fst_zip (by simp)

lemma map_snd_addList (p : ℕ × ℕ) :
    (addList p).map Prod.snd = padTo p.2.bits (max p.1.bits.length p.2.bits.length) :=
  List.map_snd_zip (by simp)

@[simp]
lemma addList_length (p : ℕ × ℕ) :
    (addList p).length = max p.1.bits.length p.2.bits.length := by
  simp only [addList, List.length_zip, padTo_length]
  omega

/-- **The fold computes `Nat.add`.** -/
lemma flushCarry_foldFun (p : ℕ × ℕ) :
    flushCarry (foldFun addList addInit addStep p) = p.1 + p.2 := by
  have hf : foldFun addList addInit addStep p = (addList p).foldl addStep (false, []) := rfl
  rw [hf, foldl_addStep]
  simp only [flushCarry, List.nil_append]
  rw [natOfBits_addSpec, map_fst_addList, map_snd_addList, natOfBits_padTo, natOfBits_padTo,
    natOfBits_bits, natOfBits_bits]
  simp

/-! ### Size bookkeeping -/

lemma addListSize (p : ℕ × ℕ) :
    (DataEncode.encode (addList p)).size ≤ 2 + 10 * (DataEncode.encode p).size := by
  have hb : ∀ xy ∈ addList p, (DataEncode.encode xy).size ≤ 10 := by
    intro xy _
    obtain ⟨x, y⟩ := xy
    have := DataEncode.size_bool x
    have := DataEncode.size_bool y
    rw [DataEncode.size_pair]
    omega
  have h1 := DataEncode.size_list_le (addList p) 10 hb
  have h2 : (addList p).length ≤ (DataEncode.encode p).size := by
    obtain ⟨a, b⟩ := p
    have ha := DataEncode.bits_length_le a
    have hb' := DataEncode.bits_length_le b
    rw [DataEncode.size_pair]
    simp only [addList_length]
    omega
  omega

/-- **The accumulator stays linear**: one carry bit plus one emitted bit per position. -/
lemma addAccSize (p : ℕ × ℕ) (j : ℕ) :
    (DataEncode.encode (foldAcc addList addInit addStep p j)).size
      ≤ 4 * (DataEncode.encode p).size + 8 := by
  have hacc : foldAcc addList addInit addStep p j
      = ((addSpec false ((addList p).take j)).1,
         [] ++ (addSpec false ((addList p).take j)).2) := by
    simp only [foldAcc, addInit]
    exact foldl_addStep _ _ _
  rw [hacc, DataEncode.size_pair]
  have hc : (DataEncode.encode (addSpec false ((addList p).take j)).1).size ≤ 4 :=
    DataEncode.size_bool _
  have hout := DataEncode.size_bits_le ([] ++ (addSpec false ((addList p).take j)).2)
  have hlen : ([] ++ (addSpec false ((addList p).take j)).2).length
      ≤ (DataEncode.encode p).size := by
    simp only [List.nil_append, addSpec_length, List.length_take]
    obtain ⟨a, b⟩ := p
    have ha := DataEncode.bits_length_le a
    have hb' := DataEncode.bits_length_le b
    rw [DataEncode.size_pair]
    simp only [addList_length]
    omega
  omega

lemma addFoldOutSize (p : ℕ × ℕ) :
    (DataEncode.encode (foldFun addList addInit addStep p)).size
      ≤ 4 * (DataEncode.encode p).size + 8 := by
  rw [← foldAcc_length addList addInit addStep p]
  exact addAccSize p _

/-- **`Nat.add` runs in polynomial time and linear space.** -/
theorem add_polyTimeLinSpace
    (h_list : PolyTimeLinSpace addList)
    (h_init : PolyTimeLinSpace addInit)
    (h_step : PolyTimeLinSpace (Function.uncurry addStep))
    (h_finish : PolyTimeLinSpace flushCarry) :
    PolyTimeLinSpace (fun p : ℕ × ℕ => p.1 + p.2) := by
  have h_fold := foldl_computableUpTo addList addInit addStep
    (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n)
    (fun n => 4 * n + 8) (fun n => 2 + 10 * n)
    h_list h_init h_step monotone_id monotone_id addListSize addAccSize
  have h_comp := ComputableUpTo.comp (S_f := fun n => 4 * n + 8) h_fold h_finish
    monotone_id monotone_id addFoldOutSize
  have h_eq : flushCarry ∘ foldFun addList addInit addStep = fun p : ℕ × ℕ => p.1 + p.2 :=
    funext flushCarry_foldFun
  rw [h_eq] at h_comp
  refine h_comp.absorb 40 2 38 (fun n => ?_) (fun n => ?_)
  · have hexp : (n + n + 2) ^ 2 = 4 * n * n + 8 * n + 4 := by ring
    rw [hexp]
    nlinarith
  · omega

end NatAdd

end MultiTapeTM

end Turing
