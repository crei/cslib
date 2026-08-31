/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold

/-!
# Example: `Nat.mul`

Shift-and-add. Fold over the bits of the second factor carrying a pair: the partial product and
the current shift `a * 2 ^ j`. Each step adds the shift when the bit is set and then doubles it.

Unlike `Nat.add`, this fold does not need the two arguments interleaved: it folds over one
factor's bits and keeps the other in the accumulator, so no padding or zipping is involved. The
step is where addition happens, so this example is genuinely *built on* the previous one rather
than circular — a step assumed here is a full addition, not a multiplication.

The accumulator bound is the interesting part: after `j` steps the partial product is
`natOfBits (b.bits.take j) * a < 2 ^ j * a` and the shift is `a * 2 ^ j`, so both have bit length
at most `a.size + b.size + 1`. Since the encoded input size is `6 * (a.size + b.size) + 6`, the
accumulator stays *linear*, and the fold runs in polynomial time and linear space.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

namespace NatMul

/-- The list the multiplier folds over: the bits of the second factor, least significant first. -/
def mulList (p : ℕ × ℕ) : List Bool := p.2.bits

/-- The initial accumulator: nothing accumulated yet, and the first factor as the initial shift. -/
def mulInit (p : ℕ × ℕ) : ℕ × ℕ := (0, p.1)

/-- Shift-and-add: add the current shift if the bit is set, then double the shift. -/
def mulStep (acc : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (acc.1 + cond b acc.2 0, acc.2 + acc.2)

/-! ### Correctness of the fold -/

/-- Closed form of the shift-and-add fold. -/
lemma foldl_mulStep (bs : List Bool) (acc sh : ℕ) :
    bs.foldl mulStep (acc, sh) = (acc + natOfBits bs * sh, sh * 2 ^ bs.length) := by
  induction bs generalizing acc sh with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons]
    change (bs.foldl mulStep (acc + cond b sh 0, sh + sh)) = _
    rw [ih]
    cases b <;>
      simp only [natOfBits_cons, Nat.bit_eq_two_mul_add, List.length_cons, pow_succ,
        Bool.cond_true, Bool.cond_false, Prod.mk.injEq] <;>
      constructor <;> ring

/-- **The fold computes `Nat.mul`.** -/
lemma foldFun_mul (p : ℕ × ℕ) :
    (foldFun mulList mulInit mulStep p).1 = p.1 * p.2 := by
  obtain ⟨a, b⟩ := p
  change (b.bits.foldl mulStep (0, a)).1 = a * b
  rw [foldl_mulStep]
  simp [natOfBits_bits, Nat.mul_comm]

/-! ### Size bookkeeping -/

/-- The accumulator after `j` steps, in closed form. -/
lemma foldAcc_mul (a b : ℕ) (j : ℕ) :
    foldAcc mulList mulInit mulStep (a, b) j
      = (natOfBits (b.bits.take j) * a, a * 2 ^ (b.bits.take j).length) := by
  change ((b.bits.take j).foldl mulStep (0, a)) = _
  rw [foldl_mulStep]
  simp

/-- The prefix of a number's bits denotes something of no greater bit length. -/
lemma size_natOfBits_take (b : ℕ) (j : ℕ) :
    (natOfBits (b.bits.take j)).size ≤ b.size := by
  have hlen : (b.bits.take j).length ≤ b.size := by
    rw [List.length_take, Nat.size_eq_bits_len]
    omega
  exact Nat.size_le.mpr
    (lt_of_lt_of_le (natOfBits_lt _) (Nat.pow_le_pow_right (by omega) hlen))

/-- **The accumulator stays linear.** Both components have bit length at most
`a.size + b.size + 1`, which the encoding turns into at most twice the input size. -/
lemma mulAccSize (p : ℕ × ℕ) (j : ℕ) :
    (DataEncode.encode (foldAcc mulList mulInit mulStep p j)).size
      ≤ 2 * (DataEncode.encode p).size := by
  obtain ⟨a, b⟩ := p
  have hlen : (b.bits.take j).length ≤ b.size := by
    rw [List.length_take, Nat.size_eq_bits_len]
    omega
  have h1 : (natOfBits (b.bits.take j) * a).size ≤ b.size + a.size :=
    le_trans (Nat.size_mul_le _ _) (Nat.add_le_add_right (size_natOfBits_take b j) _)
  have h2 : (a * 2 ^ (b.bits.take j).length).size ≤ a.size + b.size + 1 := by
    have := Nat.size_mul_le a (2 ^ (b.bits.take j).length)
    have := Nat.size_two_pow_le (b.bits.take j).length
    omega
  rw [foldAcc_mul, DataEncode.size_pair, DataEncode.size_pair,
    DataEncode.size_nat, DataEncode.size_nat, DataEncode.size_nat, DataEncode.size_nat]
  omega

/-- The list folded over is no bigger than the input. -/
lemma mulListSize (p : ℕ × ℕ) :
    (DataEncode.encode (mulList p)).size ≤ (DataEncode.encode p).size := by
  obtain ⟨a, b⟩ := p
  have h1 := DataEncode.size_bits_le b.bits
  have h2 : b.bits.length = b.size := Nat.size_eq_bits_len b
  change (DataEncode.encode b.bits).size ≤ _
  rw [DataEncode.size_pair, DataEncode.size_nat, DataEncode.size_nat]
  omega

lemma mulFoldOutSize (p : ℕ × ℕ) :
    (DataEncode.encode (foldFun mulList mulInit mulStep p)).size
      ≤ 2 * (DataEncode.encode p).size := by
  rw [← foldAcc_length mulList mulInit mulStep p]
  exact mulAccSize p _

/-- **`Nat.mul` runs in polynomial time and linear space.** -/
theorem mul_polyTimeLinSpace
    (h_list : PolyTimeLinSpace mulList)
    (h_init : PolyTimeLinSpace mulInit)
    (h_step : PolyTimeLinSpace (Function.uncurry mulStep))
    (h_fst : PolyTimeLinSpace (Prod.fst : ℕ × ℕ → ℕ)) :
    PolyTimeLinSpace (fun p : ℕ × ℕ => p.1 * p.2) := by
  have h_fold := foldl_computableUpTo mulList mulInit mulStep
    (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n) (fun n => n)
    (fun n => 2 * n) (fun n => n)
    h_list h_init h_step monotone_id monotone_id mulListSize mulAccSize
  have h_comp := ComputableUpTo.comp (S_f := fun n => 2 * n) h_fold h_fst
    monotone_id monotone_id mulFoldOutSize
  have h_eq : Prod.fst ∘ foldFun mulList mulInit mulStep = fun p : ℕ × ℕ => p.1 * p.2 :=
    funext foldFun_mul
  rw [h_eq] at h_comp
  refine h_comp.absorb 1 2 12 (fun n => ?_) (fun n => ?_)
  · have hexp : (n + n + 2) ^ 2 = 4 * n * n + 8 * n + 4 := by ring
    rw [hexp]
    nlinarith
  · omega

end NatMul

end MultiTapeTM

end Turing
