/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RTM.Tools

/-! # Binary arithmetic for rose tree machines

Program builders computing arithmetic on natural numbers in their default LSB-first binary
encoding (`Nat.bits`), together with their semantics. Each operation comes with a math-level
correctness lemma (on bit lists) and a `ComputesEnc` semantics proof for the corresponding
program builder.

## Main definitions

- `PB.succ` - the successor `n + 1`
- `PB.add` - binary addition `x + y`
- `PB.mul` - binary multiplication `x * y`

-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace PB

variable {env : List Value}
variable {α : Type} [DataEncode α]
variable {β : Type} [DataEncode β]

/-- The fold step used by `succBin`: given the running `(carry, acc)` and the next `bit`, emit the
new carry `carry && bit` and prepend the output bit `carry ^^ bit`. -/
def succBinStep (p : Bool × List Bool) (bit : Bool) : Bool × List Bool :=
  (p.1 && bit, (p.1 ^^ bit) :: p.2)

def succBin (n : List Bool) : List Bool :=
  let (final_carry, rev_res) := n.foldl succBinStep (true, [])
  (if final_carry then true :: rev_res else rev_res).reverse

/-- With carry `false`, the fold never produces a carry and simply reverses the remaining bits onto
the accumulator. -/
lemma foldl_succBinStep_false (bs : List Bool) (acc : List Bool) :
    bs.foldl succBinStep (false, acc) = (false, bs.reverse ++ acc) := by
  induction bs generalizing acc with
  | nil => simp
  | cons hd tl ih => simp [succBinStep, ih (hd :: acc)]

/-- The accumulator threads through the fold independently of the computed carry and output bits. -/
lemma foldl_succBinStep_acc (bs : List Bool) (c : Bool) (acc : List Bool) :
    bs.foldl succBinStep (c, acc)
      = ((bs.foldl succBinStep (c, [])).1, (bs.foldl succBinStep (c, [])).2 ++ acc) := by
  induction bs generalizing c acc with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, show succBinStep (c, acc) hd = (c && hd, (c ^^ hd) :: acc) from rfl,
      ih (c && hd) ((c ^^ hd) :: acc), List.foldl_cons,
      show succBinStep (c, ([] : List Bool)) hd = (c && hd, [c ^^ hd]) from rfl,
      ih (c && hd) [c ^^ hd]]
    simp

lemma succ_bin_correct (n : ℕ) : succBin n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rw [Nat.zero_bits]; rfl
  | bit b m hb ih =>
    rw [Nat.bits_append_bit m b hb]
    unfold succBin
    cases b with
    | false =>
      rw [List.foldl_cons,
        show succBinStep (true, []) false = (false, [true]) from rfl,
        foldl_succBinStep_false, Nat.bit_false_apply, Nat.bit1_bits]
      simp
    | true =>
      rw [List.foldl_cons,
        show succBinStep (true, []) true = (true, [false]) from rfl,
        foldl_succBinStep_acc, Nat.bit_true_apply,
        show 2 * m + 1 + 1 = 2 * (m + 1) from by omega,
        Nat.bit0_bits (m + 1) (Nat.succ_ne_zero m), ← ih]
      unfold succBin
      dsimp only
      split <;> simp [List.reverse_append]

def succ_foldl_body (st bit : PB) : PB :=
  let carry := st.fst
  let acc := st.snd
  toPair (boolAnd carry bit) (cons (boolXor carry bit) acc)

/-- Compute ℕ.succ (in its default binary encoding). -/
def succ (x : PB) : PB :=
  let loop_result := foldl
    succ_foldl_body
    (toPair (constantEnc true) empty)
    x
  let final_carry := loop_result.fst
  let result_rev := loop_result.snd
  -- If final carry, prepend 1; otherwise just reverse back
  reverse (boolIte final_carry (cons (constantEnc true) result_rev) result_rev)

/-- The `succ` program computes `succBin` on the underlying bit list, independently of whether
that list is a canonical ℕ encoding. -/
lemma succ_computes_list {p : PB} {l : List Bool} (h : p.ComputesEnc env l) :
    (succ p).ComputesEnc env (succBin l) := by
  have h_body : ∀ {e : List Value} {pa pb : PB} {a : Bool × List Bool} {b : Bool},
      pa.ComputesEnc e a → pb.ComputesEnc e b →
      (succ_foldl_body pa pb).ComputesEnc e
        ((fun (st : Bool × List Bool) bit => (st.1 && bit, (st.1 ^^ bit) :: st.2)) a b) := by
    intro e pa pb a b ha hb
    exact toPair_computesEnc (boolAnd_computes (fst_ComputesEnc ha) hb)
      (cons_computesEnc (boolXor_computes (fst_ComputesEnc ha) hb) (snd_ComputesEnc ha))
  have h_fold := foldl_computes
    (toPair_computesEnc (constantEnc_computesEnc (a := true)) (empty_computesEnc Bool))
    h h_body
  apply reverse_computes (boolIte_computes (fst_ComputesEnc h_fold) ?_ (snd_ComputesEnc h_fold))
  exact cons_computesEnc constantEnc_computesEnc (snd_ComputesEnc h_fold)

lemma succ_computes {p : PB} {n : ℕ} (h : p.ComputesEnc env n) :
    (succ p).ComputesEnc env (n + 1) := by
  change (succ p).ComputesEnc env (n + 1).bits
  rw [← succ_bin_correct]
  exact succ_computes_list h

/-- Computes addition of three bits, returning `(sum, carry)`. -/
def fullAdder (x y carry : Bool) : Bool × Bool :=
  (x ^^ y ^^ carry, (x && y) || (carry && (x ^^ y)))

/-- One ripple-carry step. The state `(toAdd, carry, acc)` carries the remaining bits of the second
addend (`toAdd`), the running `carry`, and the reversed output bits (`acc`). Each step consumes the
next bit of the first addend together with the front bit of `toAdd` (or `false` once `toAdd` is
exhausted), emitting the sum bit onto `acc`. -/
def addBinStep (p : List Bool × Bool × List Bool) (bit : Bool) : List Bool × Bool × List Bool :=
  match p.1 with
  | [] => ([], (fullAdder false bit p.2.1).2, (fullAdder false bit p.2.1).1 :: p.2.2)
  | a :: as => (as, (fullAdder a bit p.2.1).2, (fullAdder a bit p.2.1).1 :: p.2.2)

/-- Adds the bit lists `x` and `y` with an incoming `carry`. -/
def addCarry (carry : Bool) (x y : List Bool) : List Bool :=
  let (toAdd, finalCarry, rev) := x.foldl addBinStep (y, carry, [])
  rev.reverse ++ (if finalCarry then succBin toAdd else toAdd)

def addBin (x y : List Bool) : List Bool := addCarry false x y

/-- The accumulator threads through the `addBinStep` fold independently of the remaining addend and
carry. -/
lemma foldl_addBinStep_acc (xs ys : List Bool) (c : Bool) (acc : List Bool) :
    xs.foldl addBinStep (ys, c, acc)
      = ((xs.foldl addBinStep (ys, c, [])).1, (xs.foldl addBinStep (ys, c, [])).2.1,
         (xs.foldl addBinStep (ys, c, [])).2.2 ++ acc) := by
  induction xs generalizing ys c acc with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons]
    cases ys with
    | nil =>
      simp only [addBinStep]
      rw [ih [] _ _, ih [] _ [_]]
      simp
    | cons d ds =>
      simp only [addBinStep]
      rw [ih ds _ _, ih ds _ [_]]
      simp

/-- Evaluating `addBinStep` on `y.bits` exposes the next sum bit and carry via `fullAdder`,
independently of whether `y` is zero. -/
lemma addBinStep_bits (y : ℕ) (c b : Bool) (acc : List Bool) :
    addBinStep (y.bits, c, acc) b
      = (y.div2.bits, (fullAdder (Nat.bodd y) b c).2, (fullAdder (Nat.bodd y) b c).1 :: acc) := by
  cases y using Nat.binaryRec' with
  | zero => simp [addBinStep, Nat.zero_bits]
  | bit d m hd => rw [Nat.bits_append_bit m d hd]; simp [addBinStep]

/-- Peeling the first bit of the first addend in `addCarry`, when the second addend is `y.bits`. -/
lemma addCarry_cons_bits (c b : Bool) (xs : List Bool) (y : ℕ) :
    addCarry c (b :: xs) y.bits
      = (fullAdder (Nat.bodd y) b c).1
        :: addCarry (fullAdder (Nat.bodd y) b c).2 xs y.div2.bits := by
  unfold addCarry
  rw [List.foldl_cons, addBinStep_bits,
    foldl_addBinStep_acc xs y.div2.bits (fullAdder (Nat.bodd y) b c).2
      [(fullAdder (Nat.bodd y) b c).1]]
  simp [List.reverse_append]

lemma addCarry_correct (c : Bool) (x y : ℕ) :
    addCarry c x.bits y.bits = (x + y + c.toNat).bits := by
  induction x using Nat.binaryRec' generalizing c y with
  | zero => cases c <;> simp [addCarry, Nat.zero_bits, succ_bin_correct]
  | bit b m hb ih =>
    rw [Nat.bits_append_bit m b hb, addCarry_cons_bits, ih]
    have hy := Nat.bodd_add_div2 y
    rw [show Nat.bit b m + y + c.toNat
        = Nat.bit (fullAdder (Nat.bodd y) b c).1
            (m + y.div2 + (fullAdder (Nat.bodd y) b c).2.toNat) from by
          simp only [Nat.bit_val, fullAdder]
          cases b <;> cases c <;> cases hbd : Nat.bodd y <;> simp_all <;> omega]
    rw [Nat.bits_append_bit]
    rintro hzero
    have hb' : b = true := hb (by omega)
    subst hb'
    simp only [fullAdder] at hzero ⊢
    cases c <;> cases hbd : Nat.bodd y <;> simp_all

lemma addBin_correct (x y : ℕ) : addBin x.bits y.bits = (x + y).bits := by
  rw [addBin, addCarry_correct]
  simp

/-- The sum bit of a full adder, as a builder. -/
def addSumPB (a bit carry : PB) : PB := boolXor (boolXor a bit) carry

/-- The carry-out bit of a full adder, as a builder. -/
def addCarryPB (a bit carry : PB) : PB :=
  boolOr (boolAnd a bit) (boolAnd carry (boolXor a bit))

lemma addSumPB_computes {pa pbit pc : PB} {av bv cv : Bool}
    (ha : pa.ComputesEnc env av) (hbit : pbit.ComputesEnc env bv)
    (hc : pc.ComputesEnc env cv) :
    (addSumPB pa pbit pc).ComputesEnc env (fullAdder av bv cv).1 := by
  simp only [fullAdder, addSumPB]
  exact boolXor_computes (boolXor_computes ha hbit) hc

lemma addCarryPB_computes {pa pbit pc : PB} {av bv cv : Bool}
    (ha : pa.ComputesEnc env av) (hbit : pbit.ComputesEnc env bv)
    (hc : pc.ComputesEnc env cv) :
    (addCarryPB pa pbit pc).ComputesEnc env (fullAdder av bv cv).2 := by
  simp only [fullAdder, addCarryPB]
  exact boolOr_computes (boolAnd_computes ha hbit)
    (boolAnd_computes hc (boolXor_computes ha hbit))

/-- The fold body implementing `addBinStep`. The state encodes the triple `(toAdd, carry, acc)`:
consume the front bit of `toAdd` (or `false` once it is exhausted) together with the current bit
`bit` of the first addend, emitting the sum bit onto `acc` and threading the new carry. -/
def add_foldl_body (st bit : PB) : PB :=
  elim st.fst
    (toPair empty
      (toPair (addCarryPB (constantEnc false) bit st.snd.fst)
        (cons (addSumPB (constantEnc false) bit st.snd.fst) st.snd.snd)))
    (fun hd tl =>
      toPair tl
        (toPair (addCarryPB hd bit st.snd.fst)
          (cons (addSumPB hd bit st.snd.fst) st.snd.snd)))

/-- Compute binary addition in the default ℕ encoding. Mirrors `addBin`/`addCarry`: fold
`add_foldl_body` over the first addend `x` starting from state `(y, false, [])`, then reverse the
emitted bits and append the leftover high bits (incremented when a final carry remains). -/
def add (x y : PB) : PB :=
  let loop := foldl add_foldl_body (toPair y (toPair (constantEnc false) empty)) x
  listAppend (reverse loop.snd.snd) (boolIte loop.snd.fst (succ loop.fst) loop.fst)

/-- The `add` program computes `addBin` on the underlying bit lists, for any lists (not just
canonical ℕ encodings). -/
lemma add_computes_list {px py : PB} {l1 l2 : List Bool}
    (hx : px.ComputesEnc env l1) (hy : py.ComputesEnc env l2) :
    (add px py).ComputesEnc env (addBin l1 l2) := by
  have h_body : ∀ {e : List Value} {pa pb : PB}
      {a : List Bool × Bool × List Bool} {b : Bool},
      pa.ComputesEnc e a → pb.ComputesEnc e b →
      (add_foldl_body pa pb).ComputesEnc e (addBinStep a b) := by
    intro e pa pb a b ha hb
    obtain ⟨toAdd, carry, acc⟩ := a
    cases toAdd with
    | nil =>
      refine elim_nil_computes (fst_ComputesEnc ha) ?_
      exact toPair_computesEnc (empty_computesEnc Bool)
        (toPair_computesEnc
          (addCarryPB_computes constantEnc_computesEnc hb
            (fst_ComputesEnc (snd_ComputesEnc ha)))
          (cons_computesEnc
            (addSumPB_computes constantEnc_computesEnc hb
              (fst_ComputesEnc (snd_ComputesEnc ha)))
            (snd_ComputesEnc (snd_ComputesEnc ha))))
    | cons hd tl =>
      refine elim_cons_computes (fst_ComputesEnc ha) (computesFun₂_branch2 ?_)
      intro ext
      have ha' := (ha.extend ext).extend
        [Value.data (DataEncode.encode hd), Value.data (DataEncode.encode tl)]
      have hb' := (hb.extend ext).extend
        [Value.data (DataEncode.encode hd), Value.data (DataEncode.encode tl)]
      exact toPair_computesEnc (var_computes_fresh2 ext [])
        (toPair_computesEnc
          (addCarryPB_computes (var_computes_fresh ext _) hb'
            (fst_ComputesEnc (snd_ComputesEnc ha')))
          (cons_computesEnc
            (addSumPB_computes (var_computes_fresh ext _) hb'
              (fst_ComputesEnc (snd_ComputesEnc ha')))
            (snd_ComputesEnc (snd_ComputesEnc ha'))))
  have h_fold := foldl_computes
    (toPair_computesEnc hy
      (toPair_computesEnc (constantEnc_computesEnc (a := false)) (empty_computesEnc Bool)))
    hx h_body
  unfold addBin addCarry
  generalize hE : l1.foldl addBinStep (l2, false, []) = E at h_fold ⊢
  obtain ⟨tA, fC, rv⟩ := E
  unfold add
  exact listAppend_computes (reverse_computes (snd_ComputesEnc (snd_ComputesEnc h_fold)))
    (boolIte_computes (fst_ComputesEnc (snd_ComputesEnc h_fold))
      (succ_computes_list (fst_ComputesEnc h_fold))
      (fst_ComputesEnc h_fold))

lemma add_computes {px py : PB} {x y : ℕ}
    (hx : px.ComputesEnc env x) (hy : py.ComputesEnc env y) :
    (add px py).ComputesEnc env (x + y) := by
  change (add px py).ComputesEnc env (x + y).bits
  rw [← addBin_correct]
  exact add_computes_list hx hy

/-- Doubles a binary number (the math-level `· * 2`), keeping the canonical encoding: prepend a
`false` low bit, except for `0` (the empty list) which stays empty. -/
def doubleBin (l : List Bool) : List Bool :=
  match l with
  | [] => []
  | _ => false :: l

lemma doubleBin_bits (Y : ℕ) : doubleBin Y.bits = (2 * Y).bits := by
  cases Y using Nat.binaryRec' with
  | zero => simp [doubleBin, Nat.zero_bits]
  | bit b m hb =>
    have hYne : Nat.bit b m ≠ 0 := Nat.bit_ne_zero_iff.mpr hb
    rw [Nat.bits_append_bit m b hb, Nat.bit0_bits _ hYne, Nat.bits_append_bit m b hb]
    rfl

/-- One shift-and-add step of binary multiplication. The state `(shiftedY, product)` holds the
second addend shifted left by the current position and the running product. Each step doubles
`shiftedY` and, when the current bit of the multiplier is set, adds `shiftedY` into `product`. -/
def mulBinStep (st : List Bool × List Bool) (bit : Bool) : List Bool × List Bool :=
  (doubleBin st.1, if bit then addBin st.2 st.1 else st.2)

/-- Multiplies the bit lists `x` and `y` by folding `mulBinStep` over `x`. -/
def mulBin (x y : List Bool) : List Bool :=
  (x.foldl mulBinStep (y, [])).2

/-- Generalised correctness of the multiplication fold: folding `mulBinStep` over `n.bits`
starting from `(Y, P)` accumulates `P + n * Y` into the product component. -/
lemma mulBin_foldl (n Y P : ℕ) :
    (n.bits.foldl mulBinStep (Y.bits, P.bits)).2 = (P + n * Y).bits := by
  induction n using Nat.binaryRec' generalizing Y P with
  | zero => simp [Nat.zero_bits]
  | bit b m hb ih =>
    rw [Nat.bits_append_bit m b hb, List.foldl_cons]
    have hstep : mulBinStep (Y.bits, P.bits) b
        = ((2 * Y).bits, (if b then P + Y else P).bits) := by
      cases b <;> simp [mulBinStep, doubleBin_bits, addBin_correct]
    rw [hstep, ih]
    congr 1
    have hb2 : (if b then P + Y else P) = P + b.toNat * Y := by cases b <;> simp
    rw [hb2, Nat.bit_val, ← Nat.mul_assoc, Nat.mul_comm m 2, Nat.add_mul]
    omega

lemma mulBin_correct (x y : ℕ) : mulBin x.bits y.bits = (x * y).bits := by
  have h := mulBin_foldl x y 0
  rw [Nat.zero_bits] at h
  unfold mulBin
  rw [h]
  simp

/-- The PB builder doubling a binary number, implementing `doubleBin`. -/
def doublePB (l : PB) : PB :=
  elim l empty (fun hd tl => cons (constantEnc false) (cons hd tl))

lemma doublePB_computes {p : PB} {l : List Bool} (h : p.ComputesEnc env l) :
    (doublePB p).ComputesEnc env (doubleBin l) := by
  cases l with
  | nil => exact elim_nil_computes h (empty_computesEnc Bool)
  | cons hd tl =>
    refine elim_cons_computes h (computesFun₂_branch2 ?_)
    intro ext
    exact cons_computesEnc constantEnc_computesEnc
      (cons_computesEnc (var_computes_fresh ext _) (var_computes_fresh2 ext []))

/-- The fold body implementing `mulBinStep`: double the shifted second addend and conditionally
add it to the running product. -/
def mulFoldlBody (st bit : PB) : PB :=
  toPair (doublePB st.fst) (boolIte bit (add st.snd st.fst) st.snd)

/-- Compute binary multiplication in the default ℕ encoding. Fold `mul_foldl_body` over the first
factor `x`, starting from state `(y, [])`; the product component of the final state is the result.
The second factor `y` is copied into the accumulator (rather than read from the environment). -/
def mul (x y : PB) : PB :=
  snd (foldl mulFoldlBody (toPair y empty) x)

lemma mul_computes {px py : PB} {x y : ℕ}
    (hx : px.ComputesEnc env x) (hy : py.ComputesEnc env y) :
    (mul px py).ComputesEnc env (x * y) := by
  have h_body : ∀ {e : List Value} {pa pb : PB}
      {a : List Bool × List Bool} {b : Bool},
      pa.ComputesEnc e a → pb.ComputesEnc e b →
      (mulFoldlBody pa pb).ComputesEnc e (mulBinStep a b) := by
    intro e pa pb a b ha hb
    refine toPair_computesEnc (doublePB_computes (fst_ComputesEnc ha)) ?_
    exact boolIte_computes hb
      (add_computes_list (snd_ComputesEnc ha) (fst_ComputesEnc ha)) (snd_ComputesEnc ha)
  change (mul px py).ComputesEnc env (x * y).bits
  rw [← mulBin_correct]
  exact snd_ComputesEnc (foldl_computes
    (toPair_computesEnc hy (empty_computesEnc Bool)) hx h_body)

end PB

end RoseTreeMachine

end Turing
