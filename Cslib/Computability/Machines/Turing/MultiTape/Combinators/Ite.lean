/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Branch
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Adapters

/-!
# Complexity of a case analysis

A case analysis chooses which of several machines to continue with. `cond` is built directly on the
general tape-transformer machinery: the selector and the two branches enter the transformer
interface through `exists_transformsTapes_ofComputableInput`, and `exists_transformsTapes_branch`
dispatches on the selector's bit. `ite`, `dite` and the finite `match` are then read off `cond`.

## Why the branch not taken is never run

The dispatch reads the selector bit that the selector machine has left on a work tape and, in one
step, jumps to the `then`-arm or the `else`-arm; only that arm runs, and it emits its result
*straight to the shared output tape*. Only one arm ever runs, and its result is never parked to be
copied out — so nesting `n` conditionals runs `n` arms, not `2 ^ n`. This laziness is the content of
a case analysis, and it cannot come from composing total functions (`cond ∘ (fun a => (c a, f a,
g a))` would compute every branch), which is why one machine-level branch is unavoidable.

## From `cond` to `ite`, `dite` and `match`

`ite` and `dite` are `cond` read through `decide`; the finite `match` is a `Finset` induction that
splices in one `cond` per case.

## Bounds

Bounds here are deliberately relaxed to a single combined shape, `c * (… + 1)`, collecting the six
input bounds and the input length: nothing downstream depends on the conditional family being tight
(`loop` and `comp` do not use it), and the construction spends constant factors freely.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_match`: a case analysis on a scrutinee in a finite
  type. See `CslibTests.Complexity.Combinators` for worked examples.
* `Turing.MultiTapeTM.computableInTimeAndSpace_cond`: the recursor of `Bool`.
* `Turing.MultiTapeTM.computableInTimeAndSpace_ite`: Lean's `ite`, for a decidable predicate.
* `Turing.MultiTapeTM.computableInTimeAndSpace_dite`: Lean's `dite`, whose branches are defined
  only under a hypothesis and so are supplied through total extensions.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- The single-symbol encoding of a Boolean: `true`/`false` become the one-element words `[true]`,
`[false]`. Branching on a tape holding `boolEnc b` reads `b` directly as the head symbol, so the
dispatch of a two-way case analysis is a single-symbol read. -/
public def boolEnc : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

@[simp] public lemma boolEnc_apply (b : Bool) : boolEnc b = [b] := rfl

/-- **Complexity of a two-way case analysis**, the recursor of `Bool`. If the scrutinee and both
branches are computable, then so is the case analysis `bif sel a then g a else h a`.

The construction reuses the general tape-transformer machinery. The selector, the `then`-branch
and the `else`-branch are each placed on a shared work-tape layout by
`exists_transformsTapes_ofComputableInput`: the selector leaves its single bit `boolEnc (sel a)` on
tape `c`, and each branch reads the real input and leaves its encoded result on the shared output
tape `o` (treating `c` as a tape to keep). `exists_transformsTapes_branch` on tape `c` then runs the
`then`-branch when that bit is `true` and the `else`-branch otherwise — the two arms share the
postcondition "`o` holds `encOut (bif sel a then g a else h a)`", each arm supplying the case
(`sel a = true` / `sel a = false`) that identifies its result with it. Sequencing the selector
before the branch and emitting tape `o` (`computableInTimeAndSpace_of_transformsTapes`) reads off
the case analysis. Bounds are relaxed to the single combined shape `c * (… + 1)`; nothing
downstream needs them tight. -/
public theorem computableInTimeAndSpace_cond {sel : α → Bool} {g h : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {tc sc tif sif telse selse : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn boolEnc tc sc)
    (hif : ComputableInTimeAndSpace g encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace h encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => bif sel a then g a else h a) encIn encOut
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1))
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1)) := by
  classical
  -- the three function machines, placed on a shared layout by the general adapters
  obtain ⟨m_sel, c_sel, hsel'⟩ := exists_transformsTapes_ofComputableInput hsel
  obtain ⟨m_g, c_g, hif'⟩ := exists_transformsTapes_ofComputableInput hif
  obtain ⟨m_h, c_h, helse'⟩ := exists_transformsTapes_ofComputableInput helse
  set k := m_sel + m_g + m_h + 3 with hk
  let c : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  have hoc : o ≠ c := by apply Fin.ne_of_val_ne; simp
  -- `M_sel` writes the selector bit to tape `c`; `M_g`/`M_h` read the input, keep `c`, write to `o`
  obtain ⟨S_sel, hS_sel, M_sel, hM_sel⟩ :=
    hsel' k c ∅ (by simp) (by simp only [Finset.card_empty]; omega)
  obtain ⟨S_g, hS_g, M_g, hM_g⟩ :=
    hif' k o {c} (by simpa using hoc) (by simp only [Finset.card_singleton]; omega)
  obtain ⟨S_h, hS_h, M_h, hM_h⟩ :=
    helse' k o {c} (by simpa using hoc) (by simp only [Finset.card_singleton]; omega)
  have := hS_sel; have := hS_g; have := hS_h
  have hleg : ∀ a, (encOut (g a)).length ≤ tif a := hif.length_encOut_le
  have hleh : ∀ a, (encOut (h a)).length ≤ telse a := helse.length_encOut_le
  -- arm 1: run `g`, guarded by `sel a = true`, its result identified with the case analysis
  have h₁ : ∀ a, TransformsTapes M_g
      (fun input ws => (input = encIn a ∧ ∀ l, l ∉ ({c} : Finset (Fin k)) → ws l = [])
        ∧ sel a = true)
      (fun _ ws ws' => ws' = Function.update ws o (encOut (bif sel a then g a else h a)))
      (c_g * (tif a + 1)) (c_g * (sif a + (encOut (g a)).length + 1) + k) := by
    intro a
    refine (hM_g a).imp (fun _ _ hP => hP.1) (fun _ _ ws' hP hQ => ?_) le_rfl le_rfl
    rw [hQ]; simp only [hP.2, Bool.cond_true]
  -- arm 2: run `h`, guarded by `sel a = false`
  have h₂ : ∀ a, TransformsTapes M_h
      (fun input ws => (input = encIn a ∧ ∀ l, l ∉ ({c} : Finset (Fin k)) → ws l = [])
        ∧ sel a = false)
      (fun _ ws ws' => ws' = Function.update ws o (encOut (bif sel a then g a else h a)))
      (c_h * (telse a + 1)) (c_h * (selse a + (encOut (h a)).length + 1) + k) := by
    intro a
    refine (hM_h a).imp (fun _ _ hP => hP.1) (fun _ _ ws' hP hQ => ?_) le_rfl le_rfl
    rw [hQ]; simp only [hP.2, Bool.cond_false]
  -- branch on the selector bit on tape `c`
  obtain ⟨S_br, hS_br, M_br, hM_br⟩ :=
    exists_transformsTapes_branch (J := α) c true
      (P₁ := fun a input ws => (input = encIn a ∧ ∀ l, l ∉ ({c} : Finset (Fin k)) → ws l = [])
        ∧ sel a = true)
      (P₂ := fun a input ws => (input = encIn a ∧ ∀ l, l ∉ ({c} : Finset (Fin k)) → ws l = [])
        ∧ sel a = false)
      (Q := fun a _ ws ws' => ws' = Function.update ws o (encOut (bif sel a then g a else h a)))
      (t₁ := fun a => c_g * (tif a + 1))
      (s₁ := fun a => c_g * (sif a + (encOut (g a)).length + 1) + k)
      (t₂ := fun a => c_h * (telse a + 1))
      (s₂ := fun a => c_h * (selse a + (encOut (h a)).length + 1) + k) h₁ h₂
  have := hS_br
  -- run the selector, then the branch, as a single tape transformer emitting `o`
  have hMc : ∀ a, TransformsTapes (M_sel.seq M_br)
      (fun input ws => input = encIn a ∧ ∀ l, ws l = [])
      (fun _ _ ws' => ws' o = encOut (bif sel a then g a else h a))
      (c_sel * (tc a + 1) + (max (c_g * (tif a + 1)) (c_h * (telse a + 1)) + 1))
      (c_sel * (sc a + (boolEnc (sel a)).length + 1) + k +
        (max (c_g * (sif a + (encOut (g a)).length + 1) + k)
             (c_h * (selse a + (encOut (h a)).length + 1) + k) + k)) := by
    intro a
    refine (transformsTapes_seq (hM_sel a) (hM_br a) ?_).imp ?_ ?_ le_rfl le_rfl
    · -- handoff: after the selector, the branch precondition holds
      rintro _ ws ws' ⟨rfl, hblank⟩ hQsel
      have hchead : (ws' c).head? = some (sel a) := by rw [hQsel, Function.update_self]; simp
      have hbl : ∀ l, l ∉ ({c} : Finset (Fin k)) → ws' l = [] := fun l hl => by
        rw [hQsel, Function.update_of_ne (by simpa using hl)]; exact hblank l (by simp)
      split
      · rename_i hcond
        rw [hchead] at hcond
        exact ⟨⟨rfl, hbl⟩, Option.some.inj hcond⟩
      · rename_i hcond
        rw [hchead] at hcond
        refine ⟨⟨rfl, hbl⟩, ?_⟩
        rw [← Bool.not_eq_true]
        exact fun h => hcond (by rw [h])
    · -- an all-blank input satisfies the selector's precondition
      rintro _ ws ⟨rfl, hblank⟩
      exact ⟨rfl, fun l _ => hblank l⟩
    · -- read the result off the output tape
      rintro _ ws ws'' _ ⟨ws', _, hQbr⟩
      rw [hQbr, Function.update_self]
  -- emit tape `o`, turning the transformer into a computation
  obtain ⟨c₀, hc₀⟩ :=
    computableInTimeAndSpace_of_transformsTapes (gg := fun a => bif sel a then g a else h a) o hMc
  refine ⟨c₀ * (2 * c_sel + c_g + c_h + 3 * k + 3), hc₀.mono (fun a => ?_) (fun a => ?_)⟩
  · -- time
    set U := tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1 with hU
    have hlen : (encOut (bif sel a then g a else h a)).length ≤ U := by
      have := hleg a; have := hleh a
      cases sel a <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left c₀ ?_
    have e_sel : c_sel * (tc a + 1) ≤ c_sel * U := Nat.mul_le_mul_left _ (by omega)
    have e_g : c_g * (tif a + 1) ≤ c_g * U := Nat.mul_le_mul_left _ (by omega)
    have e_h : c_h * (telse a + 1) ≤ c_h * U := Nat.mul_le_mul_left _ (by omega)
    have hexp : (2 * c_sel + c_g + c_h + 3 * k + 3) * U
        = 2 * (c_sel * U) + c_g * U + c_h * U + 3 * (k * U) + 3 * U := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    omega
  · -- space
    set U := tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1 with hU
    have hlen : (encOut (bif sel a then g a else h a)).length ≤ U := by
      have := hleg a; have := hleh a
      cases sel a <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left c₀ ?_
    have hkU : k ≤ k * U := Nat.le_mul_of_pos_right k (by omega)
    have e_sel : c_sel * (sc a + (boolEnc (sel a)).length + 1) ≤ 2 * (c_sel * U) := by
      have h1 : (boolEnc (sel a)).length = 1 := by simp
      calc c_sel * (sc a + (boolEnc (sel a)).length + 1)
          ≤ c_sel * (2 * U) := Nat.mul_le_mul_left _ (by rw [h1]; omega)
        _ = 2 * (c_sel * U) := by rw [Nat.mul_left_comm]
    have e_g : c_g * (sif a + (encOut (g a)).length + 1) ≤ c_g * U :=
      Nat.mul_le_mul_left _ (by have := hleg a; omega)
    have e_h : c_h * (selse a + (encOut (h a)).length + 1) ≤ c_h * U :=
      Nat.mul_le_mul_left _ (by have := hleh a; omega)
    have hexp : (2 * c_sel + c_g + c_h + 3 * k + 3) * U
        = 2 * (c_sel * U) + c_g * U + c_h * U + 3 * (k * U) + 3 * U := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    omega

/-! ### The finite case analysis

The finite case analysis is built from `computableInTimeAndSpace_cond` by induction on a finite
set covering the scrutinee's reachable values. Because each inductive step splices in one more
`cond`, whose constants multiply, the bounds are renormalised at every step into the single fixed
shape `fun a => c * (t a + 1)`, `fun a => c * (s a + 1)`; the following three helpers do the
combining and the renormalisation, and the induction then reduces to routing the scrutinee. -/

variable {t s : α → ℕ} {encIn : α ↪ List Bool}

/-- A constant function, in the normalised bound shape `c * (t a + s a + (encIn a).length + 1)`. -/
private lemma const_norm {encOut : β ↪ List Bool} (b : β) :
    ∃ c, ComputableInTimeAndSpace (fun _ : α => b) encIn encOut
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encOut) b
  exact ⟨c, hc.mono (fun a => Nat.le_mul_of_pos_right c (by omega)) (fun a => Nat.zero_le _)⟩

/-- A two-way case analysis of three functions all given in the normalised shape stays in it. The
new `cond` bound mixes each argument's time *and* space bounds and adds the input length, but every
one of those is a constant times `t a + s a + (encIn a).length + 1`, so the shape is preserved. -/
private lemma cond_norm {sel : α → Bool} {g h : α → β} {encOut : β ↪ List Bool}
    (hsel : ∃ c, ComputableInTimeAndSpace sel encIn boolEnc
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1)))
    (hg : ∃ c, ComputableInTimeAndSpace g encIn encOut
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1)))
    (hh : ∃ c, ComputableInTimeAndSpace h encIn encOut
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1))) :
    ∃ c, ComputableInTimeAndSpace (fun a => bif sel a then g a else h a) encIn encOut
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1)) := by
  obtain ⟨c1, h1⟩ := hsel
  obtain ⟨c2, h2⟩ := hg
  obtain ⟨c3, h3⟩ := hh
  obtain ⟨C, hC⟩ := computableInTimeAndSpace_cond h1 h2 h3
  refine ⟨C * (2 * c1 + 2 * c2 + 2 * c3 + 2), hC.mono (fun a => ?_) (fun a => ?_)⟩ <;>
    · rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left C ?_
      have hexp : (2 * c1 + 2 * c2 + 2 * c3 + 2) * (t a + s a + (encIn a).length + 1) =
          2 * (c1 * (t a + s a + (encIn a).length + 1)) +
          2 * (c2 * (t a + s a + (encIn a).length + 1)) +
          2 * (c3 * (t a + s a + (encIn a).length + 1)) +
          2 * (t a + s a + (encIn a).length + 1) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      omega

/-- The single-bit test `decide (sel a = i₀)`, in the normalised shape. Composing the scrutinee with
the almost-constant test `· = i₀` is a `computableInTimeAndSpace_comp`; the constant test cost and
the encoded scrutinee's length are absorbed because the latter is bounded by the constant `L`. -/
private lemma cond_of_sel {ι : Type} [DecidableEq ι] {sel : α → ι} {encι : ι ↪ List Bool}
    (i₀ : ι) (L : ℕ) (hL : ∀ a, (encι (sel a)).length ≤ L)
    (hsel : ∃ c, ComputableInTimeAndSpace sel encIn encι
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1))) :
    ∃ c, ComputableInTimeAndSpace (fun a => decide (sel a = i₀)) encIn boolEnc
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1)) := by
  obtain ⟨c_sel, hsel'⟩ := hsel
  obtain ⟨cψ, hψ⟩ := computableInTimeAndSpace_of_exists_finite_ne
    (f := fun i => decide (i = i₀)) (encIn := encι) (encOut := boolEnc)
    ⟨false, by
      have hset : {i : ι | (fun i => decide (i = i₀)) i ≠ false} = {i₀} := by ext i; simp
      rw [hset]; exact Set.finite_singleton i₀⟩
  obtain ⟨cC, hcomp⟩ := computableInTimeAndSpace_comp hsel' hψ
  refine ⟨cC * (c_sel + cψ + L + 2), hcomp.mono (fun a => ?_) (fun a => ?_)⟩
  · rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left cC ?_
    have hL' := hL a
    have hexp : (c_sel + cψ + L + 2) * (t a + s a + (encIn a).length + 1) =
        c_sel * (t a + s a + (encIn a).length + 1) + cψ * (t a + s a + (encIn a).length + 1) +
        L * (t a + s a + (encIn a).length + 1) + 2 * (t a + s a + (encIn a).length + 1) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    have h1 : cψ ≤ cψ * (t a + s a + (encIn a).length + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : L ≤ L * (t a + s a + (encIn a).length + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left cC ?_
    have hL' := hL a
    have hbl : (boolEnc (decide (sel a = i₀))).length = 1 := rfl
    rw [hbl]
    have hexp : (c_sel + cψ + L + 2) * (t a + s a + (encIn a).length + 1) =
        c_sel * (t a + s a + (encIn a).length + 1) + cψ * (t a + s a + (encIn a).length + 1) +
        L * (t a + s a + (encIn a).length + 1) + 2 * (t a + s a + (encIn a).length + 1) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    have h2 : L ≤ L * (t a + s a + (encIn a).length + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- The engine of `computableInTimeAndSpace_match`: induction on a finite set `R` covering the
scrutinee's values, everything carried in the normalised shape `c * (t a + s a + (encIn a).length +
1)`. At `insert i₀ R'` the scrutinee is split by the test `sel a = i₀`. -/
private lemma match_aux {ι : Type} {br : ι → α → β}
    {encι : ι ↪ List Bool} {encOut : β ↪ List Bool} (R : Finset ι) :
    ∀ (sel : α → ι), (∀ a, sel a ∈ R) →
      (∀ i ∈ R, ComputableInTimeAndSpace (br i) encIn encOut t s) →
      (∃ c, ComputableInTimeAndSpace sel encIn encι
        (fun a => c * (t a + s a + (encIn a).length + 1))
        (fun a => c * (t a + s a + (encIn a).length + 1))) →
      ∃ c, ComputableInTimeAndSpace (fun a => br (sel a) a) encIn encOut
        (fun a => c * (t a + s a + (encIn a).length + 1))
        (fun a => c * (t a + s a + (encIn a).length + 1)) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro sel hmem _ _
    have hemp : IsEmpty α := ⟨fun a => absurd (hmem a) (Finset.notMem_empty _)⟩
    let : Fintype α := Fintype.ofIsEmpty
    obtain ⟨c, hc⟩ :=
      computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encOut) (fun a => br (sel a) a)
    exact ⟨c, hc.mono (fun a => Nat.le_mul_of_pos_right c (by omega)) (fun a => Nat.zero_le _)⟩
  | @insert i₀ R' hi₀ IH =>
    intro sel hmem hbr hsel
    by_cases hR'e : R' = ∅
    · subst hR'e
      have hall : ∀ a, sel a = i₀ := by
        intro a
        have hm := hmem a
        rw [Finset.mem_insert] at hm
        rcases hm with h | h
        · exact h
        · exact absurd h (Finset.notMem_empty _)
      have heq : (fun a => br (sel a) a) = br i₀ := funext fun a => by rw [hall a]
      rw [heq]
      exact ⟨1, (hbr i₀ (Finset.mem_insert_self i₀ ∅)).mono
        (fun a => by omega) (fun a => by omega)⟩
    · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hR'e
      have hL : ∀ a, (encι (sel a)).length ≤ (insert i₀ R').sup (fun i => (encι i).length) :=
        fun a => Finset.le_sup (f := fun i => (encι i).length) (hmem a)
      obtain ⟨cc, hcc⟩ := cond_of_sel i₀ _ hL hsel
      have hsel' : ∃ c, ComputableInTimeAndSpace
          (fun a => bif decide (sel a = i₀) then d else sel a) encIn encι
          (fun a => c * (t a + s a + (encIn a).length + 1))
          (fun a => c * (t a + s a + (encIn a).length + 1)) :=
        cond_norm ⟨cc, hcc⟩ (const_norm d) hsel
      have hmem' : ∀ a, (fun a => bif decide (sel a = i₀) then d else sel a) a ∈ R' := by
        intro a
        by_cases h : sel a = i₀
        · simpa [h] using hd
        · have hm := hmem a
          simp only [Finset.mem_insert, h, false_or] at hm
          simpa [h] using hm
      obtain ⟨cRec, hRec⟩ := IH (fun a => bif decide (sel a = i₀) then d else sel a)
        hmem' (fun i hi => hbr i (Finset.mem_insert_of_mem hi)) hsel'
      have hGeq : (fun a => br (sel a) a) =
          (fun a => bif decide (sel a = i₀) then br i₀ a
            else br (bif decide (sel a = i₀) then d else sel a) a) := by
        funext a
        by_cases h : sel a = i₀ <;> simp [h]
      rw [hGeq]
      exact cond_norm ⟨cc, hcc⟩
        ⟨1, (hbr i₀ (Finset.mem_insert_self i₀ R')).mono (fun a => by omega) (fun a => by omega)⟩
        ⟨cRec, hRec⟩

/-- **Complexity of a case analysis on a finite type.** If the scrutinee and every branch are
computable, then so is the case analysis. The machine runs the machine for `sel`, redirecting its
output onto a work tape; since the scrutinee's range is finite there are only finitely many
possible contents, all of constant length, so the finite control can tell them apart in constant
time and continue with the machine for the branch that is taken, on the original input.

What is asked of the scrutinee's type is not that it be finite but that only finitely many of its
values be reachable, which is what the machine needs: finitely many possible contents of the work
tape, of bounded length, for the control to tell apart. For a finite type that is `Set.toFinite _`.

A single pair of bounds covers the scrutinee and every branch. The number of cases is a constant
of the covering set and is absorbed into the constant factor. What expresses that only the branch
taken is executed is that no time bound appears in the space bound: a machine computing every
branch would have to park their encoded outputs, whose length is bounded only by the time that
produced them, so its space would be `s a + t a`.

A branch only has to *agree* with the function being computed where it is taken, which is what
`hagree` says; what it does elsewhere is irrelevant, since it is never run there. `f` carries no
information — it is `fun a => br (sel a) a` up to `funext` — but is kept because it is what a caller
has: their goal is a `match`, not an application of the branch family. It is inferred from the
goal, so apply this with `exact` or `refine` rather than `obtain`. -/
public theorem computableInTimeAndSpace_match {ι : Type}
    {sel : α → ι} {f : α → β} {br : ι → α → β}
    {encι : ι ↪ List Bool} {encOut : β ↪ List Bool}
    (hfin : (Set.range sel).Finite)
    (hagree : ∀ a, br (sel a) a = f a)
    (hsel : ComputableInTimeAndSpace sel encIn encι t s)
    (hbr : ∀ i ∈ Set.range sel, ComputableInTimeAndSpace (br i) encIn encOut t s) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut
      (fun a => c * (t a + s a + (encIn a).length + 1))
      (fun a => c * (t a + s a + (encIn a).length + 1)) := by
  classical
  obtain ⟨c, hc⟩ := match_aux hfin.toFinset sel
    (fun a => hfin.mem_toFinset.mpr (Set.mem_range_self a))
    (fun i hi => hbr i (hfin.mem_toFinset.mp hi))
    ⟨1, hsel.mono (fun a => by omega) (fun a => by omega)⟩
  refine ⟨c, ?_⟩
  have hf : (fun a => br (sel a) a) = f := funext hagree
  rwa [hf] at hc

/-- **Complexity of Lean's `ite`.** A conditional on a decidable predicate, given a machine that
decides it. This is `computableInTimeAndSpace_cond` read through `decide`: the `Decidable` instance
of `ite` carries no computational content, so all that is needed of the predicate is that its
Boolean test is computable to `boolEnc`. -/
public theorem computableInTimeAndSpace_ite {p : α → Prop} [DecidablePred p] {g h : α → β}
    {encOut : β ↪ List Bool} {tc sc tif sif telse selse : α → ℕ}
    (hp : ComputableInTimeAndSpace (fun a => decide (p a)) encIn boolEnc tc sc)
    (hif : ComputableInTimeAndSpace g encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace h encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => if p a then g a else h a) encIn encOut
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1))
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_cond hp hif helse
  refine ⟨c, ?_⟩
  have hfun : (fun a => bif decide (p a) then g a else h a) =
      fun a => if p a then g a else h a := by
    funext a; by_cases h : p a <;> simp [h]
  rwa [hfun] at hc

/-- **Complexity of Lean's `dite`.** The branches of a `dite` are not functions of the input alone:
each is defined only under the hypothesis that its case holds, so neither can be asked to be
computable as it stands. What is asked instead is a computable *total* function agreeing with the
branch where that branch is taken. -/
public theorem computableInTimeAndSpace_dite {p : α → Prop} [DecidablePred p]
    {_if : (a : α) → p a → β} {_else : (a : α) → ¬ p a → β} {If Else : α → β}
    {encOut : β ↪ List Bool} {tc sc tif sif telse selse : α → ℕ}
    (hIf : ∀ a (h : p a), If a = _if a h)
    (hElse : ∀ a (h : ¬ p a), Else a = _else a h)
    (hp : ComputableInTimeAndSpace (fun a => decide (p a)) encIn boolEnc tc sc)
    (hif : ComputableInTimeAndSpace If encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace Else encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => dite (p a) (_if a) (_else a)) encIn encOut
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1))
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1)) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_ite (p := p) hp hif helse
  refine ⟨c, ?_⟩
  have hfun : (fun a => if p a then If a else Else a) =
      fun a => dite (p a) (_if a) (_else a) := by
    funext a
    by_cases h : p a
    · simp [h, hIf a h]
    · simp [h, hElse a h]
  rwa [hfun] at hc

end Turing.MultiTapeTM
