/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.PFun
public import Mathlib.Tactic.Ring
public import Mathlib.Computability.StateTransition
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Words

/-!
# Loop combinator

This file is about the loop whose condition and body are fused into a single function
`body : α → Option α`, which returns `none` exactly when the loop is to stop:

```
loop
  match body a with
  | none => return a
  | some a' => a := a'
```

This is the form in which the loop is implemented by a machine, since it needs only one machine for
the whole loop body. The usual `while` loop, with a separate condition and body, is derived from it
in `Cslib.Computability.Machines.Turing.MultiTape.Combinators.While`.

## Main definitions

* `Turing.MultiTapeTM.loopFunction`: the partial function computed by the loop, defined as
  `StateTransition.eval` of the loop body. It is undefined on the inputs for which the loop
  diverges.
* `Turing.MultiTapeTM.loopIterate`: the value after a given number of iterations, or `none` if the
  loop has already stopped.

## Main results

* `Turing.MultiTapeTM.mem_loopFunction_iff`: the loop started at `a` terminates in `b` exactly if
  `b` is an iterate of `a` at which the body stops.
* `Turing.MultiTapeTM.computableInTimeAndSpace_loopFunction`: the complexity of the loop.
-/

namespace Turing.MultiTapeTM

variable {α : Type*}

/-- The partial function computed by the loop with the fused body `body`, which returns `none`
exactly when the loop is to stop. It is defined exactly on the inputs for which the loop
terminates. -/
@[expose] public def loopFunction (body : α → Option α) : α →. α := StateTransition.eval body

/-- The value after `n` iterations of the fused loop body, or `none` if the loop has stopped
after at most `n` iterations. -/
@[expose] public def loopIterate (body : α → Option α) : ℕ → α → Option α
  | 0, a => some a
  | n + 1, a => (body a).bind (loopIterate body n)

section Iterate

/-! ## The iterates of the loop body

The loop is described by two views of its body: `loopIterate`, which is what the machine actually
runs through, and `loopFunction`, which is what it computes. This section relates them.
-/

variable {body : α → Option α}

@[simp]
public lemma loopIterate_zero (a : α) : loopIterate body 0 a = some a := rfl

public lemma loopIterate_succ (n : ℕ) (a : α) :
    loopIterate body (n + 1) a = (body a).bind (loopIterate body n) := rfl

@[simp]
public lemma loopIterate_one (a : α) : loopIterate body 1 a = body a := by
  cases h : body a <;> simp [loopIterate_succ, h]

/-- The iterates of the loop body compose. -/
public lemma loopIterate_add (m n : ℕ) (a : α) :
    loopIterate body (m + n) a = (loopIterate body m a).bind (loopIterate body n) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    cases h : body a with
    | none => simp [show m + 1 + n = m + n + 1 by omega, loopIterate_succ, h]
    | some b => simp [show m + 1 + n = m + n + 1 by omega, loopIterate_succ, h, ih]

/-- One more iteration can also be performed at the end. -/
public lemma loopIterate_succ' (n : ℕ) (a : α) :
    loopIterate body (n + 1) a = (loopIterate body n a).bind body := by
  rw [loopIterate_add]
  simp

/-- Once the loop has stopped it stays stopped. -/
public lemma loopIterate_eq_none_of_le {m n : ℕ} {a : α} (h : m ≤ n)
    (hm : loopIterate body m a = none) : loopIterate body n a = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [loopIterate_add, hm]
  rfl

/-- Before the loop has stopped it has not stopped. -/
public lemma loopIterate_ne_none_of_le {m n : ℕ} {a : α} (h : m ≤ n)
    (hn : loopIterate body n a ≠ none) : loopIterate body m a ≠ none :=
  fun hm => hn (loopIterate_eq_none_of_le h hm)

/-- The values reachable by repeatedly applying the loop body are exactly its iterates. -/
public lemma reaches_iff_loopIterate {a b : α} :
    Relation.ReflTransGen (fun x y => y ∈ body x) a b ↔ ∃ n, loopIterate body n a = some b := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hstep _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [loopIterate_succ, Option.mem_def.mp hstep]; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero =>
      rw [loopIterate_zero, Option.some_inj] at hn
      exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
      rw [loopIterate_succ] at hn
      cases hc : body a with
      | none => rw [hc] at hn; simp at hn
      | some c =>
        rw [hc] at hn
        exact Relation.ReflTransGen.head (Option.mem_def.mpr hc) (ih hn)

/-- **The graph of `loopFunction`.** The loop started at `a` terminates in `b` exactly if `b` is an
iterate of `a` at which the body stops. -/
public theorem mem_loopFunction_iff {a b : α} :
    b ∈ loopFunction body a ↔ ∃ n, loopIterate body n a = some b ∧ body b = none := by
  rw [loopFunction, StateTransition.mem_eval, StateTransition.Reaches, reaches_iff_loopIterate]
  exact ⟨fun ⟨⟨n, hn⟩, hb⟩ => ⟨n, hn, hb⟩, fun ⟨n, hn, hb⟩ => ⟨⟨n, hn⟩, hb⟩⟩

end Iterate

section Bounds

/-! ## Arithmetic helpers

Every machine that the loop is assembled from costs a constant times the sum of a few lengths, and
every one of those lengths is bounded by a constant times `s a + 1` or `t a + s a + 1`. These
lemmas turn such a sum into a single constant times the bound. -/

private lemma nat_bound₀ {W u X : ℕ} (hu : 1 ≤ u) (hX : X ≤ W * u) : X + 1 ≤ (W + 1) * u := by
  calc X + 1 ≤ W * u + u := Nat.add_le_add hX hu
    _ = (W + 1) * u := by ring

private lemma nat_bound₁ {c W u X : ℕ} (hu : 1 ≤ u) (hX : X ≤ W * u) :
    c * (X + 1) ≤ c * (W + 1) * u := by
  calc c * (X + 1) ≤ c * (W * u + u) := by gcongr
    _ = c * (W + 1) * u := by ring

private lemma nat_bound₂ {c W u X Y : ℕ} (hu : 1 ≤ u) (hX : X ≤ W * u) (hY : Y ≤ W * u) :
    c * (X + Y + 1) ≤ c * (2 * W + 1) * u := by
  calc c * (X + Y + 1) ≤ c * (W * u + W * u + u) := by gcongr
    _ = c * (2 * W + 1) * u := by ring

private lemma nat_bound₃ {c W u X Y Z : ℕ} (hu : 1 ≤ u) (hX : X ≤ W * u) (hY : Y ≤ W * u)
    (hZ : Z ≤ W * u) : c * (X + Y + Z + 1) ≤ c * (3 * W + 1) * u := by
  calc c * (X + Y + Z + 1) ≤ c * (W * u + W * u + W * u + u) := by gcongr
    _ = c * (3 * W + 1) * u := by ring

/-- A constant summand is absorbed into the constant factor. -/
private lemma nat_bound_add {c d u X : ℕ} (hu : 1 ≤ u) (hX : X ≤ c * u) : X + d ≤ (c + d) * u := by
  calc X + d ≤ c * u + d * u := by gcongr; exact Nat.le_mul_of_pos_right d (by omega)
    _ = (c + d) * u := by ring

/-- A sum of bounded quantities is bounded by the sum of the bounds. -/
private lemma nat_bound_sum {c d u X Y : ℕ} (hX : X ≤ c * u) (hY : Y ≤ d * u) :
    X + Y ≤ (c + d) * u := by
  calc X + Y ≤ c * u + d * u := by gcongr
    _ = (c + d) * u := by ring

end Bounds

-- The `Finite` instances of the machines that are combined are produced by `obtain`, so they have
-- to be registered as instances with `haveI` even though the goal is a proposition.
set_option linter.style.haveILetI false in
/-- **Complexity of a loop.**

Assume that
* `f` picks, for every input, a value at which the loop terminates (`hf`), and the loop started at
  `a` stops after at most `iterBound a` iterations (`hiter`);
* the loop body is computable in time `t` and space `s` (`hbody`), where `s` also bounds the
  encoded length of all the values encountered while running the loop (`hsize`, which includes `a`
  itself);
* these bounds do not increase along the iterations of the loop (`ht`, `hs`).

Then `f` is computable in time proportional to the number of iterations times the cost of one
iteration, and in space proportional to the space of one iteration.

The machine uses three named work tapes, `T1` holding the current value, `T3` holding the result of
the last call of the body and `T4` holding the flag that says whether the loop is over, plus the
scratch tapes of the machines it runs, which `exists_transformsTapes_ofComputable` hides. It first
copies its input onto `T1` and runs the machine for `body` with `T1` as its input tape and `T3` as
its output tape. Then it repeats: run the machine for `Option.isNone` on `T3`, writing the flag to
`T4`, and branch on the flag; if the loop is over, stop, so that the contents of `T1` can be
emitted; otherwise clear `T4`, clear `T1`, run the destructor of `some` with `T3` as its input and
`T1` as its output, clear `T3` and run the body again with `T1` as its input and `T3` as its
output.

Note that `T1` has to be kept until the result of the body has been inspected, since on exit the
result of the loop is the value that was fed to the last call of the body. Copying the input onto
`T1` before the first call of the body costs only `O(s a)`, since `hsize` bounds the length of the
encoded input.

The space bound of the body alone does not bound the encoded length of the intermediate values: the
input tape is read-only and the output tape is append-only, so neither counts towards the space
bound, and a machine can produce an output much longer than the space it uses. The intermediate
values, however, are stored on a work tape, and hence `hsize` is a genuine additional assumption on
`s`. Since the resulting bounds are stated up to a constant factor, using a single `s` for both
purposes is no weaker than using two separate bounds, whose maximum `s` can be taken to be. -/
public theorem computableInTimeAndSpace_loopFunction
    {α : Type*} {body : α → Option α} {f : α → α}
    {enc : α ↪ List Bool} {encOpt : Option α ↪ List Bool} {t s iterBound : α → ℕ}
    (henc : IsOptionEncoding enc encOpt)
    (hf : ∀ a, f a ∈ loopFunction body a)
    (hiter : ∀ a, ∃ m ≤ iterBound a, loopIterate body m a = none)
    (hsize : ∀ a m x, loopIterate body m a = some x → (enc x).length ≤ s a)
    (hbody : ComputableInTimeAndSpace body enc encOpt t s)
    (ht : ∀ a m x, loopIterate body m a = some x → t x ≤ t a)
    (hs : ∀ a m x, loopIterate body m a = some x → s x ≤ s a) :
    ∃ c, ComputableInTimeAndSpace f enc enc
      (fun a => c * (iterBound a + 1) * (t a + s a + 1))
      (fun a => c * (s a + 1)) := by
  classical
  -- ### The number of iterations
  -- `N a` is the number of iterations after which the loop started at `a` stops, and `f a` is the
  -- value it stops at.
  have hkey : ∀ a, ∃ n, loopIterate body n a = some (f a) ∧ body (f a) = none :=
    fun a => mem_loopFunction_iff.mp (hf a)
  choose N hN hNstop using hkey
  have hNle : ∀ a, N a + 1 ≤ iterBound a := by
    intro a
    obtain ⟨m, hm, hmnone⟩ := hiter a
    have hlt : N a < m := by
      by_contra hcon
      have hcontra := loopIterate_eq_none_of_le (Nat.le_of_not_lt hcon) hmnone
      rw [hN a] at hcontra
      simp at hcontra
    omega
  -- every round before `N a` produces the value the next one starts at
  have hnext : ∀ a n, n < N a → ∀ x, loopIterate body n a = some x →
      ∃ x', body x = some x' ∧ loopIterate body (n + 1) a = some x' := by
    intro a n hn x hx
    have heq : loopIterate body (n + 1) a = body x := by rw [loopIterate_succ', hx]; simp
    have hne : body x ≠ none := by
      rw [← heq]
      exact loopIterate_ne_none_of_le hn (by rw [hN a]; exact Option.some_ne_none _)
    obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.mp hne
    exact ⟨x', hx', by rw [heq, hx']⟩
  -- ### The encoding of the loop flag
  obtain ⟨encBool, hencBoolHead, hencBoolLen⟩ :
      ∃ e : Bool ↪ List Bool, (∀ b, (e b).head? = some b) ∧ ∀ b, (e b).length = 1 :=
    ⟨⟨fun b => [b], fun b₁ b₂ h => by simpa using h⟩, fun _ => rfl, fun _ => rfl⟩
  -- ### Lengths of the encodings encountered along the loop
  obtain ⟨cc, hcc⟩ := henc.constructor_computable
  have hccLen : ∀ x : α, (encOpt (some x)).length ≤ cc * ((enc x).length + 1) :=
    hcc.length_encOut_le
  obtain ⟨E, hE⟩ : ∃ E, ∀ a n x, loopIterate body n a = some x →
      (encOpt (body x)).length ≤ E * (s a + 1) := by
    refine ⟨cc + (encOpt none).length, fun a n x hx => ?_⟩
    rcases hb : body x with _ | x'
    · calc (encOpt none).length ≤ cc + (encOpt none).length := Nat.le_add_left _ _
        _ ≤ (cc + (encOpt none).length) * (s a + 1) :=
            Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    · have hx' : loopIterate body (n + 1) a = some x' := by
        rw [loopIterate_succ', hx]; simpa using hb
      calc (encOpt (some x')).length ≤ cc * ((enc x').length + 1) := hccLen x'
        _ ≤ cc * (s a + 1) := Nat.mul_le_mul_left _ (by have := hsize a (n + 1) x' hx'; omega)
        _ ≤ (cc + (encOpt none).length) * (s a + 1) := Nat.mul_le_mul_right _ (by omega)
  -- ### The machines the loop is assembled from
  obtain ⟨cd, hd⟩ := henc.destructor_computable
  obtain ⟨cn, hisNone⟩ :=
    computableInTimeAndSpace_isNone (α := α) (encOpt := encOpt) (encBool := encBool)
  obtain ⟨ci, hid⟩ := computableInTimeAndSpace_id (α := α) (enc := enc)
  obtain ⟨mB, cB, hB⟩ := exists_transformsTapes_ofComputable hbody
  obtain ⟨mD, cD, hD⟩ := exists_transformsTapes_ofComputable hd
  obtain ⟨mN, cN, hNm⟩ := exists_transformsTapes_ofComputable hisNone
  obtain ⟨mI, cI, hI⟩ := exists_transformsTapes_ofComputableInput hid
  -- the tape layout: `T1` the current value, `T3` the result of the body, `T4` the flag
  obtain ⟨K, T1, T3, T4, hT13, hT14, hT34, hKB, hKD, hKN, hKI⟩ :
      ∃ (K : ℕ) (T1 T3 T4 : Fin K), T1 ≠ T3 ∧ T1 ≠ T4 ∧ T3 ≠ T4 ∧
        mB + 2 ≤ K ∧ mD + 2 ≤ K ∧ mN + 3 ≤ K ∧ mI + 1 ≤ K :=
    ⟨mB + mD + mN + mI + 5, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
      Fin.ne_of_val_ne (by simp), Fin.ne_of_val_ne (by simp), Fin.ne_of_val_ne (by simp),
      by omega, by omega, by omega, by omega⟩
  obtain ⟨SB, hSB, MBody, hMBody⟩ :=
    hB K T1 T3 ∅ hT13 (by simp) (by simp) (by simpa using hKB)
  obtain ⟨SD, hSD, MDestr, hMDestr⟩ :=
    hD K T3 T1 ∅ (Ne.symm hT13) (by simp) (by simp) (by simpa using hKD)
  obtain ⟨SN, hSN, MIsNone, hMIsNone⟩ :=
    hNm K T3 T4 {T1} hT34 (by simpa using Ne.symm hT13) (by simpa using Ne.symm hT14)
      (by simp only [Finset.card_singleton]; omega)
  obtain ⟨SI, hSI, MCopy, hMCopy⟩ := hI K T1 ∅ (by simp) (by simpa using hKI)
  obtain ⟨cC1, SC1, hSC1, MClear1, hMClear1⟩ := exists_transformsTapes_clear T1
  obtain ⟨cC3, SC3, hSC3, MClear3, hMClear3⟩ := exists_transformsTapes_clear T3
  obtain ⟨cC4, SC4, hSC4, MClear4, hMClear4⟩ := exists_transformsTapes_clear T4
  obtain ⟨SNop, hSNop, MNop, hMNop⟩ := exists_transformsTapes_nop K
  haveI := hSB; haveI := hSD; haveI := hSN; haveI := hSI
  haveI := hSC1; haveI := hSC3; haveI := hSC4; haveI := hSNop
  -- ### One constant bounding every length that occurs
  obtain ⟨W, hW1, hWcn, hWci, hWlen⟩ : ∃ W : ℕ, 1 ≤ W ∧ cn ≤ W ∧ ci ≤ W ∧
      ∀ a n x, loopIterate body n a = some x →
        (enc x).length ≤ W * (s a + 1) ∧
        (encOpt (body x)).length ≤ W * (s a + 1) ∧
        (encOpt (some x)).length ≤ W * (s a + 1) ∧
        cd * ((encOpt (some x)).length + 1) ≤ W * (s a + 1) ∧
        s x ≤ W * (s a + 1) ∧ t x ≤ W * (t a + s a + 1) := by
    refine ⟨cn + ci + cc + E + cd * (cc + 1) + 1, by omega, by omega, by omega,
      fun a n x hx => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact le_trans (by have := hsize a n x hx; omega)
        (Nat.le_mul_of_pos_left _ (by omega))
    · exact (hE a n x hx).trans (Nat.mul_le_mul_right _ (by omega))
    · exact (hccLen x).trans ((Nat.mul_le_mul_left _ (by have := hsize a n x hx; omega)).trans
        (Nat.mul_le_mul_right _ (by omega)))
    · have h1 : (encOpt (some x)).length ≤ cc * (s a + 1) :=
        (hccLen x).trans (Nat.mul_le_mul_left _ (by have := hsize a n x hx; omega))
      calc cd * ((encOpt (some x)).length + 1)
          ≤ cd * (cc * (s a + 1) + (s a + 1)) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add h1 (by omega))
        _ = cd * (cc + 1) * (s a + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · exact le_trans (by have := hs a n x hx; omega) (Nat.le_mul_of_pos_left _ (by omega))
    · exact le_trans (by have := ht a n x hx; omega) (Nat.le_mul_of_pos_left _ (by omega))
  -- the two units in which the bounds are measured
  have hu1 : ∀ a, 1 ≤ t a + s a + 1 := fun a => by omega
  have hv1 : ∀ a, 1 ≤ s a + 1 := fun a => by omega
  have hvu : ∀ (a : α) (c : ℕ), c * (s a + 1) ≤ c * (t a + s a + 1) :=
    fun a c => Nat.mul_le_mul_left _ (by omega)
  -- ### Descriptions of the tape contents at the various points of a round
  obtain ⟨Both, hBoth⟩ : ∃ P : α → Option α → (Fin K → List Bool) → Prop, ∀ y v ws, P y v ws ↔
      (ws T1 = enc y ∧ ws T3 = encOpt v ∧ ∀ l, l ≠ T1 → l ≠ T3 → ws l = []) :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨Only1, hOnly1⟩ : ∃ P : α → (Fin K → List Bool) → Prop, ∀ y ws, P y ws ↔
      (ws T1 = enc y ∧ ∀ l, l ≠ T1 → ws l = []) := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨Only3, hOnly3⟩ : ∃ P : Option α → (Fin K → List Bool) → Prop, ∀ v ws, P v ws ↔
      (ws T3 = encOpt v ∧ ∀ l, l ≠ T3 → ws l = []) := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨InvMid, hInvMid⟩ : ∃ P : α → (Fin K → List Bool) → Prop, ∀ y ws, P y ws ↔
      (ws T1 = enc y ∧ ws T3 = encOpt (body y) ∧ ws T4 = encBool (body y).isNone ∧
        ∀ l, l ≠ T1 → l ≠ T3 → l ≠ T4 → ws l = []) := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨Pround, hPround⟩ : ∃ P : α → ℕ → (Fin K → List Bool) → Prop, ∀ a n ws, P a n ws ↔
      (∃ y, loopIterate body n a = some y ∧ Both y (body y) ws) := ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨PMid, hPMid⟩ : ∃ P : α → ℕ → (Fin K → List Bool) → Prop, ∀ a n ws, P a n ws ↔
      (∃ y, loopIterate body n a = some y ∧ InvMid y ws) := ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨PExit, hPExit⟩ : ∃ P : α → ℕ → (Fin K → List Bool) → Prop, ∀ a n ws, P a n ws ↔
      (∃ y, loopIterate body n a = some y ∧ body y = none ∧ InvMid y ws) :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨PCont, hPCont⟩ : ∃ P : α → ℕ → (Fin K → List Bool) → Prop, ∀ a n ws, P a n ws ↔
      (∃ y y', loopIterate body n a = some y ∧ body y = some y' ∧ InvMid y ws) :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨QR, hQR⟩ : ∃ Q : α → ℕ → (Fin K → List Bool) → Prop, ∀ a n ws', Q a n ws' ↔
      ((∀ y, loopIterate body n a = some y → body y = none →
          ws' T1 = enc y ∧ (ws' T4).head? = some true) ∧
       (∀ y y', loopIterate body n a = some y → body y = some y' →
          Both y' (body y') ws' ∧ (ws' T4).head? ≠ some true)) := ⟨_, fun _ _ _ => Iff.rfl⟩
  -- ### Bounds for the individual machines
  -- Every length occurring in the bound of a machine of a round is bounded by `W * (s a + 1)`,
  -- hence its time by a constant times `t a + s a + 1` and its space by a constant times `s a + 1`.
  have hWt : ∀ a n x, loopIterate body n a = some x →
      (enc x).length ≤ W * (t a + s a + 1) ∧
      (encOpt (body x)).length ≤ W * (t a + s a + 1) ∧
      (encOpt (some x)).length ≤ W * (t a + s a + 1) ∧
      cd * ((encOpt (some x)).length + 1) ≤ W * (t a + s a + 1) ∧
      s x ≤ W * (t a + s a + 1) ∧ t x ≤ W * (t a + s a + 1) := by
    intro a n x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hWlen a n x hx
    exact ⟨h1.trans (hvu a W), h2.trans (hvu a W), h3.trans (hvu a W), h4.trans (hvu a W),
      h5.trans (hvu a W), h6⟩
  have hcW : ∀ (c : ℕ) (a : α), c ≤ W → c ≤ W * (t a + s a + 1) := fun c a hc =>
    hc.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hcWv : ∀ (c : ℕ) (a : α), c ≤ W → c ≤ W * (s a + 1) := fun c a hc =>
    hc.trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨A1, hA1⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cN * (cn + (encOpt (body x)).length + (encBool (body x).isNone).length + 1)
        ≤ c * (t a + s a + 1) := by
    refine ⟨cN * (3 * W + 1), fun a n x hx => ?_⟩
    rw [hencBoolLen]
    exact nat_bound₃ (hu1 a) (hcW cn a hWcn) (hWt a n x hx).2.1 (hcW 1 a hW1)
  obtain ⟨A2, hA2⟩ : ∃ c, ∀ (a : α) (b : Bool),
      cC4 * ((encBool b).length + 1) ≤ c * (t a + s a + 1) := by
    refine ⟨cC4 * (W + 1), fun a b => ?_⟩
    rw [hencBoolLen]
    exact nat_bound₁ (hu1 a) (hcW 1 a hW1)
  obtain ⟨A3, hA3⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cC1 * ((enc x).length + 1) ≤ c * (t a + s a + 1) :=
    ⟨cC1 * (W + 1), fun a n x hx => nat_bound₁ (hu1 a) (hWt a n x hx).1⟩
  obtain ⟨A4, hA4⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cD * (cd * ((encOpt (some x)).length + 1) + (encOpt (some x)).length + (enc x).length + 1)
        ≤ c * (t a + s a + 1) :=
    ⟨cD * (3 * W + 1), fun a n x hx =>
      nat_bound₃ (hu1 a) (hWt a n x hx).2.2.2.1 (hWt a n x hx).2.2.1 (hWt a n x hx).1⟩
  obtain ⟨A5, hA5⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cC3 * ((encOpt (some x)).length + 1) ≤ c * (t a + s a + 1) :=
    ⟨cC3 * (W + 1), fun a n x hx => nat_bound₁ (hu1 a) (hWt a n x hx).2.2.1⟩
  obtain ⟨A6, hA6⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cB * (t x + (enc x).length + (encOpt (body x)).length + 1) ≤ c * (t a + s a + 1) :=
    ⟨cB * (3 * W + 1), fun a n x hx =>
      nat_bound₃ (hu1 a) (hWt a n x hx).2.2.2.2.2 (hWt a n x hx).1 (hWt a n x hx).2.1⟩
  obtain ⟨A7, hA7⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cI * (ci * ((enc x).length + 1) + (enc x).length + 1) ≤ c * (t a + s a + 1) := by
    refine ⟨cI * (2 * W + 1), fun a n x hx => nat_bound₂ (hu1 a) ?_ (hWt a n x hx).1⟩
    calc ci * ((enc x).length + 1) ≤ ci * (s a + 1) :=
          Nat.mul_le_mul_left _ (by have := hsize a n x hx; omega)
      _ ≤ W * (s a + 1) := Nat.mul_le_mul_right _ hWci
      _ ≤ W * (t a + s a + 1) := hvu a W
  obtain ⟨B1, hB1⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cN * (0 + (encOpt (body x)).length + (encBool (body x).isNone).length + 1) + K
        ≤ c * (s a + 1) := by
    refine ⟨cN * (3 * W + 1) + K, fun a n x hx => nat_bound_add (hv1 a) ?_⟩
    rw [hencBoolLen]
    exact nat_bound₃ (hv1 a) (hcWv 0 a (by omega)) (hWlen a n x hx).2.1 (hcWv 1 a hW1)
  obtain ⟨B2, hB2⟩ : ∃ c, ∀ (a : α) (w : List Bool), w.length ≤ W * (s a + 1) →
      w.length + 1 + K ≤ c * (s a + 1) :=
    ⟨W + 1 + K, fun a w hw => nat_bound_add (hv1 a) (nat_bound₀ (hv1 a) hw)⟩
  obtain ⟨B3, hB3⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cD * (0 + (encOpt (some x)).length + (enc x).length + 1) + K ≤ c * (s a + 1) :=
    ⟨cD * (3 * W + 1) + K, fun a n x hx => nat_bound_add (hv1 a)
      (nat_bound₃ (hv1 a) (hcWv 0 a (by omega)) (hWlen a n x hx).2.2.1 (hWlen a n x hx).1)⟩
  obtain ⟨B4, hB4⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cB * (s x + (enc x).length + (encOpt (body x)).length + 1) + K ≤ c * (s a + 1) :=
    ⟨cB * (3 * W + 1) + K, fun a n x hx => nat_bound_add (hv1 a)
      (nat_bound₃ (hv1 a) (hWlen a n x hx).2.2.2.2.1 (hWlen a n x hx).1
        (hWlen a n x hx).2.1)⟩
  obtain ⟨B5, hB5⟩ : ∃ c, ∀ a n x, loopIterate body n a = some x →
      cI * (0 + (enc x).length + 1) + K ≤ c * (s a + 1) :=
    ⟨cI * (2 * W + 1) + K, fun a n x hx => nat_bound_add (hv1 a)
      (nat_bound₂ (hv1 a) (hcWv 0 a (by omega)) (hWlen a n x hx).1)⟩
  -- the cost of one round, and of the whole loop
  set A : ℕ := A1 + A2 + A3 + A4 + A5 + A6 + A7 + 1 with hAdef
  set B : ℕ := B1 + 3 * B2 + B3 + B4 + B5 + K + 1 with hBdef
  -- ### The exit branch: the loop is over, so nothing is left to do
  have hExit : ∀ p : α × ℕ, TransformsTapes MNop (fun _ ws => PExit p.1 p.2 ws)
      (fun _ _ ws' => QR p.1 p.2 ws') (A * (t p.1 + s p.1 + 1)) (B * (s p.1 + 1)) := by
    rintro ⟨a, n⟩
    refine hMNop.imp (fun _ _ _ => trivial) (fun _ ws ws' hP hQ => ?_) ?_ ?_
    · rw [hQ]
      obtain ⟨y, hy, hby, hmid⟩ := (hPExit a n ws).mp hP
      obtain ⟨e1, e3, e4, erest⟩ := (hInvMid y ws).mp hmid
      refine (hQR a n ws).mpr ⟨fun z hz _ => ?_, fun z z' hz hbz => ?_⟩
      · rw [hy] at hz
        obtain rfl : z = y := (Option.some.inj hz).symm
        exact ⟨e1, by rw [e4, hby, hencBoolHead]; simp⟩
      · rw [hy] at hz
        obtain rfl : z = y := (Option.some.inj hz).symm
        rw [hby] at hbz
        exact absurd hbz (by simp)
    · calc (1 : ℕ) ≤ 1 * (t a + s a + 1) := by omega
        _ ≤ A * (t a + s a + 1) := Nat.mul_le_mul_right _ (by omega)
    · calc K ≤ K * (s a + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ B * (s a + 1) := Nat.mul_le_mul_right _ (by omega)
  -- ### The continuation branch: one more iteration of the loop body
  have hCont : ∀ p : α × ℕ, TransformsTapes
      (MClear4.seq (MClear1.seq (MDestr.seq (MClear3.seq MBody))))
      (fun _ ws => PCont p.1 p.2 ws) (fun _ _ ws' => QR p.1 p.2 ws')
      (A * (t p.1 + s p.1 + 1)) (B * (s p.1 + 1)) := by
    rintro ⟨a, n⟩
    rcases hit : loopIterate body n a with _ | x
    · intro input ws cfg _ _ _ hP
      obtain ⟨y, y', hy, _, _⟩ := (hPCont a n ws).mp hP
      rw [hit] at hy
      exact absurd hy (by simp)
    rcases hb : body x with _ | x'
    · intro input ws cfg _ _ _ hP
      obtain ⟨y, y', hy, hby, _⟩ := (hPCont a n ws).mp hP
      rw [hit] at hy
      obtain rfl : y = x := (Option.some.inj hy).symm
      rw [hb] at hby
      exact absurd hby (by simp)
    have hx' : loopIterate body (n + 1) a = some x' := by
      rw [loopIterate_succ', hit]; simpa using hb
    have hPC : ∀ ws, PCont a n ws → InvMid x ws := by
      intro ws hP
      obtain ⟨y, y', hy, _, hmid⟩ := (hPCont a n ws).mp hP
      rw [hit] at hy
      obtain rfl : y = x := (Option.some.inj hy).symm
      exact hmid
    -- clear the flag tape
    have step4 : TransformsTapes MClear4 (fun _ ws => PCont a n ws)
        (fun _ _ ws' => Both x (some x') ws')
        (cC4 * ((encBool (body x).isNone).length + 1))
        ((encBool (body x).isNone).length + 1 + K) := by
      refine (hMClear4 (encBool (body x).isNone)).imp
        (fun _ ws hP => ((hInvMid x ws).mp (hPC ws hP)).2.2.1)
        (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      obtain ⟨e1, e3, e4, erest⟩ := (hInvMid x ws).mp (hPC ws hP)
      refine (hBoth x (some x') ws').mpr ⟨by rw [hQ.2 T1 hT14, e1], by rw [hQ.2 T3 hT34, e3, hb],
        fun l hl1 hl3 => ?_⟩
      by_cases hl4 : l = T4
      · subst hl4; exact hQ.1
      · rw [hQ.2 l hl4]; exact erest l hl1 hl3 hl4
    -- clear the tape holding the current value
    have step1 : TransformsTapes MClear1 (fun _ ws => Both x (some x') ws)
        (fun _ _ ws' => Only3 (some x') ws')
        (cC1 * ((enc x).length + 1)) ((enc x).length + 1 + K) := by
      refine (hMClear1 (enc x)).imp (fun _ ws hP => ((hBoth x (some x') ws).mp hP).1)
        (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      obtain ⟨e1, e3, erest⟩ := (hBoth x (some x') ws).mp hP
      refine (hOnly3 (some x') ws').mpr ⟨by rw [hQ.2 T3 (Ne.symm hT13), e3], fun l hl3 => ?_⟩
      by_cases hl1 : l = T1
      · subst hl1; exact hQ.1
      · rw [hQ.2 l hl1]; exact erest l hl1 hl3
    -- extract the new value from the result of the body
    have stepD : TransformsTapes MDestr (fun _ ws => Only3 (some x') ws)
        (fun _ _ ws' => Both x' (some x') ws')
        (cD * (cd * ((encOpt (some x')).length + 1) + (encOpt (some x')).length
          + (enc x').length + 1))
        (cD * (0 + (encOpt (some x')).length + (enc x').length + 1) + K) := by
      refine (hMDestr x').imp (fun _ ws hP => ?_) (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      · obtain ⟨e3, erest⟩ := (hOnly3 (some x') ws).mp hP
        exact ⟨e3, fun l hl3 _ => erest l hl3⟩
      · obtain ⟨f3, f1, _, frest⟩ := hQ
        exact (hBoth x' (some x') ws').mpr ⟨f1, f3, fun l hl1 hl3 => frest l hl3 hl1 (by simp)⟩
    -- clear the tape holding the result of the body
    have step3 : TransformsTapes MClear3 (fun _ ws => Both x' (some x') ws)
        (fun _ _ ws' => Only1 x' ws')
        (cC3 * ((encOpt (some x')).length + 1)) ((encOpt (some x')).length + 1 + K) := by
      refine (hMClear3 (encOpt (some x'))).imp
        (fun _ ws hP => ((hBoth x' (some x') ws).mp hP).2.1)
        (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      obtain ⟨e1, e3, erest⟩ := (hBoth x' (some x') ws).mp hP
      refine (hOnly1 x' ws').mpr ⟨by rw [hQ.2 T1 hT13, e1], fun l hl1 => ?_⟩
      by_cases hl3 : l = T3
      · subst hl3; exact hQ.1
      · rw [hQ.2 l hl3]; exact erest l hl1 hl3
    -- run the body on the new value
    have stepB : TransformsTapes MBody (fun _ ws => Only1 x' ws)
        (fun _ _ ws' => Both x' (body x') ws' ∧ ws' T4 = [])
        (cB * (t x' + (enc x').length + (encOpt (body x')).length + 1))
        (cB * (s x' + (enc x').length + (encOpt (body x')).length + 1) + K) := by
      refine (hMBody x').imp (fun _ ws hP => ?_) (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      · obtain ⟨e1, erest⟩ := (hOnly1 x' ws).mp hP
        exact ⟨e1, fun l hl1 _ => erest l hl1⟩
      · obtain ⟨f1, f3, _, frest⟩ := hQ
        exact ⟨(hBoth x' (body x') ws').mpr ⟨f1, f3, fun l hl1 hl3 => frest l hl1 hl3 (by simp)⟩,
          frest T4 (Ne.symm hT14) (Ne.symm hT34) (by simp)⟩
    refine (transformsTapes_seq step4 (transformsTapes_seq step1 (transformsTapes_seq stepD
      (transformsTapes_seq step3 stepB (fun _ _ _ _ h => h)) (fun _ _ _ _ h => h))
      (fun _ _ _ _ h => h)) (fun _ _ _ _ h => h)).imp (fun _ _ h => h)
      (fun _ ws ws' hP hQ => ?_) ?_ ?_
    · obtain ⟨w1, -, w2, -, w3, -, w4, -, hfin, hT4z⟩ := hQ
      refine (hQR a n ws').mpr ⟨fun z hz hbz => ?_, fun z z' hz hbz => ?_⟩
      · rw [hit] at hz
        obtain rfl : z = x := (Option.some.inj hz).symm
        rw [hb] at hbz
        exact absurd hbz (by simp)
      · rw [hit] at hz
        obtain rfl : z = x := (Option.some.inj hz).symm
        rw [hb] at hbz
        obtain rfl : z' = x' := (Option.some.inj hbz).symm
        exact ⟨hfin, by rw [hT4z]; simp⟩
    · have e2 := hA2 a (body x).isNone
      have e3 := hA3 a n x hit
      have e4 := hA4 a (n + 1) x' hx'
      have e5 := hA5 a (n + 1) x' hx'
      have e6 := hA6 a (n + 1) x' hx'
      calc _ ≤ A2 * (t a + s a + 1) + (A3 * (t a + s a + 1) + (A4 * (t a + s a + 1)
              + (A5 * (t a + s a + 1) + A6 * (t a + s a + 1)))) :=
            Nat.add_le_add e2 (Nat.add_le_add e3 (Nat.add_le_add e4 (Nat.add_le_add e5 e6)))
        _ = (A2 + A3 + A4 + A5 + A6) * (t a + s a + 1) := by ring
        _ ≤ A * (t a + s a + 1) := Nat.mul_le_mul_right _ (by omega)
    · have g2 := hB2 a (encBool (body x).isNone) (by rw [hencBoolLen]; exact hcWv 1 a hW1)
      have g3 := hB2 a (enc x) (hWlen a n x hit).1
      have g4 := hB3 a (n + 1) x' hx'
      have g5 := hB2 a (encOpt (some x')) (hWlen a (n + 1) x' hx').2.2.1
      have g6 := hB4 a (n + 1) x' hx'
      calc _ ≤ B2 * (s a + 1) + (B2 * (s a + 1) + (B3 * (s a + 1)
              + (B2 * (s a + 1) + B4 * (s a + 1)))) :=
            Nat.add_le_add g2 (Nat.add_le_add g3 (Nat.add_le_add g4 (Nat.add_le_add g5 g6)))
        _ = (B2 + B2 + B3 + B2 + B4) * (s a + 1) := by ring
        _ ≤ B * (s a + 1) := Nat.mul_le_mul_right _ (by omega)
  -- ### One round: compute the flag on `T4` and branch on it
  obtain ⟨SBr, hSBr, MBranch, hMBranch⟩ :=
    exists_transformsTapes_branch (J := α × ℕ) T4 true
      (P₁ := fun p _ ws => PExit p.1 p.2 ws) (P₂ := fun p _ ws => PCont p.1 p.2 ws)
      (Q := fun p _ _ ws' => QR p.1 p.2 ws')
      (t₁ := fun p => A * (t p.1 + s p.1 + 1)) (s₁ := fun p => B * (s p.1 + 1))
      (t₂ := fun p => A * (t p.1 + s p.1 + 1)) (s₂ := fun p => B * (s p.1 + 1)) hExit hCont
  haveI := hSBr
  set A' : ℕ := A1 + A + 1 with hA'def
  set B' : ℕ := B1 + B + K + 1 with hB'def
  have hRound : ∀ (a : α) (n : ℕ), TransformsTapes (MIsNone.seq MBranch)
      (fun _ ws => Pround a n ws) (fun _ _ ws' => QR a n ws')
      (A' * (t a + s a + 1)) (B' * (s a + 1)) := by
    intro a n
    rcases hit : loopIterate body n a with _ | x
    · intro input ws cfg _ _ _ hP
      obtain ⟨y, hy, _⟩ := (hPround a n ws).mp hP
      rw [hit] at hy
      exact absurd hy (by simp)
    have stepN : TransformsTapes MIsNone (fun _ ws => Pround a n ws)
        (fun _ _ ws' => PMid a n ws')
        (cN * (cn + (encOpt (body x)).length + (encBool (body x).isNone).length + 1))
        (cN * (0 + (encOpt (body x)).length + (encBool (body x).isNone).length + 1) + K) := by
      refine (hMIsNone (body x)).imp (fun _ ws hP => ?_) (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      · obtain ⟨y, hy, hbb⟩ := (hPround a n ws).mp hP
        rw [hit] at hy
        obtain rfl : y = x := (Option.some.inj hy).symm
        obtain ⟨e1, e3, erest⟩ := (hBoth y (body y) ws).mp hbb
        exact ⟨e3, fun l hl3 hl1 => erest l (by simpa using hl1) hl3⟩
      · obtain ⟨y, hy, hbb⟩ := (hPround a n ws).mp hP
        rw [hit] at hy
        obtain rfl : y = x := (Option.some.inj hy).symm
        obtain ⟨e1, e3, erest⟩ := (hBoth y (body y) ws).mp hbb
        obtain ⟨f3, f4, fkeep, frest⟩ := hQ
        exact (hPMid a n ws').mpr ⟨y, hit, (hInvMid y ws').mpr
          ⟨by rw [fkeep T1 (by simp), e1], f3, f4,
            fun l hl1 hl3 hl4 => frest l hl3 hl4 (by simpa using hl1)⟩⟩
    refine (transformsTapes_seq stepN (hMBranch (a, n)) (fun _ ws ws' hP hQ => ?_)).imp
      (fun _ _ h => h) (fun _ ws ws' hP hQ => ?_) ?_ ?_
    · -- the flag decides which branch is taken
      obtain ⟨y, hy, hmid⟩ := (hPMid a n ws').mp hQ
      obtain ⟨e1, e3, e4, erest⟩ := (hInvMid y ws').mp hmid
      by_cases hflag : (ws' T4).head? = some true
      · rw [ite_eq_left hflag]
        rw [e4, hencBoolHead] at hflag
        exact (hPExit a n ws').mpr ⟨y, hy, by simpa using hflag, hmid⟩
      · rw [ite_eq_right hflag]
        rcases hby : body y with _ | y'
        · exact absurd (by rw [e4, hby, hencBoolHead]; simp) hflag
        · exact (hPCont a n ws').mpr ⟨y, y', hy, hby, hmid⟩
    · obtain ⟨w1, -, h2⟩ := hQ
      exact h2
    · simp only [max_self]
      have e1 := hA1 a n x hit
      calc _ ≤ A1 * (t a + s a + 1) + (A * (t a + s a + 1) + 1 * (t a + s a + 1)) :=
            Nat.add_le_add e1 (Nat.add_le_add le_rfl (by omega))
        _ = (A1 + A + 1) * (t a + s a + 1) := by ring
        _ ≤ A' * (t a + s a + 1) := Nat.mul_le_mul_right _ (by omega)
    · simp only [max_self]
      have g1 := hB1 a n x hit
      calc _ ≤ B1 * (s a + 1) + (B * (s a + 1) + K * (s a + 1)) :=
            Nat.add_le_add g1 (Nat.add_le_add le_rfl (Nat.le_mul_of_pos_right _ (by omega)))
        _ = (B1 + B + K) * (s a + 1) := by ring
        _ ≤ B' * (s a + 1) := Nat.mul_le_mul_right _ (by omega)
  -- ### The loop: repeat the round until the flag says that the loop is over
  have hroundOK : ∀ (a : α) (n : ℕ), n < N a → TransformsTapes (MIsNone.seq MBranch)
      (fun _ ws => Pround a n ws)
      (fun _ _ ws' => Pround a (n + 1) ws' ∧ (ws' T4).head? ≠ some true)
      (A' * (t a + s a + 1)) (B' * (s a + 1)) := by
    intro a n hn
    refine (hRound a n).imp (fun _ _ h => h) (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
    obtain ⟨y, hy, -⟩ := (hPround a n ws).mp hP
    obtain ⟨y', hby, hy'⟩ := hnext a n hn y hy
    obtain ⟨-, q2⟩ := (hQR a n ws').mp hQ
    obtain ⟨hb', hflag⟩ := q2 y y' hy hby
    exact ⟨(hPround a (n + 1) ws').mpr ⟨y', hy', hb'⟩, hflag⟩
  have hstopOK : ∀ a : α, TransformsTapes (MIsNone.seq MBranch)
      (fun _ ws => Pround a (N a) ws)
      (fun _ _ ws' => ws' T1 = enc (f a) ∧ (ws' T4).head? = some true)
      (A' * (t a + s a + 1)) (B' * (s a + 1)) := by
    intro a
    refine (hRound a (N a)).imp (fun _ _ h => h) (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
    exact ((hQR a (N a) ws').mp hQ).1 (f a) (hN a) (hNstop a)
  obtain ⟨SL, hSL, MLoop, hMLoop⟩ :=
    exists_transformsTapes_repeat (J := α) T4 true
      (P := fun a n _ ws => Pround a n ws) (R := fun a _ ws' => ws' T1 = enc (f a))
      (N := N) (t := fun a => A' * (t a + s a + 1)) (s := fun a => B' * (s a + 1))
      hroundOK hstopOK
  haveI := hSL
  -- ### The prologue: copy the input onto `T1` and run the body once
  have hPro : ∀ a : α, TransformsTapes (MCopy.seq MBody)
      (fun input ws => input = enc a ∧ ∀ l, ws l = [])
      (fun _ _ ws' => Pround a 0 ws') (A * (t a + s a + 1)) (B * (s a + 1)) := by
    intro a
    have s1 : TransformsTapes MCopy (fun input ws => input = enc a ∧ ∀ l, ws l = [])
        (fun _ _ ws' => Only1 a ws')
        (cI * (ci * ((enc a).length + 1) + (enc a).length + 1))
        (cI * (0 + (enc a).length + 1) + K) := by
      refine (hMCopy a).imp (fun _ ws hP => ⟨hP.1, fun l _ => hP.2 l⟩)
        (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      obtain ⟨f1, -, frest⟩ := hQ
      exact (hOnly1 a ws').mpr ⟨f1, fun l hl1 => frest l hl1 (by simp)⟩
    have s2 : TransformsTapes MBody (fun _ ws => Only1 a ws)
        (fun _ _ ws' => Pround a 0 ws')
        (cB * (t a + (enc a).length + (encOpt (body a)).length + 1))
        (cB * (s a + (enc a).length + (encOpt (body a)).length + 1) + K) := by
      refine (hMBody a).imp (fun _ ws hP => ?_) (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
      · obtain ⟨e1, erest⟩ := (hOnly1 a ws).mp hP
        exact ⟨e1, fun l hl1 _ => erest l hl1⟩
      · obtain ⟨f1, f3, -, frest⟩ := hQ
        exact (hPround a 0 ws').mpr ⟨a, rfl, (hBoth a (body a) ws').mpr
          ⟨f1, f3, fun l hl1 hl3 => frest l hl1 hl3 (by simp)⟩⟩
    refine (transformsTapes_seq s1 s2 (fun _ _ _ _ h => h)).imp (fun _ _ h => h)
      (fun _ ws ws' hP hQ => ?_) ?_ ?_
    · obtain ⟨w1, -, h2⟩ := hQ
      exact h2
    · calc _ ≤ A7 * (t a + s a + 1) + A6 * (t a + s a + 1) :=
            Nat.add_le_add (hA7 a 0 a rfl) (hA6 a 0 a rfl)
        _ = (A7 + A6) * (t a + s a + 1) := by ring
        _ ≤ A * (t a + s a + 1) := Nat.mul_le_mul_right _ (by omega)
    · calc _ ≤ B5 * (s a + 1) + B4 * (s a + 1) :=
            Nat.add_le_add (hB5 a 0 a rfl) (hB4 a 0 a rfl)
        _ = (B5 + B4) * (s a + 1) := by ring
        _ ≤ B * (s a + 1) := Nat.mul_le_mul_right _ (by omega)
  -- ### The whole machine
  have hMain : ∀ a : α, TransformsTapes ((MCopy.seq MBody).seq MLoop)
      (fun input ws => input = enc a ∧ ∀ l, ws l = [])
      (fun _ _ ws' => ws' T1 = enc (f a))
      (A * (t a + s a + 1) + (N a + 1) * (A' * (t a + s a + 1) + 1))
      (B * (s a + 1) + (2 * K * (B' * (s a + 1)) + K)) := by
    intro a
    refine (transformsTapes_seq (hPro a) (hMLoop a) (fun _ _ _ _ h => h)).imp (fun _ _ h => h)
      (fun _ ws ws' hP hQ => ?_) le_rfl le_rfl
    obtain ⟨w1, -, h2⟩ := hQ
    exact h2
  obtain ⟨c₀, hc₀⟩ := computableInTimeAndSpace_of_transformsTapes T1 hMain
  -- ### The final bounds
  refine ⟨c₀ * (A + A' + 2) + c₀ * (B + 2 * K * B' + K + 2), hc₀.mono (fun a => ?_) (fun a => ?_)⟩
  · have hl : (enc (f a)).length ≤ s a := hsize a (N a) (f a) (hN a)
    have h1 : (N a + 1) * (A' * (t a + s a + 1) + 1)
        ≤ iterBound a * ((A' + 1) * (t a + s a + 1)) := by
      refine Nat.mul_le_mul (hNle a) ?_
      calc A' * (t a + s a + 1) + 1 ≤ A' * (t a + s a + 1) + (t a + s a + 1) := by omega
        _ = (A' + 1) * (t a + s a + 1) := by ring
    have hkey : A + iterBound a * (A' + 1) + 2 ≤ (A + A' + 2) * (iterBound a + 1) := by
      have hm1 : iterBound a * (A' + 1) ≤ (A + A' + 2) * iterBound a := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right _ (by omega)
      have hm2 : (A + A' + 2) * (iterBound a + 1)
          = (A + A' + 2) * iterBound a + (A + A' + 2) := by ring
      omega
    calc c₀ * (A * (t a + s a + 1) + (N a + 1) * (A' * (t a + s a + 1) + 1)
            + (enc (f a)).length + 1)
        ≤ c₀ * (A * (t a + s a + 1) + iterBound a * ((A' + 1) * (t a + s a + 1))
            + (t a + s a + 1) + (t a + s a + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = c₀ * ((A + iterBound a * (A' + 1) + 2) * (t a + s a + 1)) := by ring
      _ ≤ c₀ * (((A + A' + 2) * (iterBound a + 1)) * (t a + s a + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hkey)
      _ = c₀ * (A + A' + 2) * (iterBound a + 1) * (t a + s a + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · have hl : (enc (f a)).length ≤ s a := hsize a (N a) (f a) (hN a)
    have hK1 : K ≤ K * (s a + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc c₀ * (B * (s a + 1) + (2 * K * (B' * (s a + 1)) + K) + (enc (f a)).length + 1)
        ≤ c₀ * (B * (s a + 1) + (2 * K * (B' * (s a + 1)) + K * (s a + 1))
            + (s a + 1) + (s a + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = c₀ * (B + 2 * K * B' + K + 2) * (s a + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end Turing.MultiTapeTM
