/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Branch

/-!
# Complexity of a case analysis

A case analysis runs a machine that says which case holds and then continues with the machine for
that case. This file has one primitive, `computableInTimeAndSpace_match`, which does exactly that
for a scrutinee in an arbitrary finite type; `cond`, `ite` and `dite` are the instances at `Bool`.

## Why the finite case is the primitive and not the binary one

Lean's `ite` is not primitive: `ite c t e` is `Decidable.casesOn`, the recursor of the two
constructor inductive `Decidable c`, whose constructors carry only proofs. Since `Prop` is erased,
the computational content of `ite` is exactly the recursor of `Bool`, and a `match` on a finite
inductive type is that recursor nested once per constructor. So `Bool.rec` is the primitive of the
*elaborator*.

It is not the right primitive here, because a machine does not nest. Deciding among `n` cases is
one machine reading a scrutinee of constant length and dispatching from its finite control, which
is no harder than deciding among two; the nesting is a fiction that the machine never performs.
Building the finite case analysis out of the binary one therefore does not decompose it into
anything simpler — it only replays `n - 1` copies of the same argument, and each replay multiplies
the constants, so the bounds have to be renormalised into a fixed shape at every step to make the
induction go through. Taking the finite case as the primitive deletes all of that: what remains of
the arithmetic is three weakenings.

The two are equivalent up to constant factors in both directions, so there is no loss. Tests for
individual cases, which is what the binary form consumes, and the tag itself, which is what this
one consumes, are interderivable at constant cost: the tag gives every test by one composition
with a function on a finite type, and the tests give the tag by running all `n` of them. There is
consequently no reason to state both.

## Why this has to be a combinator

`cond` is a perfectly ordinary computable *function*: as a map `Bool × β × β → β` it reads a tag
and streams out the component it selects, in linear time and no space. But that function does not
give the case analysis, because

```
fun a => if c a then f a else g a  =  cond ∘ (fun a => (c a, f a, g a))
```

computes *both* `f a` and `g a`. That costs `tf + tg` instead of `max tf tg`, it stores both
encoded results on work tapes, and — the real problem — nesting `n` conditionals evaluates `2 ^ n`
branches instead of `n`. The content of a case analysis is that the branch not taken is never run,
and that laziness is not expressible by composing total functions: the machine has to choose before
it runs, which is why this is a combinator with a machine-level branch behind it and not a
consequence of `computableInTimeAndSpace_comp`.

## The streaming dispatch

The space bound has no time term in it — a machine computing all the branches would have to park
their encoded outputs on work tapes, and an output's length is bounded only by the time that
produced it, so its space would be `s a + t a`. What buys the pure `s a` is that the branch taken
emits its result *straight to the real output tape*, never parking it. That is why the branch is
run by the streaming dispatch `exists_branch_run`, whose arm is allowed to emit, rather than by the
output-preserving `computableInTimeAndSpace_of_transformsTapes`. The scrutinee, by contrast, ranges
over finitely many values whose encodings have a constant bound on their length, so materialising
it on a work tape costs only `O(1)` space; here it is a single symbol.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_match`: the primitive, a case analysis on a
  scrutinee in a finite type. See `CslibTests.Complexity.Combinators` for worked examples.
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

/-- A run of a machine placed by `extendTapes` on tapes that are blank on its range mirrors the
run of the underlying machine, seen through the tape embedding. This is the decomposition of a
word configuration into an embedded configuration: the tapes in the range carry the machine's own
(here blank) words, the tapes outside it are carried through as extra tapes. -/
private lemma wordsCfg_eq_embed {k kr : ℕ} {Sr : Type}
    (tmr : MultiTapeTM kr Bool Sr) (er : Fin kr ↪ Fin k) (input : List Bool)
    (ws : Fin k → List Bool) (out : List Bool) (hblank : ∀ j, ws (er j) = []) :
    wordsCfg input (some (extendTapes tmr er).q₀) ws out =
      embed er (wordsCfg input (some tmr.q₀) (fun _ => []) out)
        (fun l => tapeOfList (ws l)) (fun _ => 0) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext l
    rcases hp : partialInv er l with _ | j
    · simp only [embed, hp, wordsCfg]
    · rw [← partialInv_eq_some er hp, embed_workTapes_embed]
      simp only [wordsCfg, hblank j]
  · funext l
    rcases hp : partialInv er l with _ | j
    · simp only [embed, hp, wordsCfg]
    · rw [← partialInv_eq_some er hp, embed_workTapePos_embed]
      simp only [wordsCfg]

/-- **Phase two of the case analysis: run the chosen arm to completion.** Given the streaming
dispatch's guarantee for one arm — that after the dispatch step the combined machine's output,
halting and space are the embedded arm's — and the underlying arm machine's own guarantee that it
halts with the encoded result, the dispatch halts with that result on the output tape, in one more
step than the arm, using at most the arm's space plus twice the layout size. -/
private lemma exists_arm_run {k kr : ℕ} {Sr Sd : Type} [Finite Sr]
    {tmr : MultiTapeTM kr Bool Sr} {er : Fin kr ↪ Fin k}
    {tmd : MultiTapeTM k Bool Sd} {input : List Bool} {ws' : Fin k → List Bool}
    {O : List Bool} {τ_br s_br : ℕ}
    (hblank : ∀ j, ws' (er j) = [])
    (harm :
      (tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1)).output =
          ((extendTapes tmr er).runFrom
            (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br).output ∧
      ((tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1)).state = none ↔
          ((extendTapes tmr er).runFrom
            (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br).state = none) ∧
      tmd.spaceUsed (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1) ≤
          (extendTapes tmr er).spaceUsed
            (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br + k)
    (hhalt : (tmr.runFrom (tmr.initCfg input) τ_br).state = none)
    (hout : (tmr.runFrom (tmr.initCfg input) τ_br).output = O)
    (hsp : tmr.spaceUsed (tmr.initCfg input) τ_br ≤ s_br) :
    ∃ u₂ ≤ τ_br + 1,
      (tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) u₂).state = none ∧
      (∀ m < u₂, (tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) m).state ≠ none) ∧
      (tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) u₂).output = O ∧
      tmd.spaceUsed (wordsCfg input (some tmd.q₀) ws' []) u₂ ≤ s_br + 2 * k := by
  have hinit : tmr.initCfg input = wordsCfg input (some tmr.q₀) (fun _ => []) [] :=
    initCfg_eq_wordsCfg tmr input
  have hdecomp : (extendTapes tmr er).runFrom
      (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br =
      embed er (tmr.runFrom (wordsCfg input (some tmr.q₀) (fun _ => []) []) τ_br)
        (fun l => tapeOfList (ws' l)) (fun _ => 0) := by
    rw [wordsCfg_eq_embed tmr er input ws' [] hblank, runFrom_embed]
  -- the embedded arm's output and halting are the raw arm's
  have hEout : ((extendTapes tmr er).runFrom
      (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br).output = O := by
    rw [hdecomp]
    change (tmr.runFrom (wordsCfg input (some tmr.q₀) (fun _ => []) []) τ_br).output = O
    rw [← hinit, hout]
  have hEhalt : ((extendTapes tmr er).runFrom
      (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br).state = none := by
    rw [hdecomp]
    change (tmr.runFrom (wordsCfg input (some tmr.q₀) (fun _ => []) []) τ_br).state = none
    rw [← hinit, hhalt]
  -- so the dispatch halts at `τ_br + 1` with the result
  have hDhalt : (tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1)).state = none :=
    harm.2.1.mpr hEhalt
  have hDout : (tmd.runFrom (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1)).output = O :=
    harm.1.trans hEout
  -- the embedded arm's space is the raw arm's plus the extra tapes
  have hEsp : (extendTapes tmr er).spaceUsed
      (wordsCfg input (some (extendTapes tmr er).q₀) ws' []) τ_br ≤ s_br + k := by
    rw [wordsCfg_eq_embed tmr er input ws' [] hblank]
    refine le_trans (spaceUsed_embed_le tmr er _ _ _ τ_br) ?_
    have h1 : tmr.spaceUsed (wordsCfg input (some tmr.q₀) (fun _ => []) []) τ_br ≤ s_br := by
      rw [← hinit]; exact hsp
    omega
  have hDsp : tmd.spaceUsed (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1) ≤ s_br + 2 * k := by
    refine le_trans harm.2.2 ?_; omega
  -- the first halting time is no later, and output and space are inherited
  obtain ⟨u₂, hu₂le, hu₂halt, hu₂act⟩ :=
    exists_minimal_halting_time tmd (wordsCfg input (some tmd.q₀) ws' []) (τ_br + 1) hDhalt
  refine ⟨u₂, hu₂le, hu₂halt, hu₂act, ?_, ?_⟩
  · rw [← hDout]; exact (runFrom_output_eq_of_halt tmd _ hu₂le hu₂halt).symm
  · exact le_trans (spaceUsed_mono tmd _ hu₂le) hDsp

/-- **Complexity of a two-way case analysis**, the recursor of `Bool`. If the scrutinee and both
branches are computable, then so is the case analysis `bif sel a then g a else h a`, in time the
test plus the larger branch and, crucially, space the test plus the larger branch — with no time
term, because the branch taken emits straight to the output tape. The scrutinee is encoded by
`boolEnc`, so the dispatch reads a single symbol. -/
public theorem computableInTimeAndSpace_cond {sel : α → Bool} {g h : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {tc sc tif sif telse selse : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn boolEnc tc sc)
    (hif : ComputableInTimeAndSpace g encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace h encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => bif sel a then g a else h a) encIn encOut
      (fun a => c * (tc a + max (tif a) (telse a) + 1))
      (fun a => c * (sc a + max (sif a) (selse a) + 1)) := by
  classical
  obtain ⟨m_c, c_c, Hc⟩ := exists_transformsTapes_ofComputableInput hsel
  obtain ⟨kg, Sg, hSg, tmg, Hg⟩ := hif
  obtain ⟨kh, Sh, hSh, tmh, Hh⟩ := helse
  set K := m_c + kg + kh + 1 with hK
  -- tape 0 holds the scrutinee bit; the branch machines live on tapes disjoint from it
  have hK0 : 0 < K := by omega
  let T_c : Fin K := ⟨0, hK0⟩
  let e_g : Fin kg ↪ Fin K :=
    ⟨fun j => ⟨1 + j.val, by have := j.isLt; omega⟩,
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simpa using this)⟩
  let e_h : Fin kh ↪ Fin K :=
    ⟨fun j => ⟨1 + kg + j.val, by have := j.isLt; omega⟩,
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simpa using this)⟩
  have hne_g : ∀ j, e_g j ≠ T_c := fun j => Fin.ne_of_val_ne (by change 1 + j.val ≠ 0; omega)
  have hne_h : ∀ j, e_h j ≠ T_c := fun j => Fin.ne_of_val_ne (by change 1 + kg + j.val ≠ 0; omega)
  -- the scrutinee transformer, leaving `[sel a]` on tape `T_c`
  obtain ⟨Sc, hSc, tmc, Hc_spec⟩ := Hc K T_c ∅ (by simp) (by simp only [Finset.card_empty]; omega)
  -- the streaming dispatch between the two (embedded) branch machines
  obtain ⟨Sd, hSd, tmd, Hd⟩ :=
    exists_branch_run T_c true (extendTapes tmg e_g) (extendTapes tmh e_h)
  -- build with the raw additive bounds, then renormalise once
  have main : ComputableInTimeAndSpace (fun a => bif sel a then g a else h a) encIn encOut
      (fun a => c_c * (tc a + 1) + (max (tif a) (telse a) + 1))
      (fun a => c_c * (sc a + 1 + 1) + K + (max (sif a) (selse a) + 2 * K)) := by
    refine ⟨K, Sc ⊕ Sd, inferInstance, tmc.seq tmd, fun a => ?_⟩
    set start := (tmc.seq tmd).initCfg (encIn a) with hstart
    have hstart_words : start = wordsCfg (encIn a) (some (tmc.seq tmd).q₀) (fun _ => []) [] := by
      rw [hstart, initCfg_eq_wordsCfg]
    -- phase one: the scrutinee transformer leaves `[sel a]` on `T_c`, blank elsewhere
    obtain ⟨τ, hτ, ws', hrun1, hQ1, hsp1⟩ :=
      Hc_spec a (encIn a) (fun _ => []) [] ⟨rfl, fun l _ => rfl⟩
    have hlen : (boolEnc (sel a)).length = 1 := rfl
    rw [hlen] at hsp1
    have hc1eq : tmc.runFrom (start.withState (some tmc.q₀)) τ =
        wordsCfg (encIn a) none ws' [] := by rw [hstart_words]; exact hrun1
    obtain ⟨τ', hτ'le, hτ'halt, hτ'act⟩ :=
      exists_minimal_halting_time tmc (start.withState (some tmc.q₀)) τ (by rw [hc1eq]; rfl)
    have hc1eq' : tmc.runFrom (start.withState (some tmc.q₀)) τ' = wordsCfg (encIn a) none ws' [] :=
      (runFrom_eq_of_halt tmc _ hτ'le hτ'halt).symm.trans hc1eq
    have hblank : ∀ l, l ≠ T_c → ws' l = [] := by
      intro l hl; rw [hQ1, Function.update_of_ne hl]
    have hTc_head : (ws' T_c).head? = some (sel a) := by
      rw [hQ1, Function.update_self]; rfl
    have hstartws : start.withState (some tmc.q₀) =
        wordsCfg (encIn a) (some tmc.q₀) (fun _ => []) [] := by rw [hstart_words]; rfl
    have hsp1' : tmc.spaceUsed (start.withState (some tmc.q₀)) τ' ≤ c_c * (sc a + 1 + 1) + K := by
      rw [hstartws]; exact le_trans (spaceUsed_mono tmc _ hτ'le) hsp1
    -- phase two: reduce to running the chosen arm to completion
    suffices H : ∀ u₂ : ℕ, u₂ ≤ max (tif a) (telse a) + 1 →
        (tmd.runFrom (wordsCfg (encIn a) (some tmd.q₀) ws' []) u₂).state = none →
        (∀ m < u₂, (tmd.runFrom (wordsCfg (encIn a) (some tmd.q₀) ws' []) m).state ≠ none) →
        (tmd.runFrom (wordsCfg (encIn a) (some tmd.q₀) ws' []) u₂).output =
          encOut (bif sel a then g a else h a) →
        tmd.spaceUsed (wordsCfg (encIn a) (some tmd.q₀) ws' []) u₂ ≤ max (sif a) (selse a) + 2 * K →
        ∃ t' ≤ c_c * (tc a + 1) + (max (tif a) (telse a) + 1),
          ∃ s' ≤ c_c * (sc a + 1 + 1) + K + (max (sif a) (selse a) + 2 * K),
          ComputesInTimeAndSpace (tmc.seq tmd) (encIn a)
            (encOut (bif sel a then g a else h a)) t' s' by
      cases hb : sel a with
      | false =>
        obtain ⟨t'h, ht'hle, s'h, hs'hle, hhstate, hhout, hhsp⟩ := Hh a
        have hhead : (ws' T_c).head? ≠ some true := by rw [hTc_head, hb]; simp
        obtain ⟨u₂, hu₂le, hu₂halt, hu₂act, hu₂out, hu₂sp⟩ :=
          exists_arm_run (fun j => hblank (e_h j) (hne_h j)) ((Hd (encIn a) ws' [] t'h).2 hhead)
            hhstate hhout (le_trans hhsp.le (le_trans hs'hle (le_max_right (sif a) (selse a))))
        exact H u₂ (by have := le_max_right (tif a) (telse a); omega) hu₂halt hu₂act
          (by rw [hb]; exact hu₂out) hu₂sp
      | true =>
        obtain ⟨t'g, ht'gle, s'g, hs'gle, hgstate, hgout, hgsp⟩ := Hg a
        have hhead : (ws' T_c).head? = some true := by rw [hTc_head, hb]
        obtain ⟨u₂, hu₂le, hu₂halt, hu₂act, hu₂out, hu₂sp⟩ :=
          exists_arm_run (fun j => hblank (e_g j) (hne_g j)) ((Hd (encIn a) ws' [] t'g).1 hhead)
            hgstate hgout (le_trans hgsp.le (le_trans hs'gle (le_max_left (sif a) (selse a))))
        exact H u₂ (by have := le_max_left (tif a) (telse a); omega) hu₂halt hu₂act
          (by rw [hb]; exact hu₂out) hu₂sp
    intro u₂ hu₂ hu₂halt hu₂act hu₂out hu₂sp
    obtain ⟨hseq_run, hseq_act, hseq_sp⟩ :=
      seq_spec (tm₁ := tmc) (tm₂ := tmd) (c := start) (by rw [hstart_words]; rfl)
        hc1eq' rfl hτ'act hsp1' rfl hu₂halt hu₂act hu₂sp
    refine ⟨τ' + u₂, by omega, (tmc.seq tmd).spaceUsed start (τ' + u₂), hseq_sp, ?_, ?_, rfl⟩
    · rw [hseq_run]; rfl
    · rw [hseq_run]; exact hu₂out
  -- renormalise the additive bounds into the stated multiplicative shape
  refine ⟨2 * c_c + 3 * K + 2, main.mono (fun a => ?_) (fun a => ?_)⟩
  · -- time
    have e1 : c_c * (tc a + 1) ≤ c_c * (tc a + max (tif a) (telse a) + 1) :=
      Nat.mul_le_mul_left c_c (by omega)
    have e2 : c_c * (tc a + max (tif a) (telse a) + 1) + (tc a + max (tif a) (telse a) + 1) =
        (c_c + 1) * (tc a + max (tif a) (telse a) + 1) := (Nat.succ_mul c_c _).symm
    have e3 : (c_c + 1) * (tc a + max (tif a) (telse a) + 1) ≤
        (2 * c_c + 3 * K + 2) * (tc a + max (tif a) (telse a) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · -- space
    set mS := max (sif a) (selse a) with hmS
    set MS := sc a + mS + 1 with hMS
    have P1 : c_c * (sc a + 1 + 1) ≤ 2 * (c_c * MS) := by
      have h2 : c_c * (sc a + 1 + 1) ≤ c_c * (MS + 1) := Nat.mul_le_mul_left c_c (by omega)
      have h3 : c_c * (MS + 1) = c_c * MS + c_c := Nat.mul_succ c_c MS
      have h4 : c_c ≤ c_c * MS := Nat.le_mul_of_pos_right c_c (by omega)
      omega
    have P3 : 3 * K ≤ 3 * (K * MS) := by
      have : K ≤ K * MS := Nat.le_mul_of_pos_right K (by omega)
      omega
    have expand : (2 * c_c + 3 * K + 2) * MS = 2 * (c_c * MS) + 3 * (K * MS) + 2 * MS := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    omega

end Turing.MultiTapeTM
