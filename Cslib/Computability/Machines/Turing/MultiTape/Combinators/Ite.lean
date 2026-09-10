/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Branch
public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.Adapters
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concat
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.TakeDrop
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Complexity of a case analysis

A case analysis chooses which of several machines to continue with. Everything here is built at the
function level on a single machine-level atom — `computableInTimeAndSpace_iteFirstBit`, the branch
on the input's first encoded bit — together with the reusable atoms
`computableInTimeAndSpace_concat` (concatenate two outputs), `computableInTimeAndSpace_drop` (strip
a prefix) and function composition.

## The one machine atom, and why the branch not taken is never run

`iteFirstBit` reads the first symbol of the input directly and, before it has run anything, jumps
to `g`'s machine or `h`'s machine; that machine then reads the whole input in place and emits its
result *straight to the real output tape*. Only one arm ever runs, and its result is never parked on
a work tape — so there is no time term in the space bound, and nesting `n` conditionals runs `n`
arms, not
`2 ^ n`. This laziness is the content of a case analysis, and it cannot come from composing total
functions (`cond ∘ (fun a => (c a, f a, g a))` would compute every branch), which is why one
machine-level branch is unavoidable. It is the only one this file needs.

## From the atom to `cond`, `ite`, `dite` and `match`

`iteFirstBit` branches on the input's first bit; `cond sel g h` branches on `sel a`, which is not
the input's first bit. The gap is closed entirely with the other atoms: the selector's bit is
concatenated ahead of the input to form a tagged value whose encoding starts with `sel a`, the
branch reads that bit, each arm strips the tag with `drop 1` before running its branch, and the
tagging is undone on the way in by one composition. `ite` and `dite` are `cond` read through
`decide`; the finite `match` is a `Finset` induction that splices in one `cond` per case.

## Bounds

Bounds here are deliberately relaxed to a single shape, `c * (… + 1)`: nothing downstream depends on
the conditional family being tight (`loop` and `comp` do not use it), and the function-level
construction spends constant factors freely. The space bound still carries no *time* term, because
the branch taken streams to the output; it does pick up the constant-factor and input-length slack
that composition introduces.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_iteFirstBit`: the machine atom, the branch on the
  input's first encoded bit.
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

/-- A run of a machine placed by `extendTapes` on tapes that are blank on its range mirrors the
run of the underlying machine, seen through the tape embedding. This is the decomposition of a
word configuration into an embedded configuration: the tapes in the range carry the machine's own
(here blank) words, the tapes outside it are carried through as extra tapes. -/
private lemma wordsCfg_eq_embed_blank {k kr : ℕ} {Sr : Type}
    (tmr : MultiTapeTM kr Bool Sr) (er : Fin kr ↪ Fin k) (input : List Bool)
    (ws : Fin k → List Bool) (out : List Bool) (hblank : ∀ j, ws (er j) = []) :
    wordsCfg input (some (extendTapes tmr er).q₀) ws out =
      embed er (wordsCfg input (some tmr.q₀) (fun _ => []) out)
        (fun l => tapeOfList (ws l)) (fun _ => 0) := by
  change wordsCfg input (some tmr.q₀) ws out = _
  rw [wordsCfg_eq_embed er input (some tmr.q₀) ws out,
    show (fun j => ws (er j)) = (fun _ => []) from funext hblank]

/-- **Phase two of the case analysis: run the chosen arm to completion.** Given the streaming
dispatch's guarantee for one arm — that after the dispatch step the combined machine's output,
halting and space are the embedded arm's — and the underlying arm machine's own guarantee that it
halts with the encoded result, the dispatch halts with that result on the output tape, in one more
step than the arm, using at most the arm's space plus twice the layout size. -/
private lemma exists_arm_run {k kr : ℕ} {Sr Sd : Type}
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
    rw [wordsCfg_eq_embed_blank tmr er input ws' [] hblank, runFrom_embed]
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
    rw [wordsCfg_eq_embed_blank tmr er input ws' [] hblank]
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

/-- **The elementary two-way branch on the input's first symbol.** If `g` and `h` are computable,
then so is the function that runs `g` when the input's first encoded symbol is `some true` and `h`
otherwise. The dispatch reads the input directly, so both arms then read the whole input in place
and emit their result straight to the real output tape — no scrutinee is materialised, and there is
no time term in the space bound.

This is the atom on which the whole conditional family is rebuilt: `cond`, `ite`, `dite` and the
finite `match` all reduce to it by tagging the input with a selector bit and stripping the tag in
each arm. -/
public theorem computableInTimeAndSpace_iteFirstBit {g h : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {tg sg th sh : α → ℕ}
    (hg : ComputableInTimeAndSpace g encIn encOut tg sg)
    (hh : ComputableInTimeAndSpace h encIn encOut th sh) :
    ∃ c, ComputableInTimeAndSpace
      (fun a => if (encIn a).head? = some true then g a else h a) encIn encOut
      (fun a => c * (tg a + th a + 1)) (fun a => c * (sg a + sh a + 1)) := by
  classical
  obtain ⟨kg, Sg, hSg, tmg, Hg⟩ := hg
  obtain ⟨kh, Sh, hSh, tmh, Hh⟩ := hh
  set K := kg + kh with hK
  -- the two branch machines live on disjoint blocks of a shared `K`-tape layout
  let e_g : Fin kg ↪ Fin K :=
    ⟨fun j => ⟨j.val, by have := j.isLt; omega⟩,
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simpa using this)⟩
  let e_h : Fin kh ↪ Fin K :=
    ⟨fun j => ⟨kg + j.val, by have := j.isLt; omega⟩,
      fun a b hab => Fin.ext (by have := congrArg Fin.val hab; simpa using this)⟩
  -- the streaming input-dispatch between the two (embedded) branch machines
  obtain ⟨Sd, hSd, tmd, Hd⟩ :=
    exists_inputBranch_run true (extendTapes tmg e_g) (extendTapes tmh e_h)
  refine ⟨2 * K + 1, K, Sd, hSd, tmd, fun a => ?_⟩
  -- reduce to running the chosen arm to completion on all-blank work tapes
  by_cases hb : (encIn a).head? = some true
  · -- the input starts with `true`: run `g`'s machine
    obtain ⟨t'g, ht'gle, s'g, hs'gle, hgstate, hgout, hgsp⟩ := Hg a
    obtain ⟨u₂, hu₂le, hu₂halt, hu₂act, hu₂out, hu₂sp⟩ :=
      exists_arm_run (er := e_g) (fun _ => rfl)
        ((Hd (encIn a) (fun _ => []) [] t'g).1 hb) hgstate hgout hgsp.le
    refine ⟨u₂, ?_, tmd.spaceUsed (tmd.initCfg (encIn a)) u₂, ?_, ?_, ?_, ?_⟩
    · -- time: `u₂ ≤ t'g + 1 ≤ tg a + 1`
      have hu : u₂ ≤ tg a + 1 := by omega
      have h2 : tg a + 1 ≤ tg a + th a + 1 := by omega
      exact le_trans hu (le_trans h2 (Nat.le_mul_of_pos_left _ (by omega)))
    · -- space: `≤ s'g + 2K ≤ sg a + 2K`
      change tmd.spaceUsed (tmd.initCfg (encIn a)) u₂ ≤ (2 * K + 1) * (sg a + sh a + 1)
      have hle : tmd.spaceUsed (tmd.initCfg (encIn a)) u₂ ≤ sg a + 2 * K := by
        rw [initCfg_eq_wordsCfg]; exact le_trans hu₂sp (by omega)
      refine le_trans hle ?_
      have hexp : (2 * K + 1) * (sg a + sh a + 1) =
          (2 * K + 1) * (sg a + sh a) + (2 * K + 1) := Nat.mul_succ _ _
      have hge : sg a ≤ (2 * K + 1) * (sg a + sh a) := by
        have h2 : sg a + sh a ≤ (2 * K + 1) * (sg a + sh a) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      omega
    · rw [initCfg_eq_wordsCfg]; exact hu₂halt
    · rw [initCfg_eq_wordsCfg, hu₂out]; simp [hb]
    · rfl
  · -- otherwise: run `h`'s machine
    obtain ⟨t'h, ht'hle, s'h, hs'hle, hhstate, hhout, hhsp⟩ := Hh a
    obtain ⟨u₂, hu₂le, hu₂halt, hu₂act, hu₂out, hu₂sp⟩ :=
      exists_arm_run (er := e_h) (fun _ => rfl)
        ((Hd (encIn a) (fun _ => []) [] t'h).2 hb) hhstate hhout hhsp.le
    refine ⟨u₂, ?_, tmd.spaceUsed (tmd.initCfg (encIn a)) u₂, ?_, ?_, ?_, ?_⟩
    · have : u₂ ≤ th a + 1 := by omega
      exact le_trans this (le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega)))
    · change tmd.spaceUsed (tmd.initCfg (encIn a)) u₂ ≤ (2 * K + 1) * (sg a + sh a + 1)
      have hle : tmd.spaceUsed (tmd.initCfg (encIn a)) u₂ ≤ sh a + 2 * K := by
        rw [initCfg_eq_wordsCfg]; exact le_trans hu₂sp (by omega)
      refine le_trans hle ?_
      have hexp : (2 * K + 1) * (sg a + sh a + 1) =
          (2 * K + 1) * (sg a + sh a) + (2 * K + 1) := Nat.mul_succ _ _
      have hge : sh a ≤ (2 * K + 1) * (sg a + sh a) := by
        have h2 : sg a + sh a ≤ (2 * K + 1) * (sg a + sh a) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      omega
    · rw [initCfg_eq_wordsCfg]; exact hu₂halt
    · rw [initCfg_eq_wordsCfg, hu₂out]; simp [hb]
    · rfl

/-- **Normalised composition.** Composing a computable `id`-relabelling with a computable function,
both in the normalised bound shape `c * (P a + 1)`, stays in that shape. The scratch encoding's
length is bounded by `P a + 1`, and the composed result's length by the second function's bound, so
every term that composition adds is already a multiple of `P a + 1`. -/
private lemma norm_comp {γ' : Type*} {gg : α → γ'} {encX encY : α ↪ List Bool}
    {encZ : γ' ↪ List Bool} {P : α → ℕ} {cf cg : ℕ}
    (hf : ComputableInTimeAndSpace (id : α → α) encX encY
      (fun a => cf * (P a + 1)) (fun a => cf * (P a + 1)))
    (hg : ComputableInTimeAndSpace gg encY encZ
      (fun a => cg * (P a + 1)) (fun a => cg * (P a + 1)))
    (hY : ∀ a, (encY a).length ≤ P a + 1) :
    ∃ c, ComputableInTimeAndSpace gg encX encZ
      (fun a => c * (P a + 1)) (fun a => c * (P a + 1)) := by
  obtain ⟨cc, hcc⟩ := computableInTimeAndSpace_comp hf hg
  rw [show gg ∘ (id : α → α) = gg from rfl] at hcc
  refine ⟨cc * (cf + 2 * cg + 2), hcc.mono (fun a => ?_) (fun a => ?_)⟩
  · simp only [id_eq]
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left cc ?_
    have hexp : (cf + 2 * cg + 2) * (P a + 1) =
        cf * (P a + 1) + 2 * (cg * (P a + 1)) + 2 * (P a + 1) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    have hY' := hY a
    omega
  · simp only [id_eq]
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left cc ?_
    have hexp : (cf + 2 * cg + 2) * (P a + 1) =
        cf * (P a + 1) + 2 * (cg * (P a + 1)) + 2 * (P a + 1) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    have hY' := hY a
    have hZ := hg.length_encOut_le a
    omega

/-- **Complexity of a two-way case analysis**, the recursor of `Bool`. If the scrutinee and both
branches are computable, then so is the case analysis `bif sel a then g a else h a`.

The construction is entirely at the function level, on top of the elementary atoms. The selector's
bit is concatenated ahead of the input (`computableInTimeAndSpace_concat`) to form a tagged value
whose encoding starts with `sel a`; the branch on that first bit
(`computableInTimeAndSpace_iteFirstBit`) runs `g` or `h`, each first stripping the tag with `drop 1`
(`computableInTimeAndSpace_drop`) and running its branch by composition; and the tagging is undone
on the way in by one more composition. Bounds are relaxed to the single shape `c * (P a + 1)`, with
`P` collecting the six input bounds and the input length — nothing downstream needs them tight. -/
public theorem computableInTimeAndSpace_cond {sel : α → Bool} {g h : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {tc sc tif sif telse selse : α → ℕ}
    (hsel : ComputableInTimeAndSpace sel encIn boolEnc tc sc)
    (hif : ComputableInTimeAndSpace g encIn encOut tif sif)
    (helse : ComputableInTimeAndSpace h encIn encOut telse selse) :
    ∃ c, ComputableInTimeAndSpace (fun a => bif sel a then g a else h a) encIn encOut
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1))
      (fun a => c * (tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length + 1)) := by
  classical
  set P : α → ℕ :=
    fun a => tc a + sc a + tif a + sif a + telse a + selse a + (encIn a).length with hP
  -- the tagged encoding: the selector bit in front of the input
  let encTag : α ↪ List Bool :=
    ⟨fun a => sel a :: encIn a, fun a b hab => by
      simp only [List.cons.injEq] at hab; exact encIn.injective hab.2⟩
  have hencTag : ∀ a, encTag a = sel a :: encIn a := fun a => rfl
  -- pointwise facts about `P`
  have hLin : ∀ a, (encIn a).length ≤ P a := fun a => by simp only [hP]; omega
  have hLtag : ∀ a, (encTag a).length ≤ P a + 1 := fun a => by
    rw [hencTag]; simp only [List.length_cons]; have := hLin a; omega
  -- normalise the three inputs and the identity into the `c * (P a + 1)` shape
  have hsel_n : ComputableInTimeAndSpace sel encIn boolEnc
      (fun a => 1 * (P a + 1)) (fun a => 1 * (P a + 1)) :=
    hsel.mono (fun a => by simp only [hP]; omega) (fun a => by simp only [hP]; omega)
  have hif_n : ComputableInTimeAndSpace g encIn encOut
      (fun a => 1 * (P a + 1)) (fun a => 1 * (P a + 1)) :=
    hif.mono (fun a => by simp only [hP]; omega) (fun a => by simp only [hP]; omega)
  have helse_n : ComputableInTimeAndSpace h encIn encOut
      (fun a => 1 * (P a + 1)) (fun a => 1 * (P a + 1)) :=
    helse.mono (fun a => by simp only [hP]; omega) (fun a => by simp only [hP]; omega)
  have hid_n : ComputableInTimeAndSpace (id : α → α) encIn encIn
      (fun a => 1 * (P a + 1)) (fun a => 1 * (P a + 1)) :=
    (computableInTimeAndSpace_id (enc := encIn)).mono
      (fun a => by have := hLin a; omega) (fun a => by omega)
  -- tag: `id : encIn → encTag`, via concatenation of the selector bit and the input
  obtain ⟨ct, htag⟩ := computableInTimeAndSpace_concat
    (encD := encTag) (f := sel) (g := (id : α → α)) (h := (id : α → α))
    (fun a => by rw [hencTag]; rfl) hsel_n hid_n
  have htag_n : ComputableInTimeAndSpace (id : α → α) encIn encTag
      (fun a => (ct * 3) * (P a + 1)) (fun a => (ct * 3) * (P a + 1)) := by
    refine htag.mono (fun a => ?_) (fun a => ?_) <;>
      · rw [Nat.mul_assoc]; refine Nat.mul_le_mul_left ct ?_
        have h3 : (3 : ℕ) * (P a + 1) = (P a + 1) + (P a + 1) + (P a + 1) := by
          rw [Nat.succ_mul, Nat.succ_mul, Nat.one_mul]
        omega
  -- untag: `id : encTag → encIn`, dropping the tag bit
  have huntag_n : ComputableInTimeAndSpace (id : α → α) encTag encIn
      (fun a => 2 * (P a + 1)) (fun a => 2 * (P a + 1)) := by
    refine (computableInTimeAndSpace_drop (encFrom := encTag) (encTo := encIn) 1
      (fun a => by rw [hencTag]; rfl)).mono (fun a => ?_) (fun a => ?_)
    · have := hLtag a; omega
    · omega
  -- each branch on the tagged input: strip the tag, then run the branch
  obtain ⟨cg', hg'⟩ :=
    norm_comp (P := P) huntag_n hif_n (fun a => le_trans (hLin a) (Nat.le_succ _))
  obtain ⟨ch', hh'⟩ :=
    norm_comp (P := P) huntag_n helse_n (fun a => le_trans (hLin a) (Nat.le_succ _))
  -- branch on the first (tag) bit of the tagged input
  obtain ⟨ci, hite⟩ := computableInTimeAndSpace_iteFirstBit hg' hh'
  have hite_n : ComputableInTimeAndSpace
      (fun a => if (encTag a).head? = some true then g a else h a) encTag encOut
      (fun a => (ci * (cg' + ch' + 1)) * (P a + 1))
      (fun a => (ci * (cg' + ch' + 1)) * (P a + 1)) := by
    refine hite.mono (fun a => ?_) (fun a => ?_) <;>
      · rw [Nat.mul_assoc]; refine Nat.mul_le_mul_left ci ?_
        have hexp : (cg' + ch' + 1) * (P a + 1) =
            cg' * (P a + 1) + ch' * (P a + 1) + (P a + 1) := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
        omega
  -- undo the tagging on the way in, then read off the case analysis
  obtain ⟨cf, hfinal⟩ := norm_comp (P := P) htag_n hite_n hLtag
  refine ⟨cf, ?_⟩
  have hfun : (fun a => if (encTag a).head? = some true then g a else h a) =
      fun a => bif sel a then g a else h a := by
    funext a
    rw [hencTag]
    cases hb : sel a <;> simp
  rw [hfun] at hfinal
  exact hfinal

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
