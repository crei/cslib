/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Cslib.Foundations.Data.Fin.Tuple

/-!
# Reading the input from a work tape

`inputFromTape tm` behaves like `tm`, except that it reads its input from a work tape — the
*virtual input tape* — instead of the real one, which it never touches. The virtual input head
lives at cell `p - 1` when the simulated input head is at position `p`, so the word cells
`0, …, len - 1` are the input positions `1, …, len` and the two boundary positions read the blanks
at cells `-1` and `len`.

The one thing a blank cell cannot tell the machine is *which* boundary it is at — and it must
know, because the input head clamps there. This ambiguity is resolved by tracking a boundary
classification. A second fresh work tape, the *flag tape*, moves in lockstep with the virtual input
head and carries a single non-blank `mark` at cell `-1`, so the left boundary is recognised by
reading the flag. Reading blank on both the virtual input tape and the flag tape means the right
boundary.

The configuration map `inCfg` places the simulated input on the virtual input tape, places the
marker on the flag tape, and leaves the real input tape unused. The main lemmas show that one step
and an entire run of the redirected machine mirror the corresponding step and run of `tm`.

`inputFromWord tm mark` turns this into a machine on words: it writes `mark` to cell `-1` of the
flag tape (`markFlag k (some mark)`), runs `inputFromTape tm`, and erases the mark again
(`markFlag k none`).

## Main definitions

* `Turing.MultiTapeTM.inputFromTape`, `Turing.MultiTapeTM.inCfg`: the redirected machine and its
  configuration map.
* `Turing.MultiTapeTM.markFlag`, `Turing.MultiTapeTM.inputFromWord`: setting and erasing the flag,
  and the machine on words.

## Main results

* `Turing.MultiTapeTM.runFrom_inCfg`, `Turing.MultiTapeTM.spaceUsed_inputFromTape`: the mirrored
  run and its space.
* `Turing.MultiTapeTM.transformsTapes_inputFromWord_of_runFrom`: a run of `tm` on the virtual input
  word, from and to `Turing.MultiTapeTM.wordsCfg` configurations, gives a specification of
  `inputFromWord tm mark`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-! ### The redirected machine -/

/-- The clamped move of the virtual input head: at the left boundary (blank under the virtual
head, flag marked) left moves are blocked, at the right boundary (blank on both) right moves
are. -/
@[expose] public def clampMove (wvip wflag : Option Symbol) (m : SignType) : SignType :=
  match wvip with
  | some _ => m
  | none =>
    match wflag with
    | some _ => (match m with | SignType.neg => SignType.zero | _ => m)
    | none => (match m with | SignType.pos => SignType.zero | _ => m)

/-- `tm`, reading its input from the virtual input tape `Fin.natAdd k 0`, with the flag tape
`Fin.natAdd k 1` marking the cell left of the input. The real input tape is never read and never
moved. -/
@[expose] public noncomputable def inputFromTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 2) Symbol State :=
  ofTr tm.q₀ fun q _ work =>
    let a := tm.tr q (work (Fin.natAdd k 0)) fun j => work (j.castAdd 2)
    let m := clampMove (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1)) a.inputTape
    { a with
      inputTape := 0
      workTapes := Fin.append a.workTapes fun _ => (none, m) }

/-- A configuration of `tm` on `input`, as the redirecting machine sees it, over an arbitrary
ambient input: `input` sits on the virtual input tape with the head at cell `inputPos - 1`, the flag
tape carries its mark at `-1` with its head in lockstep, and the ambient input head rests at
`1`. -/
@[expose] public def inCfg (mark : Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
    (outerInput : List Symbol) : Cfg (k + 2) Symbol State outerInput where
  state := c.state
  inputPos := 1
  workTapes := Fin.append c.workTapes
    ![tapeOfList input, Function.update (fun _ ↦ none) (-1) (some mark)]
  workTapePos := Fin.append c.workTapePos (fun _ : Fin 2 ↦ (c.inputPos : ℤ) - 1)
  output := c.output

section Projections

variable {mark : Symbol} {input : List Symbol} {outerInput : List Symbol}

@[simp]
public lemma inCfg_inputPos (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).inputPos = 1 := rfl

@[simp]
public lemma inCfg_workTapes_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapes (j.castAdd 2) = c.workTapes j := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapes_vip (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapes (Fin.natAdd k 0) = tapeOfList input := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapes_flag (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapes (Fin.natAdd k 1) =
      Function.update (fun _ => none) (-1) (some mark) := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapePos_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapePos (j.castAdd 2) = c.workTapePos j := by
  simp [inCfg]

/-- The virtual input head and the flag head both stand at cell `inputPos - 1`. -/
@[simp]
public lemma inCfg_workTapePos_natAdd (c : Cfg k Symbol State input) (i : Fin 2) :
    (inCfg mark c outerInput).workTapePos (Fin.natAdd k i) = (c.inputPos.val : ℤ) - 1 := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapeSymbols_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapeSymbols (j.castAdd 2) = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The virtual input head reads exactly what the simulated input head reads: the word cells are
the input positions, the two boundary cells are blank. -/
@[simp]
public lemma inCfg_workTapeSymbols_vip (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapeSymbols (Fin.natAdd k 0) = c.inputSymbol := by
  have := c.inputPos.isLt
  rw [Cfg.workTapeSymbols, inCfg_workTapes_vip, inCfg_workTapePos_natAdd]
  obtain h | h | h : c.inputPos.val = 0 ∨ c.inputPos.val = input.length + 1 ∨
      (0 < c.inputPos.val ∧ c.inputPos.val < input.length + 1) := by omega
  · rw [inputSymbol_eq_none_of_boundary (.inl h), h]
    exact tapeOfList_negSucc input 0
  · rw [inputSymbol_eq_none_of_boundary (.inr h), h]; simp
  · rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega),
      show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val - 1 : ℕ) by omega, tapeOfList_ofNat,
      List.getElem?_eq_getElem (by omega)]

/-- The flag head reads the mark exactly at the left boundary. -/
@[simp]
public lemma inCfg_workTapeSymbols_flag (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapeSymbols (Fin.natAdd k 1) =
      if c.inputPos.val = 0 then some mark else none := by
  simp [Cfg.workTapeSymbols, Function.update_apply]

/-- The clamped move of the virtual input head tracks the simulated input head exactly. -/
public lemma val_moveInputPos_sub_one_eq_clampMove (mark : Symbol) (c : Cfg k Symbol State input)
    (m : SignType) :
    ((moveInputPos c.inputPos m).val : ℤ) - 1 =
      ((c.inputPos.val : ℤ) - 1) +
        (clampMove c.inputSymbol (if c.inputPos.val = 0 then some mark else none) m : ℤ) := by
  have := c.inputPos.isLt
  rw [val_moveInputPos_eq]
  obtain h | h | h : c.inputPos.val = 0 ∨ c.inputPos.val = input.length + 1 ∨
      (0 < c.inputPos.val ∧ c.inputPos.val < input.length + 1) := by omega
  · -- left boundary: virtual head blank, flag marked
    rw [inputSymbol_eq_none_of_boundary (.inl h), ite_eq_left h]
    rcases m with _ | _ | _ <;> simp only [clampMove, SignType.cast] <;> omega
  · -- right boundary: virtual head blank, flag unmarked
    rw [inputSymbol_eq_none_of_boundary (.inr h), ite_eq_right (by omega)]
    rcases m with _ | _ | _ <;> simp only [clampMove, SignType.cast] <;> omega
  · -- inside the input: virtual head nonblank
    rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega)]
    rcases m with _ | _ | _ <;> simp only [clampMove, SignType.cast] <;> omega

/-- **The redirection is a step-semiconjugation.** One step of the machine reading its input from
the virtual tape mirrors one step of the original, under the embedding `inCfg`. -/
public lemma step_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State input) (outerInput : List Symbol) :
    tm.inputFromTape.step (inCfg mark c outerInput) =
      inCfg mark (tm.step c) outerInput := by
  cases hq : c.state with
  | none => simp [inCfg, hq]
  | some q =>
    rw [step_of_state (cfg := inCfg mark c outerInput) hq, step_of_state hq]
    simp only [inputFromTape, tr_ofTr, inCfg_workTapeSymbols_vip, inCfg_workTapeSymbols_flag,
      inCfg_workTapeSymbols_castAdd]
    refine Cfg.ext rfl (by simp [inCfg]) ?_ ?_ rfl <;> funext l <;>
      induction l using Fin.addCases <;> simp [inCfg, val_moveInputPos_sub_one_eq_clampMove mark]

/-- The redirected run mirrors the original. -/
public lemma runFrom_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State input) (outerInput : List Symbol) (n : ℕ) :
    tm.inputFromTape.runFrom (inCfg mark c outerInput) n =
      inCfg mark (tm.runFrom c n) outerInput :=
  (Function.Semiconj.iterate_right (f := (inCfg mark · outerInput))
    (fun c => (step_inCfg tm mark c outerInput).symm) n c).symm

/-- **Space of the input-redirected machine.** The `k` inner tapes visit exactly what the original
does; the two extra tapes (virtual input, flag) each move only with the simulated input head,
which stays within `[-1, input.length]` — so they add at most `2 * (input.length + 2)`. -/
public lemma spaceUsed_inputFromTape (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State input) (outerInput : List Symbol) (n : ℕ) :
    tm.inputFromTape.spaceUsed (inCfg mark c outerInput) n ≤
      tm.spaceUsed c n + 2 * (input.length + 2) := by
  simpa using tm.spaceUsed_le_of_workTapePos_embedding (Fin.castAddEmb 2) c
    (inCfg mark c outerInput) (input.length + 2) (fun m _ j => by simp [runFrom_inCfg])
    fun l hl => by
      induction l using Fin.addCases with
      | left j => exact absurd ⟨j, rfl⟩ hl
      | right i =>
        refine (spaceUsedByTape_le_card _ (S := .Icc (-1) input.length) fun m _ => ?_).trans
          (by rw [Int.card_Icc]; omega)
        have := (tm.runFrom c m).inputPos.isLt
        simp only [runFrom_inCfg, inCfg_workTapePos_natAdd, Finset.mem_Icc]
        omega

end Projections

/-! ### Setting and erasing the flag -/

/-- `markWork write` placed on the flag tape, the last of `k + 2` work tapes: it writes `write` to
the cell left of the head of that tape. -/
public noncomputable def markFlag (k : ℕ) (write : Option Symbol) :
    MultiTapeTM (k + 2) Symbol MarkWorkState :=
  (markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k 1))

/-- `tm`, reading its input from a word on the virtual input tape `Fin.natAdd k 0`, with `mark`
written to cell `-1` of the flag tape, the last work tape, before and erased after. -/
public noncomputable def inputFromWord (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 2) Symbol (MarkWorkState ⊕ State ⊕ MarkWorkState) :=
  (markFlag k (some mark)).seq (tm.inputFromTape.seq (markFlag k none))

/-- `Turing.MultiTapeTM.inCfg` of a `wordsCfg` configuration: the input `w` on the virtual input
tape, `mark` at cell `-1` of the flag tape, every head at cell `0`. -/
public lemma inCfg_wordsCfg (mark : Symbol) {w : List Symbol} (q : Option State)
    (ws : Fin k → List Symbol) (out outer : List Symbol) :
    inCfg mark (wordsCfg w q ws out) outer =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.addCases <;>
    simp [inCfg, wordsCfg]

/-- Updating the flag tape of an appended family of tapes only changes the flag entry. -/
private lemma update_append_flag {α : Type*} (ws₀ : Fin k → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

private lemma markFlag_q₀ (write : Option Symbol) :
    (markFlag k write).q₀ = (markWork Symbol write).q₀ := rfl

/-- The flag tape of a configuration whose tapes are `Fin.append tapes ![vip, flag]`, as a one-tape
configuration of `markWork`. -/
private lemma oneTapeCfg_flag {input : List Symbol} (write : Option Symbol)
    (tapes : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    oneTapeCfg (Fin.natAdd k 1)
        (⟨some (markWork Symbol write).q₀, ip, Fin.append tapes ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) =
      ⟨some (markWork Symbol write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, Fin.append_right]

/-- In two steps, `markFlag k write` writes `write` to cell `-1` of the flag tape and changes
nothing else. -/
private lemma runFrom_markFlag {input : List Symbol} (write : Option Symbol)
    (tapes : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    (markFlag k write).runFrom
        (⟨some (markFlag k write).q₀, ip, Fin.append tapes ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) 2 =
      ⟨none, ip, Fin.append tapes ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ := by
  rw [markFlag_q₀, markFlag, runFrom_tapeEmb, oneTapeCfg_flag, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa using update_append_flag tapes vip flag (Function.update flag (-1) write)
  · funext l; simp [Function.update_apply]

/-- `markFlag k write` visits at most `k + 3` cells: two on the flag tape and the starting cell
of each other tape. -/
private lemma spaceUsed_markFlag_le {input : List Symbol} (write : Option Symbol)
    (tapes : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) (n : ℕ) :
    (markFlag k write).spaceUsed
        (⟨some (markFlag k write).q₀, ip, Fin.append tapes ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) n ≤ k + 3 := by
  rw [markFlag_q₀]
  refine (spaceUsed_tapeEmb_le (markWork Symbol write) (Fin.natAdd k 1) _ n).trans ?_
  rw [oneTapeCfg_flag]
  have := spaceUsed_markWork_le write ip flag out 0 n
  omega

/-- A `wordsCfg` configuration whose last two words are `w` and the empty word, written out. -/
private lemma wordsCfg_append_words {outer : List Symbol} (q : Option State)
    (ws : Fin k → List Symbol) (w out : List Symbol) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append tapeOfList ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

section Flag

variable (mark : Symbol) (ws : Fin k → List Symbol) (w out outer : List Symbol)

/-- Setting the flag on a `wordsCfg` configuration gives the configuration in which
`inputFromTape` starts, visiting at most `k + 3` cells. -/
private lemma runFrom_setFlag :
    (markFlag k (some mark)).runFrom
        (wordsCfg outer (some (markFlag k (some mark)).q₀) (Fin.append ws ![w, []]) out) 2 =
      inCfg mark (wordsCfg w (none : Option MarkWorkState) ws out) outer ∧
    (markFlag k (some mark)).spaceUsed
        (wordsCfg outer (some (markFlag k (some mark)).q₀) (Fin.append ws ![w, []]) out) 2 ≤
      k + 3 := by
  rw [wordsCfg_append_words, runFrom_markFlag, inCfg_wordsCfg]
  exact ⟨rfl, spaceUsed_markFlag_le _ _ _ _ _ _ _⟩

/-- Erasing the flag on the configuration in which `inputFromTape` halts gives a `wordsCfg`
configuration, visiting at most `k + 3` cells. -/
private lemma runFrom_eraseFlag :
    (markFlag k none).runFrom ((inCfg mark (wordsCfg w (none : Option State) ws out)
        outer).withState (some (markFlag (Symbol := Symbol) k none).q₀)) 2 =
      wordsCfg outer none (Fin.append ws ![w, []]) out ∧
    (markFlag k none).spaceUsed ((inCfg mark (wordsCfg w (none : Option State) ws out)
        outer).withState (some (markFlag (Symbol := Symbol) k none).q₀)) 2 ≤ k + 3 := by
  have hcfg : (inCfg mark (wordsCfg w (none : Option State) ws out) outer).withState
      (some (markFlag (Symbol := Symbol) k none).q₀) =
        ⟨some (markFlag (Symbol := Symbol) k none).q₀, 1, Fin.append (fun j => tapeOfList (ws j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)], fun _ => 0, out⟩ := by
    rw [inCfg_wordsCfg]; rfl
  rw [hcfg, runFrom_markFlag, wordsCfg_append_words, Function.update_idem]
  exact ⟨by simp, spaceUsed_markFlag_le _ _ _ _ _ _ _⟩

end Flag

open Sequential in
/-- If `tm`, run on the input `w` with work tapes `ws₀`, halts after `t` steps with work tapes
`ws₁` and every head back at its start, having emitted `e`, then `inputFromWord tm mark` takes the
work tapes `Fin.append ws₀ ![w, []]` to `Fin.append ws₁ ![w, []]` and emits `e`. -/
public theorem transformsTapes_inputFromWord_of_runFrom (mark : Symbol)
    {tm : MultiTapeTM k Symbol State} {w e : List Symbol} {ws₀ ws₁ : Fin k → List Symbol}
    {t s : ℕ} (hrun : tm.runFrom (wordsCfg w (some tm.q₀) ws₀ []) t = wordsCfg w none ws₁ e)
    (hspace : tm.spaceUsed (wordsCfg w (some tm.q₀) ws₀ []) t ≤ s) :
    TransformsTapes (tm.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * (w.length + 2) + 2 * k + 6) := by
  rw [transformsTapes_iff_nil_output]
  rintro outer _ rfl
  -- set the flag, run `tm` on the virtual input tape, erase the flag
  obtain ⟨h₀, hs₀⟩ := runFrom_setFlag mark ws₀ w [] outer
  have h₁ : tm.inputFromTape.runFrom (inCfg mark (wordsCfg w (some tm.q₀) ws₀ []) outer) t =
      inCfg mark (wordsCfg w none ws₁ e) outer := by
    rw [runFrom_inCfg, hrun]
  obtain ⟨h₂, hs₂⟩ := runFrom_eraseFlag (State := State) mark ws₁ w e outer
  have h₁₂ := runFrom_seq h₁ rfl h₂ rfl
  rw [show t + 4 = 2 + (t + 2) by omega]
  refine ⟨_, e, runFrom_seq h₀ rfl h₁₂ rfl, ⟨rfl, rfl⟩, ?_⟩
  refine (spaceUsed_seq_le h₀ rfl (congrArg Cfg.state h₁₂)).trans <|
    (Nat.add_le_add_left (spaceUsed_seq_le h₁ rfl (congrArg Cfg.state h₂)) _).trans ?_
  have := spaceUsed_inputFromTape tm mark (wordsCfg w (some tm.q₀) ws₀ []) outer t
  omega

end Turing.MultiTapeTM
