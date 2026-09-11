/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Examples.TapeView

/-!
# The input head

The input tape of a `MultiTapeTM` is not a work tape. Its head is confined to
`Fin (input.length + 2)` and `moveInputPos` **clamps**: an attempt to step off either end produces
no movement, where a work tape would extend with blanks. So the finite stand-in cannot be a
`Tape`; it is a *cursor* into a finite list, whose moves are no-ops at the ends.

`padded input` is that finite list — a blank, the input, a blank — and `inputSymbol_eq` shows it
is exactly what the machine reads: `Cfg.inputSymbol` is its `inputPos`-th entry. `CursorRepr` then
ties a cursor to a position, and the three lemmas at the end show `cursorRead`, `cursorR` and
`cursorL` implement reading and `moveInputPos` faithfully.

Everything here is proved. The cursor operations also carry `Bounds` certificates built from the
primitives, so the input head costs the same as a work tape head.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

namespace Simulation

variable {α : Type}

/-- A cursor into a *finite* list: the cells before the head in reverse order, and the cells from
the head onwards. Unlike `Tape`, the head never leaves the list — moving off either end does
nothing, which is exactly `moveInputPos`'s clamping. -/
abbrev Cursor (α : Type) := List α × List α

/-- The cell under the cursor, or `d` past the end. -/
def cursorRead (d : α) (c : Cursor α) : α := c.2.head?.getD d

/-- Move right, unless that would take the head off the end. The default `d` is never read: it is
only there to make the projection total. -/
def cursorR (d : α) (c : Cursor α) : Cursor α :=
  cond c.2.tail.isEmpty c (c.2.head?.getD d :: c.1, c.2.tail)

/-- Move left, unless that would take the head off the start. -/
def cursorL (d : α) (c : Cursor α) : Cursor α :=
  cond c.1.isEmpty c (c.1.tail, c.1.head?.getD d :: c.2)

/-! ### Certificates, from the primitives -/

variable [DataEncode α]

/-- Reading the cursor is taking the head of its second component. -/
def cursorReadBounds (d : α) : Bounds (cursorRead d) :=
  (Bounds.comp (Bounds.headD d)
    Bounds.snd)

/-- Moving right: test whether the tail is empty, then either do nothing or shift one cell. -/
def cursorRBounds (d : α) : Bounds (cursorR d) :=
  (Bounds.ite
    (Bounds.comp Bounds.isEmpty
      (Bounds.comp Bounds.tail Bounds.snd))
    Bounds.id
    (Bounds.pair
      (Bounds.cons (Bounds.comp (Bounds.headD d)
          Bounds.snd)
        Bounds.fst)
      (Bounds.comp Bounds.tail
        Bounds.snd)))

/-- Moving left. -/
def cursorLBounds (d : α) : Bounds (cursorL d) :=
  (Bounds.ite
    (Bounds.comp Bounds.isEmpty Bounds.fst)
    Bounds.id
    (Bounds.pair
      (Bounds.comp Bounds.tail Bounds.fst)
      (Bounds.cons (Bounds.comp (Bounds.headD d)
          Bounds.fst)
        Bounds.snd)))

/-! ### The input tape as a finite list -/

/-- The input tape of a `MultiTapeTM` as a finite list: a blank cell, the input, a blank cell.
Entry `i` is what the machine reads when `inputPos = i`. -/
def padded {Symbol : Type} (input : List Symbol) : List (Option Symbol) :=
  none :: (input.map some ++ [none])

@[simp]
lemma padded_length {Symbol : Type} (input : List Symbol) :
    (padded input).length = input.length + 2 := by
  simp [padded]

/-- **What the machine reads is the padded input at the head position.** -/
lemma inputSymbol_eq {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (cfg : Cfg k Symbol State input) :
    cfg.inputSymbol = ((padded input)[cfg.inputPos.val]?).getD none := by
  have hlt := cfg.inputPos.isLt
  unfold Cfg.inputSymbol
  split_ifs with h₁ h₂
  · have hval : cfg.inputPos.val = 0 := by rw [h₁]; rfl
    simp [padded, hval]
  · simp [padded, h₂]
  · have hne0 : cfg.inputPos.val ≠ 0 := fun hz => h₁ (Fin.ext hz)
    obtain ⟨m, hm⟩ : ∃ m, cfg.inputPos.val = m + 1 := ⟨cfg.inputPos.val - 1, by omega⟩
    have hmlt : m < input.length := by omega
    have hmlt' : m < (List.map (some : Symbol → Option Symbol) input).length := by
      simpa using hmlt
    simp [padded, hm, List.getElem?_append_left hmlt', List.getElem?_map,
      List.getElem?_eq_getElem hmlt]

/-! ### A cursor represents a head position -/

/-- `c` is a cursor on the padded input with its head at `pos`. -/
def CursorRepr {Symbol : Type} (input : List Symbol) (c : Cursor (Option Symbol))
    (pos : Fin (input.length + 2)) : Prop :=
  c.1.length = pos.val ∧ c.1.reverse ++ c.2 = padded input

lemma CursorRepr.length_add {Symbol : Type} {input : List Symbol}
    {c : Cursor (Option Symbol)} {pos : Fin (input.length + 2)}
    (h : CursorRepr input c pos) : c.1.length + c.2.length = input.length + 2 := by
  have := congrArg List.length h.2
  simpa using this

/-- **Reading the cursor is reading the input tape.** -/
lemma cursorRead_eq {Symbol : Type} {input : List Symbol} {c : Cursor (Option Symbol)}
    {pos : Fin (input.length + 2)} (h : CursorRepr input c pos) :
    cursorRead none c = ((padded input)[pos.val]?).getD none := by
  have hlen : c.1.reverse.length = pos.val := by simpa using h.1
  rw [← h.2, List.getElem?_append_right (by omega), hlen]
  simp [cursorRead, List.head?_eq_getElem?]

/-- **Moving the cursor right implements `moveInputPos … .pos`.** -/
lemma cursorR_repr {Symbol : Type} {input : List Symbol} {c : Cursor (Option Symbol)}
    {pos : Fin (input.length + 2)} (d : Option Symbol) (h : CursorRepr input c pos) :
    CursorRepr input (cursorR d c) (moveInputPos pos .pos) := by
  have h1 := h.1
  have h2 := h.2
  have hsum := h.length_add
  have hpos := pos.isLt
  match hc : c.2 with
  | [] =>
    exfalso
    rw [hc] at hsum
    simp at hsum
    omega
  | [x] =>
    have hval : pos.val = input.length + 1 := by
      rw [hc] at hsum; simp at hsum; omega
    have hp : pos = (⟨input.length + 1, by omega⟩ : Fin (input.length + 2)) := Fin.ext hval
    have hmove : moveInputPos pos SignType.pos = pos := by
      rw [hp]; exact moveInputPos_rightBoundary
    have hfix : cursorR d c = c := by simp [cursorR, hc]
    rw [hmove, hfix]
    exact h
  | x :: y :: r =>
    have hne : pos.val ≠ input.length + 1 := by
      rw [hc] at hsum; simp at hsum; omega
    have hstep : cursorR d c = (x :: c.1, y :: r) := by simp [cursorR, hc]
    rw [moveInputPos_pos_of_ne_right pos hne, hstep]
    rw [hc] at h2
    exact ⟨by simp [h1], by simpa using h2⟩

/-- **Moving the cursor left implements `moveInputPos … .neg`.** -/
lemma cursorL_repr {Symbol : Type} {input : List Symbol} {c : Cursor (Option Symbol)}
    {pos : Fin (input.length + 2)} (d : Option Symbol) (h : CursorRepr input c pos) :
    CursorRepr input (cursorL d c) (moveInputPos pos .neg) := by
  have h1 := h.1
  have h2 := h.2
  match hc : c.1 with
  | [] =>
    have hval : pos.val = 0 := by rw [hc] at h1; simpa using h1.symm
    have hp : pos = 0 := Fin.ext (by simpa using hval)
    have hmove : moveInputPos pos SignType.neg = pos := by
      rw [hp]; exact moveInputPos_leftBoundary
    have hfix : cursorL d c = c := by simp [cursorL, hc]
    rw [hmove, hfix]
    exact h
  | x :: l =>
    have hne : pos ≠ 0 := by
      intro hp
      rw [hc, hp] at h1
      simp at h1
    have hstep : cursorL d c = (l, x :: c.2) := by simp [cursorL, hc]
    rw [moveInputPos_neg_of_ne_left pos hne, hstep]
    rw [hc] at h1 h2
    refine ⟨?_, ?_⟩
    · simp at h1 ⊢; omega
    · simpa using h2

end Simulation

end MultiTapeTM

end Turing
