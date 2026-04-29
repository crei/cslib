/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Iterate
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Skip
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed


namespace Turing
namespace Routines



/-- Run `tm` at the left end of the current item, restoring to the original position afterwards. -/
public def atLeft {k : ℕ} (i : Fin k) (tm : MultiTapeTM k Char) : MultiTapeTM k Char :=
  if_eq '(' i tm (toLeftEnd i;ₜ tm;ₜ toRightEnd i)

@[simp]
public lemma atLeft_eval_struct {k : ℕ} {i : Fin k} (tm : MultiTapeTM k Char)
  {views : Fin k → TapeView} :
    (atLeft i tm).eval_struct views =
      (tm.eval_struct (Function.update views i ((views i).toLeftEnd))).map
        (fun views' => Function.update views' i ((views' i).setHeadPosOf (views i))) := by
  simp [atLeft]
  sorry -- TOOD prove by AI


def skipRight_n {k : ℕ} (n : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  iterate_n (skipRight i) n

-- TODO maybe we can change this to
-- lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k}
--     {views : Fin k → TapeView}
--     (h_valid : ((views i).parent.current.atPath [j + n]).isSome)
--     (h_parent : (views i) = (views i).parent.appendPath j
--           (Data.atPath_isSome_of_le_isSome (by simp) h_valid))
--     (h_left : (views i).headPos = .leftEnd) :


lemma skipRight_n.eval_struct {j n : ℕ} {k : ℕ} {i : Fin k}
    {views : Fin k → TapeView}
    {parent : TapeView}
    (h_valid : (parent.current.atPath [j + n]).isSome)
    (h_left : parent.headPos = .leftEnd)
    (h_parent : (views i) = parent.appendPath j
          (Data.atPath_isSome_of_le_isSome (by simp) h_valid)) :
    (skipRight_n n i).eval_struct views = .some (Function.update views i
      ((views i).parent.appendPath (j + n)
        (by simpa [h_parent] using h_valid))) := by
  induction n generalizing j views with
  | zero => simp [skipRight_n, iterate_n_zero, h_parent]
  | succ n ih =>
    have h_j1 : (parent.current.atPath [j + 1]).isSome :=
      Data.atPath_isSome_of_le_isSome (by omega) h_valid
    simp only [skipRight_n, iterate_n_succ, seq_eval_struct]
    rw [skipRight_eval_struct
      (by simp [h_parent]) (by simp [h_parent, h_left])]
    simp only [Part.bind_some, h_parent,
      TapeView.appendPath, TapeView.parent, List.dropLast_concat,
      List.getLast?_concat, Option.get_some, Nat.succ_eq_add_one]
    rw [dif_pos h_j1,
      show iterate_n (skipRight i) n = skipRight_n n i from rfl,
      ih (by rwa [show j + 1 + n = j + (n + 1) from by omega])
        (by simp)]
    simp only [Function.update_idem, Function.update_self,
      TapeView.appendPath, TapeView.parent, List.dropLast_concat,
      show j + 1 + n = j + (n + 1) from by omega]


/-- If positioned on the element of a list, navigates to the list containing it. -/
public def outOfList {k : ℕ} (i : Fin k) : MultiTapeTM k Char :=
  left i;ₜ while_eq ')' i (right i;ₜ skipLeft i;ₜ left i)

-- ((1)(2)(3))

lemma outOfList_inner {k : ℕ} {i : Fin k}
    (views : Fin k → TapeView)
    {tv : TapeView}
    (idx : ℕ)
    (path : List ℕ)
    (h_path : tv.path = path ++ [idx.succ])
    (h_left : tv.headPos = .leftEnd) :
  (right i;ₜ skipLeft i;ₜ left i).eval_tot (by grind)
    (Function.update (TapeView.toBiTape ∘ views) i tv.toBiTape.move_left) =
     Function.update (TapeView.toBiTape ∘ views) i
       (tv.parent.appendPath idx (by
           apply Data.atPath_isSome_of_succ_isSome
           sorry
         )).toBiTape.move_left := by
  sorry

/-- `outOfArg i` ascends back from within a list to the list itself. -/
@[simp]
public lemma outOfList_eval_struct {k : ℕ} {i : Fin k} {views : Fin k → TapeView} :
  (outOfList i).eval_struct views = some (Function.update views i (views i).parent) := by sorry


/-- Navigate to the `idx`-th element of a `Data.list` encoding on tape `i`.
Moves past `(` and then skips `idx` Data elements.
If `i` is larger than the length of the list, does nothing. -/
public def toElem {k : ℕ} (idx : ℕ) (i : Fin k) : MultiTapeTM k Char :=
  toLeftEnd i;ₜ right i;ₜ skipRight_n idx i

/-- `toElem idx i` moves to the `idx`th element of the `Data.list` currently pointed to
on tape `i`. -/
@[simp]
public lemma toElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {views : Fin k → TapeView}
  (h_valid : ((views i).current.atPath [idx]).isSome) :
  (toElem idx i).eval_struct views = .some
    (Function.update views i ((views i).appendPath' idx h_valid)) := by
  have h_ne : (views i).current ≠ Data.list [] :=
    Data.atPath_zero_isSome_of_nonempty.mp
      (Data.atPath_isSome_of_le_isSome (by omega) h_valid)
  simp only [toElem, seq_eval_struct, toLeftEnd_eval_struct, Part.bind_some, right_eval_struct,
    Part.bind_some, Function.update_idem, Function.update_self,
    show ¬(views i).toLeftEnd.current = Data.list [] from h_ne, ↓reduceDIte]
  rw [skipRight_n.eval_struct (j := 0) (parent := (views i).toLeftEnd)
      (by simpa using h_valid) (by simp) (by simp)]
  simp

-- TODO this has a double toLeftEnd which is not needed.

/-- Execute `tm` at a certain element of the list. -/
public def atElem {k : ℕ} (idx : ℕ) (i : Fin k) (tm : MultiTapeTM k Char) : MultiTapeTM k Char :=
  atLeft i (toElem idx i;ₜ tm;ₜ outOfList i)

@[simp]
public lemma atElem_eval_struct {k : ℕ} {idx : ℕ} {i : Fin k} {tm : MultiTapeTM k Char}
    {views : Fin k → TapeView}
    (h_valid : ((views i).current.atPath [idx]).isSome) :
    (atElem idx i tm).eval_struct views = (tm.eval_struct
      (Function.update views i ((views i).appendPath' idx h_valid))).map
        fun views' => Function.update views' i ((views' i).parent.setHeadPosOf (views i)) := by
  simp [atElem, h_valid, Part.bind_some_eq_map]

/-- The semantics of `atElem` when applied to a static index. This is not really useful
when applied to a `List` because `fElem` needs to compute the elem for any valid `x` of the type. -/
@[simp]
public lemma atElem_computes_function {k : ℕ} {idx : ℕ} {i j : Fin k}
    {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
    {tm : MultiTapeTM k Char}
    (h_ne : i ≠ j)
    (fElem : α → β)
    (h_elem : ∀ x, ((StrEnc.toData x).atPath [idx]) = some (StrEnc.toData (fElem x)))
    (f : β → γ → γ)
    (h_tm : computes_function_read_update' tm f i j) :
    computes_function_read_update' (atElem idx i tm) (fun a => f (fElem a)) i j := by
  intro x y views h_views_i h_views_j
  rw [atElem_eval_struct (by simp [h_views_i, h_elem])]
  rw [h_tm (fElem x) y _ (by simp; grind) (by grind)]
  simp only [Part.map_some, Part.some_inj]
  funext r
  by_cases hri : r = i
  · subst hri
    simp [h_ne]
  · grind

-- TODO this has a double toLeftEnd which is not needed.

/-- Move into the given path, then execute `tm` and then move out again. -/
public def atPath {k : ℕ} (path : List ℕ) (i : Fin k) (tm : MultiTapeTM k Char) :
    MultiTapeTM k Char :=
  match path with
  | [] => tm
  | n :: path' => atElem n i (atPath path' i tm)

@[simp]
public lemma atPath_computes_function {k : ℕ} {path : List ℕ} {i j : Fin k}
    {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
    {tm : MultiTapeTM k Char}
    (h_ne : i ≠ j)
    (fPath : α → β)
    (h_path : ∀ x, ((StrEnc.toData x).atPath path) = some (StrEnc.toData (fPath x)))
    (f : β → γ → γ)
    (h_tm : computes_function_read_update' tm f i j) :
    computes_function_read_update' (atPath path i tm) (fun a => f (fPath a)) i j := by
  intro x y views h_views_i h_views_j
  suffices h : ∀ {path : List ℕ} {d : Data} {b : β},
      d.atPath path = some (StrEnc.toData b) →
      ∀ (views : Fin k → TapeView),
        (views i).current = d → views j = TapeView.ofEnc y →
        (atPath path i tm).eval_struct views =
          .some (Function.update views j (TapeView.ofEnc (f b y))) from
    h (h_path x) views h_views_i h_views_j
  clear h_views_i h_views_j h_path views x
  intro path
  induction path with
  | nil =>
    intro d b h_d views h_i h_j
    simp only [Data.atPath_nil, Option.some.injEq] at h_d
    exact h_tm b y views (by simp [h_i, h_d]) h_j
  | cons n path' ih =>
    intro d b h_d views h_i h_j
    rw [show n :: path' = [n] ++ path' from rfl, Data.atPath_append] at h_d
    obtain ⟨d₁, hd₁, h_tail⟩ := Option.bind_eq_some_iff.mp h_d
    have h_valid : ((views i).current.atPath [n]).isSome := by simp [h_i, hd₁]
    unfold atPath
    rw [atElem_eval_struct h_valid,
      ih h_tail _ (by simp [h_i, hd₁]) (by simp [h_ne.symm, h_j])]
    simp only [Part.map_some, Part.some_inj]
    funext r
    by_cases hri : r = i
    · subst hri; simp [h_ne]
    · grind


end Routines
end Turing
