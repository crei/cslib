/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing
namespace Routines

/-- If a tape contains the encoding of a function, navigates to the value part belonging
to a certain input and executes `tm`.
TODO: Can probably be implemented using find_list. -/
public def atFunctionValue {k : ℕ} (tm : MultiTapeTM k Char) (f input : Fin k) :
  MultiTapeTM k Char := sorry

/-- The index of the given value in the sorted list of all values of its type. -/
public def indexInType {α : Type} [Fintype α] [LinearOrder α] (x : α) : ℕ :=
  (Finset.univ.sort (· ≤ ·)).idxOf x

public lemma indexInTypeValid {α : Type} [Fintype α] [LinearOrder α] (x : α) :
  indexInType x < Fintype.card α := by
  simp [indexInType]
  sorry

@[simp]
public lemma atFunctionValue.eval_struct
    {α β : Type} [StrEnc α] [Fintype α] [LinearOrder α] [StrEnc β]
    {k : ℕ} (tm : MultiTapeTM k Char) {f input : Fin k}
    (h_ne : f ≠ input)
    {views : Fin k → TapeView}
    {x : α}
    {function : α → β}
    (h_input : (views input).current = StrEnc.toData x)
    (h_f : (views f).current = (StrEnc.ofFunction α β).toData function) :
    (atFunctionValue tm f input).eval_struct views = (tm.eval_struct
      (Function.update views f
        ((views f).appendPath''
            [indexInType x, 1] (by simp [h_f, function_graph, Data.atPath, indexInTypeValid])))).map
          fun views' => Function.update views' f ((views' f).parent.parent.setHeadPosOf (views f)) := by
  sorry

-- @[simp]
-- public lemma atPath_computes_function {k : ℕ} {path : List ℕ} {i j : Fin k}
--     {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
--     {tm : MultiTapeTM k Char}
--     (h_ne : i ≠ j)
--     (fPath : α → β)
--     (h_path : ∀ x, ((StrEnc.toData x).atPath path) = some (StrEnc.toData (fPath x)))
--     (f : β → γ → γ)
--     (h_tm : computes_function_read_update' tm f i j) :
--     computes_function_read_update' (atPath path i tm) (fun a => f (fPath a)) i j := by
--   intro x y views h_views_i h_views_j
--   have h_d := h_path x
--   clear h_path
--   change (atPath path i tm).eval_struct views =
--     Part.some (Function.update views j (TapeView.ofEnc (f (fPath x) y)))
--   generalize StrEnc.toData x = d at h_d h_views_i
--   generalize fPath x = b at h_d ⊢
--   induction path generalizing d views with
--   | nil =>
--     simp only [Data.atPath_nil, Option.some.injEq] at h_d
--     exact h_tm b y views (by simp [h_views_i, h_d]) h_views_j
--   | cons n path' ih =>
--     rw [show n :: path' = [n] ++ path' from rfl, Data.atPath_append] at h_d
--     obtain ⟨d₁, hd₁, h_tail⟩ := Option.bind_eq_some_iff.mp h_d
--     have h_valid : ((views i).current.atPath [n]).isSome := by simp [h_views_i, hd₁]
--     unfold atPath
--     rw [atElem_eval_struct h_valid]
--     rw [ih (Function.update views i ((views i).appendPath' n h_valid))
--         (by simp [h_ne.symm, h_views_j]) d₁ (by simp; grind) h_tail]
--     simp [h_ne]

end Routines
end Turing
