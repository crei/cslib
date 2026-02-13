/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.SuccRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.CopyRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PushRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.PopRoutine
public import Cslib.Computability.Machines.MultiTapeTuring.WhileCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes
public import Cslib.Computability.Machines.MultiTapeTuring.IteCombinator
public import Cslib.Computability.Machines.MultiTapeTuring.EqualRoutine

namespace Turing

variable [Inhabited α] [Fintype α]
variable {aux k : ℕ}

--- A Turing machine with a set of auxiliary tapes that are the last of the general tapes.
--- The auxiliary tapes are only relevant for the semantics of the machine:
--- The machine is required to reset the contents and head position of the auxiliary
--- tapes to their original values at the end of the computation.
public structure MultiTapeTMWithAuxTapes (k aux : ℕ) (α : Type)
    extends MultiTapeTM (k + aux) α

--- Adds `aux` many tapes to the TM, which are guaranteed to be restored to their original
--- content at the end of the computation.
@[simp, grind =]
public def MultiTapeTM.allocate_aux_tapes (tm : MultiTapeTM k α) (aux : ℕ) :
    MultiTapeTMWithAuxTapes k aux α where
  toMultiTapeTM := tm.extend (by omega)

--- Sets the last `aux` many tapes to be aux tapes, which are guaranteed to be restored to their
--- original content at the end of the computation.
@[simp, grind =]
public def MultiTapeTM.set_aux_tapes (aux : ℕ) (tm : MultiTapeTM (k + aux) α) :
    MultiTapeTMWithAuxTapes k aux α where
  toMultiTapeTM := tm

instance : Coe (MultiTapeTM k α) (MultiTapeTMWithAuxTapes k 0 α) where
  coe tm := tm.allocate_aux_tapes 0

namespace MultiTapeTMWithAuxTapes

--- We define `eval_list` only on the non-aux tapes and require that all aux tapes
--- are reset to their original contents.
public noncomputable def eval_list
    (tm : MultiTapeTMWithAuxTapes k aux (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part (Fin k → List (List α)) :=
  ⟨∃ final_tapes, ∀ existing_tapes : Fin (k + aux) → List (List α),
    tm.TransformsLists
      -- TODO maybe we need "extends" and "restricts" functions for tapes.
      (fun i => if h : i < k then tapes ⟨i, h⟩ else existing_tapes ⟨i, by omega⟩)
      (fun i => if h : i < k then final_tapes ⟨i, h⟩ else existing_tapes ⟨i, by omega⟩),
    fun h => h.choose⟩

--- Require a minimum number of auxiliary tapes, adding new ones if needed.
public def require_aux_tapes
  (tm : MultiTapeTMWithAuxTapes k aux α) (aux' : ℕ) :
    MultiTapeTMWithAuxTapes k (max aux aux') α where
  toMultiTapeTM := tm.toMultiTapeTM.extend (by omega)


--- Turn a TM with `k₁` tapes and `aux₁` many aux tapes into a TM with `k₂` tapes and `aux₂` many
--- aux tapes, where `seq` specifies which tapes of the new TM correspond to the tapes of the
--- old TM. Aux tapes are just assigned in order.
public def with_tapes
  {aux₁ aux₂ k₁ k₂ : ℕ}
  {h_le_k : k₁ ≤ k₂}
  {h_le_aux : aux₁ ≤ aux₂}
  (tm : MultiTapeTMWithAuxTapes k₁ aux₁ α)
  (seq : Vector (Fin k₂) k₁) : MultiTapeTMWithAuxTapes k₂ aux₂ α :=
  (tm.toMultiTapeTM.with_tapes (h_le := by omega) (
    ((seq.map fun (t : Fin k₂) => (⟨t, by omega⟩)) : (Vector (Fin (k₂ + aux₂)) k₁)) ++
    (((.ofFn fun i => ⟨k₂ + i, by omega⟩) : (Vector (Fin (k₂ + aux₂)) aux₁))))).set_aux_tapes aux₂

--- Run tm₂ after tm₁ has terminated.
public def seq (tm₁ tm₂ : MultiTapeTMWithAuxTapes k aux α) : MultiTapeTMWithAuxTapes k aux α :=
  sorry

-- TODO this requires the auxiliary tapes to be empty between the two computations (because of
-- the use of eval_list).
-- Do we need that?
@[simp, grind=]
public theorem seq_eval_list
  {tm₁ tm₂ : MultiTapeTMWithAuxTapes k aux (WithSep α)}
  {tapes₀ : Fin k → List (List α)} :
  (seq tm₁ tm₂).eval_list tapes₀ =
    tm₁.eval_list tapes₀ >>= fun tape₁ => tm₂.eval_list tape₁ := by
  sorry

public theorem seq_associative
  (tm₁ tm₂ tm₃ : MultiTapeTMWithAuxTapes k aux α)
  (tapes₀ : Fin k → List (List α)) :
  (seq (seq tm₁ tm₂) tm₃).eval = (seq tm₁ (seq tm₂ tm₃)).eval := by
  sorry

infixl:90 " <;a> " => seq

end MultiTapeTMWithAuxTapes

end Turing
