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
public import Cslib.Computability.Machines.MultiTapeTuring.WithTapes

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

@[simp]
public abbrev tapes_take
  (tapes : Fin k → List (List α))
  (k' : ℕ)
  (h_le : k' ≤ k) : Fin k' → List (List α) :=
  fun i => tapes ⟨i, by omega⟩

@[simp]
public lemma Function.update_tapes_take
    {α}
    (k : ℕ)
    {k' : ℕ}
    {h_le : k' ≤ k}
    {tapes : Fin k → List (List α)}
    {p : Fin k'}
    {v : List (List α)} :
  Function.update (tapes_take tapes k' h_le) p v =
    tapes_take (Function.update tapes ⟨p,  by omega⟩ v) k' h_le := by
  sorry

@[simp]
public abbrev tapes_extend_by
  (tapes : Fin k → List (List α))
  (extend_by : Fin (k + aux) → List (List α)) :
  Fin (k + aux) → List (List α) :=
  fun i => if h : i < k then tapes ⟨i, h⟩ else extend_by i

--- Extends the number of tapes (lists) from `k` to `k + aux` by adding empty lists.
@[simp]
public abbrev tapes_extend (tapes : Fin k → List (List α)) : Fin (k + aux) → List (List α) :=
  tapes_extend_by tapes (fun _ => [])

--- Reduces the number of tapes from `k + aux` to `k` if all the removed tapes (lists) are empty.
@[simp, grind =]
public def try_reduce_tapes_if_empty (tapes : Fin (k + aux) → List (List α)) :
    Option (Fin k → List (List α)) :=
  if ∀ i, (h : i < aux) → tapes ⟨k + i, by omega⟩ = [] then
    some fun i => tapes ⟨i, by omega⟩
  else
    none

namespace MultiTapeTMWithAuxTapes

--- We define `eval_list` only on the non-aux tapes and require that when run on empty aux
--- tapes, they are reset to empty at the end. If this is not the case, this function evaluates
--- to `Part.none` even if the machine halts.
--- The stricter requirement is that the aux tapes are also reset to their original
--- contents when they are not empty, but it is not practical to model this here.
@[simp, grind =]
public noncomputable def eval_list_aux
    (tm : MultiTapeTMWithAuxTapes k aux (WithSep α))
    (tapes : Fin k → List (List α)) :
    Part (Fin k → List (List α)) :=
  (tm.toMultiTapeTM.eval_list (tapes_extend tapes)).bind
    fun tapes => try_reduce_tapes_if_empty tapes

@[simp, grind =]
public lemma set_aux_tapes_eval_list {α}
  (tm : MultiTapeTM (k + aux) (WithSep α))
  (tapes : Fin k → List (List α)) :
  (tm.set_aux_tapes aux).eval_list_aux tapes =
    (tm.eval_list (tapes_extend tapes)).bind fun tapes => try_reduce_tapes_if_empty tapes := by
  simp

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

-- --- Semantics of tm.with_tapes when tm is a 3-tape Turing machine.
-- @[simp, grind =]
-- public theorem with_tapes_eval_list_3
--   {i j l : Fin k}
--   (tm : MultiTapeTMWithAuxTapes 3 aux (WithSep α))
--   (tapes : Fin k → List (List α)) :
--   (tm.with_tapes #v[i, j, l]).eval_list tapes =
--     (tm.eval_list (fun _ => tapes j)).map
--     (fun tapes' t => if t = j then tapes' 0 else tapes t) := by
--   unfold MultiTapeTM.with_tapes
--   have h_tapes :
--     ((fun tapes'' : Fin k.succ → BiTape α => tapes'' ∘ Equiv.swap 0 j) ∘
--     (fun (tapes'' : Fin 1 → BiTape α) i =>
--       if h : i = 0 then tapes'' ⟨i, by simp [h]⟩ else tapes (Equiv.swap 0 j i))) =
--     fun tapes' => (fun t => if t = j then tapes' 0 else tapes t) := by
--     grind
--   simp [Part.map_map, h_tapes]

-- --- Semantics of tm.with_tapes when tm is a 3-tape Turing machine.
-- @[simp, grind =]
-- public theorem with_tapes_eval_3
--   {j : Fin k.succ}
--   (tm : MultiTapeTMWithAuxTapes 3 aux α)
--   (tapes : Fin k.succ → BiTape α) :
--   (tm.with_tapes #v[j] (h_le := by omega)).eval tapes =
--     (tm.eval (fun _ => tapes j)).map
--     (fun tapes' t => if t = j then tapes' 0 else tapes t) := by
--   unfold MultiTapeTM.with_tapes
--   have h_tapes :
--     ((fun tapes'' : Fin k.succ → BiTape α => tapes'' ∘ Equiv.swap 0 j) ∘
--     (fun (tapes'' : Fin 1 → BiTape α) i =>
--       if h : i = 0 then tapes'' ⟨i, by simp [h]⟩ else tapes (Equiv.swap 0 j i))) =
--     fun tapes' => (fun t => if t = j then tapes' 0 else tapes t) := by
--     grind
--   simp [Part.map_map, h_tapes]

--- Run tm₂ after tm₁ has terminated.
-- public def seq (tm₁ tm₂ : MultiTapeTMWithAuxTapes k aux α) : MultiTapeTMWithAuxTapes k aux α :=
--   (MultiTapeTM.seq tm₁ tm₂).set_aux_tapes aux

-- -- TODO this requires the auxiliary tapes to be empty between the two computations (because of
-- -- the use of eval_list).
-- -- Do we need that?
-- @[simp, grind=]
-- public theorem seq_eval_list_aux
--   {tm₁ tm₂ : MultiTapeTMWithAuxTapes k aux (WithSep α)}
--   {tapes₀ : Fin k → List (List α)} :
--   (seq tm₁ tm₂).eval_list_aux tapes₀ =
--     tm₁.eval_list_aux tapes₀ >>= fun tape₁ => tm₂.eval_list_aux tape₁ := by
--   sorry

-- @[simp, grind=]
-- public theorem seq_eval_list
--   {tm₁ tm₂ : MultiTapeTMWithAuxTapes k aux (WithSep α)}
--   {tapes₀ : Fin (k + aux) → List (List α)} :
--   (seq tm₁ tm₂).eval_list tapes₀ =
--     tm₁.eval_list tapes₀ >>= fun tape₁ => tm₂.eval_list tape₁ := by
--   sorry

-- public theorem seq_associative
--   (tm₁ tm₂ tm₃ : MultiTapeTMWithAuxTapes k aux α)
--   (tapes₀ : Fin k → List (List α)) :
--   (seq (seq tm₁ tm₂) tm₃).eval = (seq tm₁ (seq tm₂ tm₃)).eval := by
--   sorry

-- infixl:90 " <;a> " => seq

end MultiTapeTMWithAuxTapes

end Turing
