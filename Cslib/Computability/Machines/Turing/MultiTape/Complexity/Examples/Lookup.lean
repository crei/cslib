/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives

/-!
# Example: association-list lookup

Looking a key up in an association list is a fold: walk the entries carrying the key and whatever
has been found so far. As with list indexing, the key has to live in the accumulator, because a
fold's step never sees the original input.

This is the piece a universal machine needs that a fixed transition function does not: its
transition table arrives on the input, so consulting it is a search rather than a case
distinction.

The accumulator bound is unusually easy here. When keys and values are finite types the whole
accumulator type `K × Option V` is finite, so its encoded size is bounded by a *constant* — no
membership argument of the kind `ListIndex` needed. The lookup therefore costs linear space
regardless of how large the table is.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

namespace Lookup

variable {K V : Type} [DataEncode K] [DataEncode V] [BEq K]

/-- An association list. -/
abbrev Table (K V : Type) := List (K × V)

/-- The list the lookup folds over: the table itself. -/
def lookupList (p : Table K V × K) : Table K V := p.1

/-- The initial accumulator: the key being searched for, and nothing found yet. -/
def lookupInit (p : Table K V × K) : K × Option V := (p.2, none)

/-- One step: keep whatever has already been found, otherwise take this entry if its key
matches. -/
def lookupStep (acc : K × Option V) (kv : K × V) : K × Option V :=
  (acc.1, cond acc.2.isSome acc.2 (cond (kv.1 == acc.1) (some kv.2) none))

/-- The value of the first entry with the given key, or `none`. -/
def firstMatch (k : K) : Table K V → Option V
  | [] => none
  | kv :: rest => cond (kv.1 == k) (some kv.2) (firstMatch k rest)

/-! ### Correctness of the fold -/

omit [DataEncode K] [DataEncode V] in
/-- Once a value has been found the fold keeps it: later matches cannot overwrite it. -/
lemma foldl_lookupStep_some (l : Table K V) (k : K) (v : V) :
    (l.foldl lookupStep (k, some v)).2 = some v := by
  induction l generalizing k v with
  | nil => rfl
  | cons kv l ih => simpa [lookupStep] using ih k v

omit [DataEncode K] [DataEncode V] in
/-- **The fold is a lookup.** -/
lemma foldl_lookupStep_none (l : Table K V) (k : K) :
    (l.foldl lookupStep (k, none)).2 = firstMatch k l := by
  induction l generalizing k with
  | nil => rfl
  | cons kv l ih =>
    rw [List.foldl_cons]
    change (l.foldl lookupStep (k, cond (kv.1 == k) (some kv.2) none)).2 = _
    cases h : kv.1 == k with
    | false => simpa [firstMatch, h] using ih k
    | true => simpa [firstMatch, h] using foldl_lookupStep_some l k kv.2

/-- Lookup, as the second component of the fold's result. -/
def lookupFn (p : Table K V × K) : Option V :=
  (foldFun lookupList lookupInit lookupStep p).2

omit [DataEncode K] [DataEncode V] in
@[simp]
lemma lookupFn_eq (tbl : Table K V) (k : K) : lookupFn (tbl, k) = firstMatch k tbl :=
  foldl_lookupStep_none tbl k

/-! ### Size bookkeeping -/

/-- Every accumulator of the lookup fold inhabits the finite type `K × Option V`, so its encoded
size is bounded by a constant of the types alone. -/
def accBound (K V : Type) [DataEncode K] [DataEncode V] [Fintype K] [Fintype V] : ℕ :=
  Finset.univ.sup fun a : K × Option V => (DataEncode.encode a).size

lemma lookupAccSize [Fintype K] [Fintype V] (p : Table K V × K) (j : ℕ) :
    (DataEncode.encode (foldAcc lookupList lookupInit lookupStep p j)).size ≤ accBound K V :=
  Finset.le_sup (f := fun a : K × Option V => (DataEncode.encode a).size) (Finset.mem_univ _)

omit [BEq K] in
/-! ### The certificate -/

/-- **A resource certificate for lookup**, from `Bounds.fold`. The step is a function between
finite types, and the accumulator bound is the constant `accBound`, so nothing beyond the
primitives is assumed. -/
def lookupBounds [Fintype K] [Fintype V] :
    Bounds (lookupFn : Table K V × K → Option V) :=
  let hl : Bounds (lookupList : Table K V × K → Table K V) :=
    Bounds.fst
  let hi : Bounds (lookupInit : Table K V × K → K × Option V) :=
    (Bounds.pair Bounds.snd
      (Bounds.const (none : Option V)))
  let hs : Bounds (Function.uncurry (lookupStep : K × Option V → K × V → K × Option V)) :=
    Bounds.ofFintype _
  Bounds.comp Bounds.snd
    (Bounds.fold hl hi hs (fun _ => accBound K V) monotone_const lookupAccSize)

end Lookup

end MultiTapeTM

end Turing
