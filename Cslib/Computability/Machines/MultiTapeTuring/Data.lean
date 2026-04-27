/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Dyadic
public import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Linarith

namespace Turing


/-- Universal data type for structured TM computation. -/
public inductive Data where
  /-- A list of data values. -/
  | list : List Data → Data

/-- Extract the list of children from a `Data` value. -/
@[expose]
public abbrev Data.toList : Data → List Data
  | .list ds => ds

mutual
  /-- TODO document -/
  public def Data.decEq : (a b : Data) → Decidable (a = b)
    | .list l₁, .list l₂ =>
      match Data.decEqList l₁ l₂ with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun h' => h (Data.list.inj h'))

  /-- TODO document -/
  public def Data.decEqList : (l₁ l₂ : List Data) → Decidable (l₁ = l₂)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse nofun
    | a :: as, b :: bs =>
      match Data.decEq a b, Data.decEqList as bs with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
      | _, isFalse h₂ =>
        isFalse (fun h => h₂ (List.tail_eq_of_cons_eq h))
      | isFalse h₁, _ =>
        isFalse (fun h => h₁ (List.head_eq_of_cons_eq h))
end

public instance : DecidableEq Data := Data.decEq


-- ═══════════════════════════════════════════════════════════════════════════
-- Data.atPath
-- ═══════════════════════════════════════════════════════════════════════════

/-- Navigate into a `Data` value at the given path.
    Returns the sub-`Data` element at the path, or `none` if the path is invalid
    (e.g., through out-of-bounds on a `list`). -/
@[expose]
public def Data.atPath : Data → List ℕ → Option Data
  | d, [] => some d
  | Data.list ds, k :: rest =>
    if h : k < ds.length then (ds[k]).atPath rest else none

@[simp]
public lemma Data.atPath_nil (d : Data) : d.atPath [] = some d := by
  unfold Data.atPath; rfl

@[simp]
public lemma Data.atPath_list_cons (ds : List Data) (k : ℕ) (rest : List ℕ)
    (h : k < ds.length) :
    (Data.list ds).atPath (k :: rest) = (ds[k]).atPath rest := by
  simp [Data.atPath, h]

@[simp]
public lemma Data.atPath_zero_isSome_of_nonempty {d : Data} :
    (d.atPath [0]).isSome ↔ (d ≠ .list []) := by
  cases d with
  | list ds =>
    simp only [Data.atPath, ne_eq, Data.list.injEq]
    cases ds with
    | nil => simp
    | cons d ds => simp


@[simp]
public lemma Data.atPath_append {d : Data} {path₁ path₂ : List ℕ} :
    d.atPath (path₁ ++ path₂) = d.atPath path₁ >>= fun d => d.atPath path₂ := by
  induction path₁ generalizing d with
  | nil => simp [Data.atPath]
  | cons k rest ih =>
    cases d with
    | list ds => grind [Data.atPath]

@[simp]
public lemma Data.atPath_get_atPath {d : Data} {path₁ path₂ : List ℕ}
    (h_valid : (d.atPath path₁).isSome) :
    ((d.atPath path₁).get h_valid).atPath path₂ =
      d.atPath (path₁ ++ path₂) := by
  rw [Data.atPath_append]
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp h_valid
  simp [hd']

@[simp]
public lemma Data.atPath_dropLast_isSome_of_isSome {d : Data} {path : List ℕ}
    (h_is_some : (d.atPath path).isSome) :
  (d.atPath path.dropLast).isSome := by
  induction path using List.reverseRecOn with
  | nil => exact h_is_some
  | append_singleton l a _ =>
    rw [List.dropLast_concat]
    rw [Data.atPath_append] at h_is_some
    cases hd : d.atPath l with
    | none => simp [hd, Option.bind] at h_is_some
    | some d' => simp

@[simp]
public lemma Data.atPath_dropLast_bind_getLast {d : Data} {path : List ℕ}
    (h_path : path.getLast?.isSome) :
    ((d.atPath path.dropLast).bind fun d => d.atPath [path.getLast?.get h_path]) =
      d.atPath path := by
  conv_rhs => rw [show path = path.dropLast ++ [path.getLast?.get h_path] from by
    simp [List.dropLast_append_getLast?]]
  simp [Data.atPath_append]

public lemma Data.atPath_isSome_of_le_isSome {d : Data} {i₁ i₂ : ℕ}
    (h_le : i₁ ≤ i₂)
    (h_is_some : (d.atPath [i₂]).isSome) :
  (d.atPath [i₁]).isSome := by
  cases d with
  | list ds =>
    unfold Data.atPath at h_is_some ⊢
    split at h_is_some
    · split
      · rfl
      · rename_i h₂ h₁; exact absurd (by omega : i₁ < ds.length) h₁
    · simp at h_is_some

-- TODO redundant?
@[simp]
public lemma Data.atPath_isSome_of_succ_isSome {d : Data} {idx : ℕ}
    (h_succ_is_some : (d.atPath [idx + 1]).isSome) :
  (d.atPath [idx]).isSome :=
  Data.atPath_isSome_of_le_isSome (by omega) h_succ_is_some

-- ═══════════════════════════════════════════════════════════════════════════
-- Data.enc
-- ═══════════════════════════════════════════════════════════════════════════

/-- Encoding of `Data` into a list of characters. -/
@[expose]
public def Data.enc : Data → List Char
  | Data.list ds => ['('] ++ (ds.map Data.enc).flatten ++ [')']

@[simp]
public lemma Data.enc_list (ds : List Data) :
    Data.enc (Data.list ds) = ['('] ++ (ds.map Data.enc).flatten ++ [')'] := by
  unfold Data.enc; rfl

@[simp]
public lemma Data.enc_ne_nil (d : Data) : d.enc ≠ [] := by
  cases d with
  | list ds => simp [Data.enc_list]

@[simp]
public lemma Data.enc_length_pos (d : Data) : 0 < d.enc.length := by
  cases d with
  | list ds => simp [Data.enc_list]

@[simp]
public lemma Data.enc_getElem_zero (d : Data) :
    d.enc[0]'(Data.enc_length_pos d) = '(' := by
  cases d with | list ds => simp [Data.enc_list]

@[simp]
public lemma Data.enc_getLast (d : Data) :
    d.enc.getLast (by simp) = ')' := by
  cases d with | list ds => simp [Data.enc_list]

@[simp]
public lemma Data.enc_getElem_last (d : Data) :
    d.enc[d.enc.length - 1]'(by simp) = ')' := by
  cases d with
  | list ds =>
    simp [Data.enc_list]

-- ─── Balance machinery for prefix-freeness ───────────────────────────────

private def bw (c : Char) : Int :=
  if c = '(' then 1
  else if c = ')' then -1
  else 0

private def bal (l : List Char) : Int := (l.map bw).sum

@[simp] private lemma bal_nil : bal [] = 0 := rfl

@[simp] private lemma bal_cons (c : Char) (l : List Char) :
    bal (c :: l) = bw c + bal l := by simp [bal]

@[simp] private lemma bal_append (l₁ l₂ : List Char) :
    bal (l₁ ++ l₂) = bal l₁ + bal l₂ := by
  simp [bal, List.map_append, List.sum_append]


/-- Balance at interior positions of a flatten of balanced segments is non-negative. -/
private lemma bal_flatten_take_nonneg
    (segs : List (List Char))
    (h_bal : ∀ s ∈ segs, bal s = 0)
    (h_pos : ∀ s ∈ segs, ∀ i, 0 < i → i < s.length → 0 < bal (s.take i))
    (j : ℕ) (hj : j ≤ segs.flatten.length) :
    0 ≤ bal (segs.flatten.take j) := by
  induction segs generalizing j with
  | nil => simp [bal]
  | cons s ss ih =>
    simp only [List.flatten_cons] at hj ⊢
    rcases le_or_gt j s.length with hle | hgt
    · rw [List.take_append_of_le_length hle]
      rcases Nat.eq_or_lt_of_le hle with rfl | hjlt
      · rw [List.take_length]; linarith [h_bal s (.head ..)]
      · rcases j with _ | j
        · simp [bal]
        · linarith [h_pos s (.head ..) (j + 1) (by omega) hjlt]
    · rw [List.take_append, List.take_of_length_le (by omega)]
      simp only [bal_append, h_bal s (.head ..), zero_add]
      exact ih (fun t ht => h_bal t (.tail _ ht))
              (fun t ht => h_pos t (.tail _ ht))
              _ (by simp only [List.length_append] at hj; omega)

/-- Balance of each encoding is 0 and positive at every interior position. -/
private lemma Data.enc_bal (d : Data) :
    bal d.enc = 0 ∧ ∀ i, 0 < i → i < d.enc.length → 0 < bal (d.enc.take i) := by
  match d with
  | .list ds =>
    simp only [Data.enc_list]
    have ih d' (_ : d' ∈ ds) := Data.enc_bal d'
    have bal_flat : bal (ds.map Data.enc).flatten = 0 := by
      induction ds with
      | nil => simp [bal]
      | cons d ds' ihds =>
        simp only [List.map_cons, List.flatten_cons, bal_append,
            (ih d (.head ..)).1, ihds (fun d' hd' => ih d' (.tail _ hd')), zero_add]
    have bal_flat_nonneg j (hj : j ≤ (ds.map Data.enc).flatten.length) :=
      bal_flatten_take_nonneg (ds.map Data.enc)
        (fun s hs => by obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hs; exact (ih d' hd').1)
        (fun s hs k hk hkl => by
          obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hs; exact (ih d' hd').2 k hk hkl)
        j hj
    set flat := (ds.map Data.enc).flatten
    constructor
    · simp only [bal_append, bal_cons, bal_flat]; decide
    · intro i hi hlt
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      change 0 < bal (('(' :: (flat ++ [')'])).take i)
      match i, hi with
      | i + 1, _ =>
        simp only [List.take_succ_cons, bal_cons,
            List.take_append_of_le_length (show i ≤ flat.length by omega)]
        linarith [bal_flat_nonneg i (by omega), show bw '(' = (1 : Int) from by decide]
  termination_by sizeOf d

/-- A proper prefix of any encoding leads to a balance contradiction. -/
private lemma Data.enc_no_proper_prefix {d₁ d₂ : Data}
    (hpfx : d₁.enc <+: d₂.enc) (hne : d₁.enc ≠ d₂.enc) : False := by
  obtain ⟨t, ht⟩ := hpfx
  have hlt : d₁.enc.length < d₂.enc.length := by
    have htne : t ≠ [] := fun h => hne (by rw [← ht, h, List.append_nil])
    rw [← ht, List.length_append]
    exact Nat.lt_add_of_pos_right (List.length_pos_of_ne_nil htne)
  linarith [(Data.enc_bal d₂).2 d₁.enc.length (Data.enc_length_pos d₁) hlt,
    show bal (d₂.enc.take d₁.enc.length) = 0 from by
      rw [← ht, List.take_append_of_le_length le_rfl, List.take_length]
      exact (Data.enc_bal d₁).1]

-- ─── Injectivity ─────────────────────────────────────────────────────────

/-- Extract inner content from bracket-delimited encodings. -/
private lemma cons_append_inj {a : α} {l₁ l₂ : List α} {b : α}
    (h : [a] ++ l₁ ++ [b] = [a] ++ l₂ ++ [b]) : l₁ = l₂ :=
  List.append_cancel_right (List.cons.inj h).2

/-- Extract a prefix from an append equality. -/
private lemma prefix_of_append_eq {l₁ l₂ r₁ r₂ : List α}
    (h : l₁ ++ r₁ = l₂ ++ r₂) (hle : l₁.length ≤ l₂.length) : l₁ <+: l₂ := by
  have h1 := congrArg (List.take l₁.length) h
  rw [List.take_append_of_le_length le_rfl, List.take_length,
      List.take_append_of_le_length hle] at h1
  exact h1 ▸ List.take_prefix l₁.length l₂

mutual

/-- Injectivity of `Data.enc` (internal, mutual with flatten helper). -/
private def Data.enc_injective_mut (d₁ d₂ : Data) (h : d₁.enc = d₂.enc) :
    d₁ = d₂ :=
  match d₁, d₂ with
  | .list ds₁, .list ds₂ => by
    simp only [Data.enc_list] at h
    exact congrArg Data.list (enc_flatten_injective_mut ds₁ ds₂ (cons_append_inj h))

/-- Flatten of encodings is injective. -/
private def enc_flatten_injective_mut
    (ds₁ ds₂ : List Data)
    (h : (ds₁.map Data.enc).flatten = (ds₂.map Data.enc).flatten) :
    ds₁ = ds₂ := by
  match ds₁, ds₂ with
  | [], [] => rfl
  | [], d :: _ | d :: _, [] =>
    simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
    exact absurd (congrArg List.length h) (by
      simp only [List.length_nil, List.length_append]; have := Data.enc_length_pos d; omega)
  | d₁ :: ds₁, d₂ :: ds₂ =>
    simp only [List.map_cons, List.flatten_cons] at h
    have heq : d₁.enc = d₂.enc := by
      by_contra hne
      rcases le_or_gt d₁.enc.length d₂.enc.length with hle | hlt
      · exact Data.enc_no_proper_prefix (prefix_of_append_eq h hle) hne
      · exact Data.enc_no_proper_prefix (prefix_of_append_eq h.symm hlt.le) (Ne.symm hne)
    rw [Data.enc_injective_mut d₁ d₂ heq] at h ⊢
    exact congrArg (d₂ :: ·) (enc_flatten_injective_mut ds₁ ds₂ (List.append_cancel_left h))

end

public lemma Data.enc_injective : Function.Injective Data.enc :=
  fun d₁ d₂ h => Data.enc_injective_mut d₁ d₂ h

/-- No `Data.enc` is a proper prefix of another. -/
public lemma Data.enc_prefix_free {d₁ d₂ : Data}
    (h : d₁.enc <+: d₂.enc) : d₁ = d₂ := by
  rcases h with ⟨t, ht⟩
  have : t = [] := by
    by_contra htne
    exact Data.enc_no_proper_prefix ⟨t, ht⟩ (by rw [← ht]; simp [htne])
  exact Data.enc_injective_mut d₁ d₂ (by rwa [this, List.append_nil] at ht)

/-- No `Data.enc` is a proper suffix of another (balance argument). -/
public lemma Data.enc_suffix_free {d₁ d₂ : Data}
    (h : d₁.enc <:+ d₂.enc) : d₁ = d₂ := by
  obtain ⟨t, ht⟩ := h
  rcases t with _ | ⟨a, t⟩
  · exact Data.enc_injective (by simpa using ht)
  · exfalso
    have hlt : (a :: t).length < d₂.enc.length := by simp [← ht]
    have h_bal_t : bal (a :: t) = 0 := by
      have : bal d₂.enc = bal (a :: t) + bal d₁.enc := by
        rw [← ht]; exact bal_append _ _
      linarith [(Data.enc_bal d₁).1, (Data.enc_bal d₂).1]
    have h_take : d₂.enc.take (a :: t).length = (a :: t) := by
      rw [← ht, List.take_append_of_le_length le_rfl, List.take_length]
    have h_pos : 0 < bal (d₂.enc.take (a :: t).length) :=
      (Data.enc_bal d₂).2 (a :: t).length (by simp) hlt
    linarith [show bal (d₂.enc.take (a :: t).length) = bal (a :: t) from by rw [h_take]]

/-- Typeclass for types that can be encoded as `Data` for TM computation. -/
public class StrEnc (α : Type*) where
  /-- Map a value to its `Data` representation. -/
  toData : α → Data
  /-- Attempt to decode a `Data` value back into the type.
      Returns `none` if the `Data` does not represent a valid value of the type. -/
  fromData : Data → Option α
  /-- `fromData` is the partial inverse of `toData`: it succeeds with `x` exactly
      when its input is the canonical encoding of `x`. -/
  fromData_eq_some_iff : ∀ {d : Data} {x : α}, fromData d = some x ↔ toData x = d

/-- Decoding after encoding always succeeds and returns the original value. -/
@[simp]
public lemma StrEnc.fromData_toData {α : Type*} [StrEnc α] (x : α) :
    StrEnc.fromData (StrEnc.toData x) = some x :=
  StrEnc.fromData_eq_some_iff.mpr rfl

/-- If decoding succeeds, re-encoding the result recovers the original `Data`. -/
public lemma StrEnc.toData_fromData {α : Type*} [StrEnc α] (d : Data) (x : α)
    (h : StrEnc.fromData d = some x) : StrEnc.toData x = d :=
  StrEnc.fromData_eq_some_iff.mp h

@[simp]
public lemma StrEnc.fromData_toData_apply (α : Type*) [StrEnc α] (x : α) :
    StrEnc.fromData (StrEnc.toData x) = some x :=
  StrEnc.fromData_toData x

/-- Smart constructor for `StrEnc` from the two directions of the inverse relation. -/
@[reducible, expose]
public def StrEnc.mk' {α : Type*} (toData : α → Data) (fromData : Data → Option α)
    (fromData_toData : ∀ x : α, fromData (toData x) = some x)
    (toData_fromData : ∀ d x, fromData d = some x → toData x = d) : StrEnc α where
  toData := toData
  fromData := fromData
  fromData_eq_some_iff := fun {d x} =>
    ⟨toData_fromData d x, fun h => h ▸ fromData_toData x⟩

/-- Encoding of a value of type `α` via its `Data` representation. -/
public abbrev StrEnc.enc {α : Type*} [StrEnc α] (w : α) : List Char :=
  Data.enc (StrEnc.toData w)

/-- `toData` is injective, since `fromData` is a left inverse. -/
public lemma StrEnc.toData_injective (α : Type*) [StrEnc α] :
    Function.Injective (StrEnc.toData (α := α)) := fun a b h =>
  Option.some_injective _ (by rw [← StrEnc.fromData_toData a, h, StrEnc.fromData_toData])

@[expose, grind =]
public def StrEnc.atPath? {α β : Type*} [StrEnc α] [StrEnc β]
    (x : α) (path : List ℕ) : Option β :=
  ((StrEnc.toData x).atPath path).bind StrEnc.fromData

@[simp]
public lemma StrEnc.atPath?_nil {α : Type*} [StrEnc α] (x : α) :
    StrEnc.atPath? x [] = some x := by
  simp [StrEnc.atPath?]

public instance : StrEnc Data where
  toData := id
  fromData := some
  fromData_eq_some_iff := ⟨fun h => (Option.some_injective _ h).symm, fun h => h ▸ rfl⟩

public instance : StrEnc Bool := StrEnc.mk'
  (fun
      -- ((()))
    | false => .list [.list [.list []]]
      -- (()())
    | true => .list [.list [], .list []])
  (fun
    | .list [.list [.list []]] => some false
    | .list [.list [], .list []] => some true
    | _ => none)
  (fun | false => rfl | true => rfl)
  (fun _ _ _ => by grind)

@[simp]
public lemma Bool.toData (d : Bool) :
  StrEnc.toData d = match d with
    | false => .list [.list [.list []]]
    | true => .list [.list [], .list []] := by rfl

public instance (α : Type*) [StrEnc α] : StrEnc (List α) := StrEnc.mk'
  (fun l => Data.list (l.map StrEnc.toData))
  (fun ⟨ds⟩ => ds.mapM StrEnc.fromData)
  (fun l => by
    induction l with
    | nil => rfl
    | cons a as ih => simp [List.mapM_cons, StrEnc.fromData_toData a, ih])
  (fun d xs h => by
    cases d with
    | list ds =>
      induction ds generalizing xs with
      | nil =>
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
        subst h
        rfl
      | cons d ds ih =>
        simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
        obtain ⟨a, ha, rest⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨as, has, hxs⟩ := Option.bind_eq_some_iff.mp rest
        simp only [Option.some.injEq] at hxs
        subst hxs
        simp only [List.map_cons, Data.list.injEq, List.cons.injEq]
        refine ⟨StrEnc.toData_fromData _ _ ha, ?_⟩
        have := ih as has
        simp only [Data.list.injEq] at this
        exact this)

public lemma List.toData {α : Type*} [StrEnc α] (l : List α) :
    StrEnc.toData l = Data.list (l.map StrEnc.toData) := by rfl

@[simp]
public lemma StrEnc.list_atPath? {α : Type*} [StrEnc α] (x : List α) (i : ℕ) (h_lt : i < x.length) :
    StrEnc.atPath? x [i] = some x[i] := by
  simp [StrEnc.atPath?, toData, h_lt]

/-- Encode `Option α` using the empty list for `none` and a singleton list otherwise. -/
public instance (α : Type) [StrEnc α] : StrEnc (Option α) := StrEnc.mk'
  (fun o => StrEnc.toData o.toList)
  (fun
    | Data.list [x] => (StrEnc.fromData x).map some
    | Data.list [] => some none
    | _ => none)
  (fun o => by
    cases o with
    | none => simp [StrEnc.toData]
    | some _ => simp [StrEnc.toData])
  (fun d x h => by
    match d, h with
    | Data.list [], h =>
      simp only [Option.some.injEq] at h; subst h; rfl
    | Data.list [y], h =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, hxa⟩ := h
      subst hxa
      simp only [Option.toList, StrEnc.toData, List.map_cons, List.map_nil,
        Data.list.injEq, List.cons.injEq, and_true]
      exact StrEnc.toData_fromData _ _ ha)

/-- Encode `ℕ` in dyadic, using `true` for `2` and `false` for `1`. -/
public instance : StrEnc ℕ := StrEnc.mk'
  (fun n => StrEnc.toData ((dyadic n).map (·  == '2')))
  (fun d => do
    let bits : List Bool ← StrEnc.fromData d
    dyadic_inv (bits.map (if · then '2' else '1')))
  (fun n => by
    simp only [StrEnc.fromData_toData]
    have hroundtrip : ∀ l : List Char, (∀ c ∈ l, c = '1' ∨ c = '2') →
        (l.map (· == '2')).map (if · then '2' else '1') = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons c cs ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨by rcases hl c (.head _) with rfl | rfl <;> decide,
               ih (fun c hc => hl c (.tail _ hc))⟩
    simp [hroundtrip _ (fun c hc => dyadic_mem_chars hc), dyadic_inv_dyadic])
  (fun d n h => by
    simp only [bind_pure_comp, Option.bind_eq_bind] at h
    obtain ⟨bits, hbits, hdyadic⟩ := Option.bind_eq_some_iff.mp h
    have h_d : StrEnc.toData bits = d := StrEnc.toData_fromData _ _ hbits
    have h_chars : ∀ c ∈ bits.map (if · then '2' else '1'), c = '1' ∨ c = '2' := by
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨b, _, rfl⟩ := hc
      cases b <;> simp
    have h_dy : dyadic n = bits.map (if · then '2' else '1') :=
      dyadic_dyadic_inv _ _ h_chars hdyadic
    show StrEnc.toData ((dyadic n).map (· == '2')) = d
    rw [h_dy, ← h_d]
    congr 1
    rw [List.map_map]
    conv_rhs => rw [← List.map_id bits]
    apply List.map_congr_left
    intro b _; cases b <;> simp)

@[simp]
public lemma Nat.toData_zero :
  StrEnc.toData 0 = Data.list [] := by simp [StrEnc.toData, dyadic]

@[simp]
public lemma Nat.toData_one :
  StrEnc.toData 1 = StrEnc.toData [false] := by simp [StrEnc.toData, dyadic]

@[simp]
public lemma Nat.toData_two :
  StrEnc.toData 2 = StrEnc.toData [true] := by simp [StrEnc.toData, dyadic]

@[simp]
public lemma Nat.toData_three :
  StrEnc.toData 3 = StrEnc.toData [false, false] := by simp [StrEnc.toData, dyadic]; grind

@[simp]
public lemma Nat.fromData_zero :
  StrEnc.fromData (Data.list []) = some 0 := by simp [StrEnc.fromData, dyadic_inv]

@[simp]
public lemma Nat.fromData_one :
  StrEnc.fromData (StrEnc.toData [false]) = some 1 := by simp [StrEnc.fromData, dyadic_inv]

@[simp]
public lemma Nat.fromData_two :
  StrEnc.fromData (StrEnc.toData [true]) = some 2 := by simp [StrEnc.fromData, dyadic_inv]

@[simp]
public lemma Nat.fromData_three :
  StrEnc.fromData (StrEnc.toData [false, false]) = some 3 := by
  simp [StrEnc.fromData, dyadic_inv]

/-- Encode `Char` through `ℕ` -/
public instance : StrEnc Char := StrEnc.mk'
  (fun o => StrEnc.toData o.toNat)
  (fun d => do
    let n ← StrEnc.fromData (α := ℕ) d
    if h : n.isValidChar then some (Char.ofNatAux n h) else none)
  (fun c => by
    show (StrEnc.fromData (α := ℕ) (StrEnc.toData c.toNat)) >>=
        (fun n => if h : n.isValidChar then some (Char.ofNatAux n h) else none) = some c
    rw [StrEnc.fromData_toData]
    show (if h : c.toNat.isValidChar then some (Char.ofNatAux c.toNat h) else none) = some c
    have hv : c.toNat.isValidChar := c.valid
    rw [dif_pos hv]
    show some ⟨c.val, _⟩ = some c
    cases c; rfl)
  (fun d c h => by
    have h' : (StrEnc.fromData (α := ℕ) d) >>=
        (fun n => if h : n.isValidChar then some (Char.ofNatAux n h) else none) = some c := h
    obtain ⟨n, hn, hc⟩ := Option.bind_eq_some_iff.mp h'
    by_cases hvalid : n.isValidChar
    · rw [dif_pos hvalid] at hc
      have hc' : Char.ofNatAux n hvalid = c := Option.some_injective _ hc
      have hnat : (Char.ofNatAux n hvalid).toNat = n := by
        rw [Char.toNat]; rfl
      show StrEnc.toData c.toNat = d
      rw [← hc', hnat]
      exact StrEnc.toData_fromData _ _ hn
    · rw [dif_neg hvalid] at hc
      cases hc)

/-- Encode `Fin k` through `ℕ`.
TODO: We might want to use padded encoding if `k` is a power of two. -/
public instance (k : ℕ) : StrEnc (Fin k) := StrEnc.mk'
  (fun i => StrEnc.toData i.val)
  (fun d => do
    let n ← StrEnc.fromData (α := ℕ) d
    if h : n < k then some ⟨n, h⟩ else none)
  (fun i => by simp [i.isLt])
  (fun d i h => by
    have h' : (StrEnc.fromData (α := ℕ) d) >>=
        (fun n => if h : n < k then some (⟨n, h⟩ : Fin k) else none) = some i := h
    obtain ⟨n, hn, hi⟩ := Option.bind_eq_some_iff.mp h'
    by_cases hlt : n < k
    · rw [dif_pos hlt] at hi
      have : (⟨n, hlt⟩ : Fin k) = i := Option.some_injective _ hi
      show StrEnc.toData i.val = d
      rw [← this]
      exact StrEnc.toData_fromData _ _ hn
    · rw [dif_neg hlt] at hi; cases hi)

public instance (k : ℕ) (α : Type*) [StrEnc α] : StrEnc (Fin k → α) := StrEnc.mk'
  (fun f => StrEnc.toData (List.ofFn f))
  (fun d => do
    let l ← StrEnc.fromData (α := List α) d
    if h : l.length = k then
      some (fun i => l[i.val]'(h ▸ i.isLt))
    else
      none)
  (fun f => by
    simp only [StrEnc.fromData_toData_apply]
    ext i
    simp [List.getElem_ofFn])
  (fun d f h => by
    have h' : (StrEnc.fromData (α := List α) d) >>=
        (fun l => if h : l.length = k then
          some (fun i : Fin k => l[i.val]'(h ▸ i.isLt)) else none) = some f := h
    obtain ⟨l, hl, hf⟩ := Option.bind_eq_some_iff.mp h'
    by_cases hlen : l.length = k
    · rw [dif_pos hlen] at hf
      have hf' : (fun i : Fin k => l[i.val]'(hlen ▸ i.isLt)) = f :=
        Option.some_injective _ hf
      show StrEnc.toData (List.ofFn f) = d
      have : List.ofFn f = l := by
        rw [← hf']
        apply List.ext_getElem
        · simp [hlen]
        · intro n h1 h2
          simp [List.getElem_ofFn]
      rw [this]
      exact StrEnc.toData_fromData _ _ hl
    · rw [dif_neg hlen] at hf; cases hf)

public instance (α β : Type*) [StrEnc α] [StrEnc β] : StrEnc (α × β) := StrEnc.mk'
  (fun p => Data.list [StrEnc.toData p.1, StrEnc.toData p.2])
  (fun
    | Data.list [a, b] =>
      match StrEnc.fromData a, StrEnc.fromData b with
      | some a', some b' => some (a', b')
      | _, _ => none
    | _ => none)
  (fun p => by simp)
  (fun d p h => by
    rcases d with ⟨xs⟩
    rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · change none = some p at h; cases h
    · change none = some p at h; cases h
    pick_goal 2
    · change none = some p at h; cases h
    show Data.list [StrEnc.toData p.1, StrEnc.toData p.2] = Data.list [a, b]
    have h' : (match StrEnc.fromData a, StrEnc.fromData b with
      | some a', some b' => some (a', b')
      | _, _ => none) = some p := h
    rcases ha : StrEnc.fromData (α := α) a with _ | a' <;> rw [ha] at h'
    · cases h'
    rcases hb : StrEnc.fromData (α := β) b with _ | b' <;> rw [hb] at h'
    · cases h'
    cases h'
    rw [StrEnc.toData_fromData _ _ ha, StrEnc.toData_fromData _ _ hb])

@[simp]
public lemma StrEnc.tuple_atPath?_zero {α β : Type*} [StrEnc α] [StrEnc β] (x : α × β) :
    StrEnc.atPath? x [0] = some x.fst := by
  show ((Data.list [StrEnc.toData x.fst, StrEnc.toData x.snd]).atPath [0]).bind
    StrEnc.fromData = some x.fst
  simp

@[simp]
public lemma StrEnc.tuple_atPath?_one {α β : Type*} [StrEnc α] [StrEnc β] (x : α × β) :
    StrEnc.atPath? x [1] = some x.snd := by
  show ((Data.list [StrEnc.toData x.fst, StrEnc.toData x.snd]).atPath [1]).bind
    StrEnc.fromData = some x.snd
  simp


/-- `StrEnc` for functions `α → β` where `α` is finite, encoded as the function's
    graph: a list of `(a, f a)` pairs.
    Not registered as an instance to avoid overlap with `Fin k → α`.
    Activate with `letI := StrEnc.ofFunction α β`. -/
@[reducible]
public noncomputable def StrEnc.ofFunction (α : Type) (β : Type*)
    [Fintype α] [DecidableEq α] [StrEnc α] [StrEnc β] : StrEnc (α → β) := StrEnc.mk'
  (fun f => StrEnc.toData (Finset.univ.val.toList.map fun a => (a, f a)))
  (fun d =>
    match StrEnc.fromData (α := List (α × β)) d with
    | none => none
    | some pairs =>
      let f := fun a => pairs.lookup a
      if h : ∀ a, (f a).isSome then
        let g := fun a => (f a).get (h a)
        haveI := Classical.propDecidable
          (Finset.univ.val.toList.map (fun a => (a, g a)) = pairs)
        if Finset.univ.val.toList.map (fun a => (a, g a)) = pairs then some g else none
      else
        none)
  (fun f => by
    simp only [StrEnc.fromData_toData_apply]
    have h_mem : ∀ a : α, a ∈ Finset.univ.val.toList := fun a =>
      Multiset.mem_toList.mpr (Finset.mem_univ a)
    have h_lookup : ∀ a, (Finset.univ.val.toList.map (fun a => (a, f a))).lookup a
        = some (f a) :=
      fun a => List.lookup_graph f (h_mem a)
    have h_forall : ∀ a,
        ((Finset.univ.val.toList.map (fun a => (a, f a))).lookup a).isSome := by
      intro a; simp [h_lookup a]
    rw [dif_pos h_forall]
    have hg : (fun a => ((Finset.univ.val.toList.map (fun a => (a, f a))).lookup a).get
        (h_forall a)) = f := by
      ext a; have := h_lookup a; simp_all
    have hcond : Finset.univ.val.toList.map
        (fun a => (a, ((Finset.univ.val.toList.map (fun a => (a, f a))).lookup a).get
          (h_forall a))) = Finset.univ.val.toList.map (fun a => (a, f a)) := by
      apply List.map_congr_left
      intro a _; rw [show (((Finset.univ.val.toList.map (fun a => (a, f a))).lookup a).get
          (h_forall a)) = f a from congrFun hg a]
    rw [if_pos hcond]
    rw [hg])
  (fun d g h => by
    dsimp only at h
    rcases hpairs : StrEnc.fromData (α := List (α × β)) d with _ | pairs
    · rw [hpairs] at h
      change none = some g at h
      cases h
    rw [hpairs] at h
    change (let f := fun a => pairs.lookup a
      if hsome : ∀ a, (f a).isSome then
        let g' := fun a => (f a).get (hsome a)
        haveI := Classical.propDecidable
          (Finset.univ.val.toList.map (fun a => (a, g' a)) = pairs)
        if Finset.univ.val.toList.map (fun a => (a, g' a)) = pairs then some g' else none
      else none) = some g at h
    simp only at h
    by_cases hsome : ∀ a, (pairs.lookup a).isSome
    · rw [dif_pos hsome] at h
      by_cases heq : Finset.univ.val.toList.map
          (fun a => (a, (pairs.lookup a).get (hsome a))) = pairs
      · rw [if_pos heq] at h
        cases h
        show StrEnc.toData (Finset.univ.val.toList.map
            (fun a => (a, (pairs.lookup a).get (hsome a)))) = d
        rw [heq]
        exact StrEnc.toData_fromData _ _ hpairs
      · rw [if_neg heq] at h; cases h
    · rw [dif_neg hsome] at h; cases h)

/-- `StrEnc` instance for any `Encodable` type via its encoding to `ℕ`.
    Not registered as an instance to avoid overlap with specific encodings
    (e.g., `Bool`). Use `attribute [local instance] StrEnc.ofEncodable` or
    `letI := StrEnc.ofEncodable α` to activate. -/
@[reducible]
public def StrEnc.ofEncodable (α : Type) [Encodable α] : StrEnc α := StrEnc.mk'
  (fun a => StrEnc.toData (Encodable.encode a))
  (fun d => do
    let n ← StrEnc.fromData (α := ℕ) d
    let a ← Encodable.decode n
    if Encodable.encode a = n then some a else none)
  (fun a => by
    show (StrEnc.fromData (α := ℕ) (StrEnc.toData (Encodable.encode a))) >>=
        (fun n => (Encodable.decode (α := α) n) >>=
          fun a' => if Encodable.encode a' = n then some a' else none) = some a
    rw [StrEnc.fromData_toData]
    show ((Encodable.decode (Encodable.encode a)) >>=
      fun a' => if Encodable.encode a' = Encodable.encode a then some a' else none) = some a
    rw [Encodable.encodek]
    show (if Encodable.encode a = Encodable.encode a then some a else none) = some a
    rw [if_pos rfl])
  (fun d a h => by
    have h' : (StrEnc.fromData (α := ℕ) d) >>=
        (fun n => (Encodable.decode (α := α) n) >>=
          fun a' => if Encodable.encode a' = n then some a' else none) = some a := h
    obtain ⟨n, hn, h2⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨a', ha', h3⟩ := Option.bind_eq_some_iff.mp h2
    by_cases heq : Encodable.encode a' = n
    · rw [if_pos heq] at h3
      cases h3
      show StrEnc.toData (Encodable.encode a) = d
      rw [heq]
      exact StrEnc.toData_fromData _ _ hn
    · rw [if_neg heq] at h3; cases h3)

end Turing
