/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Fold
public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.BoundsTactic

/-!
# Checking a CNF assignment is polynomial time

The standard verifier for `SAT ∈ NP`: given an assignment and a formula in conjunctive normal
form, decide whether the assignment satisfies it.

It is two nested folds. The outer one walks the clauses conjunctively; the inner one walks a
clause's literals disjunctively. Both carry the **assignment inside the accumulator**, because a
`foldl` step in this framework deliberately never sees the original input — the design decision
made when `foldl_computableUpTo` was stated. That is what keeps the accumulator bound linear:
the assignment is a component of the input, so carrying it costs `n + O(1)`, not more.

Variable lookup is `asg[i]?`, which is the fold already worked out in `Examples/ListIndex.lean`.
-/

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

namespace Cnf

/-- A variable, named by a unary index. Unary rather than binary so that looking a variable up in
the assignment is a fold over *existing* primitives (drop one cell per tick) rather than needing
`ℕ` arithmetic, for which this framework has no certificate. Unary and binary indices are
polynomially related, so the polynomial-time claim is unaffected. -/
abbrev Var := List Unit

/-- A literal: a variable together with the polarity that satisfies it. -/
abbrev Lit := Var × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A formula in conjunctive normal form. -/
abbrev Formula := List Clause

/-- An assignment; variables past the end read as `false`. -/
abbrev Assignment := List Bool

/-! ### Variable lookup, as a fold

Ticking one cell off the assignment per unit of the index. The step is `fun acc _ => acc.tail`,
whose certificate is `Bounds.comp Bounds.tail Bounds.fst` — primitives only. -/

/-- The unary index to walk. -/
def varList (p : Assignment × Var) : Var := p.2

/-- Start from the whole assignment. -/
def varInit (p : Assignment × Var) : Assignment := p.1

/-- Drop one cell per unit of the index. -/
def varStep (acc : Assignment) (_ : Unit) : Assignment := acc.tail

/-- The value of a variable under an assignment; variables past the end read as `false`. -/
def varVal (p : Assignment × Var) : Bool :=
  (foldFun varList varInit varStep p).head?.getD false

/-- **The lookup fold drops one cell per tick.** -/
lemma foldFun_var (p : Assignment × Var) :
    foldFun varList varInit varStep p = List.tail^[p.2.length] p.1 :=
  foldl_const_iterate _ _ _

lemma foldAcc_var (p : Assignment × Var) (j : ℕ) :
    foldAcc varList varInit varStep p j = List.tail^[(p.2.take j).length] p.1 :=
  foldl_const_iterate _ _ _

/-- Dropping cells never grows the encoding. -/
lemma size_tail_iterate_le (asg : Assignment) (k : ℕ) :
    (DataEncode.encode (List.tail^[k] asg)).size ≤ (DataEncode.encode asg).size := by
  induction k generalizing asg with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact le_trans (ih _) (DataEncode.size_tail_le asg)

/-- **The lookup accumulator is a suffix of the assignment**, hence never bigger than the input. -/
lemma varAccSize (p : Assignment × Var) (j : ℕ) :
    (DataEncode.encode (foldAcc varList varInit varStep p j)).size
      ≤ (DataEncode.encode p).size := by
  obtain ⟨asg, i⟩ := p
  rw [foldAcc_var]
  simp only []
  have h1 := size_tail_iterate_le asg ((i.take j).length)
  have h2 : (DataEncode.encode ((asg, i) : Assignment × Var)).size
      = (DataEncode.encode asg).size + (DataEncode.encode i).size + 2 :=
    DataEncode.size_pair _ _
  omega

/-- A certificate for the lookup fold. The accumulator bound is the human's contribution; the
three ingredient certificates are primitives. -/
def varFoldBounds : Bounds (foldFun varList varInit varStep) :=
  Bounds.fold (list := varList) (init := varInit) (step := varStep)
    Bounds.snd Bounds.fst (Bounds.comp Bounds.tail Bounds.fst)
    (fun n => n) monotone_id varAccSize

/-- A certificate for variable lookup. -/
def varValBounds : Bounds varVal :=
  Bounds.comp (Bounds.headD false) varFoldBounds

attribute [bounds] varValBounds

/-- Is a literal satisfied by an assignment? -/
def litSat (asg : Assignment) (l : Lit) : Bool := varVal (asg, l.1) == l.2

/-- Is a clause satisfied? -/
def clauseSat (asg : Assignment) (c : Clause) : Bool := c.any (litSat asg)

/-- Is a formula satisfied? -/
def formulaSat (p : Assignment × Formula) : Bool := p.2.all (clauseSat p.1)

/-! ### Boolean connectives

Functions between finite types, so `Bounds.ofFintype` covers them. Registering them lets the
tactic resolve `||`, `&&` and `==` wherever they appear. -/

/-- Every `Bool × Bool` encodes in at most ten cells, so `ofFintype`'s time constant for a
Boolean connective is at most fourteen. -/
lemma sup_pair_le (f : Bool × Bool → Bool) :
    (Finset.univ.sup fun a : Bool × Bool =>
      (DataEncode.encode a).size + (DataEncode.encode (f a)).size) ≤ 14 := by
  refine Finset.sup_le fun a _ => ?_
  obtain ⟨x, y⟩ := a
  have h1 := DataEncode.size_bool x
  have h2 := DataEncode.size_bool y
  have h3 := DataEncode.size_bool (f (x, y))
  rw [DataEncode.size_pair]
  omega

/-- …and its output constant at most four. -/
lemma sup_out_le (f : Bool × Bool → Bool) :
    (Finset.univ.sup fun a : Bool × Bool => (DataEncode.encode (f a)).size) ≤ 4 :=
  Finset.sup_le fun _ _ => DataEncode.size_bool _

/-- Disjunction. -/
def orBounds : Bounds (Function.uncurry (· || · : Bool → Bool → Bool)) := Bounds.ofFintype _

/-- Conjunction. -/
def andBounds : Bounds (Function.uncurry (· && · : Bool → Bool → Bool)) := Bounds.ofFintype _

/-- Boolean equality. -/
def beqBounds : Bounds (Function.uncurry (· == · : Bool → Bool → Bool)) := Bounds.ofFintype _

attribute [bounds] orBounds andBounds beqBounds

/-- `n ↦ c * (n + 1) ^ k` is monotone; the closed forms below are all of this shape. -/
lemma mono_poly (c k : ℕ) : Monotone (fun n => c * (n + 1) ^ k) :=
  fun _ _ h => Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) _)

/-- The linear case, stated without the exponent. -/
lemma mono_lin (c : ℕ) : Monotone (fun n => c * (n + 1)) :=
  fun _ _ h => Nat.mul_le_mul le_rfl (by omega)

/-- **A certificate for literal evaluation, synthesised.** -/
def litSatBounds₀ : Bounds (Function.uncurry litSat) := by bounds

/-- The same certificate, weakened to a closed form.

Every combinator glues its operands' bound *expressions* together, so a certificate built by
four nested composites carries a bound tree that is exponentially large in the nesting depth even
though the function it bounds is small. Weakening to a closed form at each stage keeps the tree
flat, which is what makes the final read-off in `formulaSat_polyTimeLinSpace` tractable. -/
def litSatBounds : Bounds (Function.uncurry litSat) :=
  litSatBounds₀.weaken (fun n => 100 * (n + 1) ^ 2) (fun n => 200 * (n + 1)) (fun _ => 4)
    (mono_poly 100 2) (mono_lin 200) monotone_const
    (fun n => by
      have b3 := sup_pair_le (Function.uncurry (· == · : Bool → Bool → Bool))
      have u := DataEncode.size_bool false
      have hexp : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
      rw [hexp]
      simp only [boundsDefs, litSatBounds₀, varValBounds, varFoldBounds,
        beqBounds, Bounds.ofFintype, Bounds.fold]
      nlinarith [b3, u, Nat.zero_le n, Nat.mul_le_mul u (le_refl n)])
    (fun n => by
      have b3 := sup_pair_le (Function.uncurry (· == · : Bool → Bool → Bool))
      have c3 := sup_out_le (Function.uncurry (· == · : Bool → Bool → Bool))
      have t := DataEncode.size_bool true
      have u := DataEncode.size_bool false
      simp only [boundsDefs, litSatBounds₀, varValBounds, varFoldBounds,
        beqBounds, Bounds.ofFintype, Bounds.fold]
      omega)
    (fun n => by
      have c3 := sup_out_le (Function.uncurry (· == · : Bool → Bool → Bool))
      simp only [boundsDefs, litSatBounds₀, varValBounds, varFoldBounds,
        beqBounds, Bounds.ofFintype, Bounds.fold]
      omega)

attribute [bounds] litSatBounds

/-! ### The inner fold: one clause -/

/-- The literals of the clause. -/
def clauseList (p : Assignment × Clause) : Clause := p.2

/-- Carry the assignment; nothing satisfied yet. -/
def clauseInit (p : Assignment × Clause) : Assignment × Bool := (p.1, false)

/-- Disjoin the next literal's value. -/
def clauseStep (acc : Assignment × Bool) (l : Lit) : Assignment × Bool :=
  (acc.1, acc.2 || litSat acc.1 l)

lemma foldl_clauseStep (c : Clause) (asg : Assignment) (b : Bool) :
    (c.foldl clauseStep (asg, b)).2 = (b || clauseSat asg c) := by
  induction c generalizing b with
  | nil => simp [clauseSat]
  | cons l c ih => simp [clauseStep, ih, clauseSat, Bool.or_assoc]

lemma foldl_clauseStep_fst (c : Clause) (asg : Assignment) (b : Bool) :
    (c.foldl clauseStep (asg, b)).1 = asg := by
  induction c generalizing b with
  | nil => rfl
  | cons l c ih => simpa [clauseStep] using ih (b || litSat asg l)

/-- **The inner fold decides one clause.** -/
lemma foldFun_clause (p : Assignment × Clause) :
    (foldFun clauseList clauseInit clauseStep p).2 = clauseSat p.1 p.2 := by
  obtain ⟨asg, c⟩ := p
  change (c.foldl clauseStep (asg, false)).2 = _
  rw [foldl_clauseStep]
  simp

/-! ### The outer fold: the whole formula -/

/-- The clauses of the formula. -/
def formulaList (p : Assignment × Formula) : Formula := p.2

/-- Carry the assignment; satisfied so far. -/
def formulaInit (p : Assignment × Formula) : Assignment × Bool := (p.1, true)

/-- Conjoin the next clause's value. -/
def formulaStep (acc : Assignment × Bool) (c : Clause) : Assignment × Bool :=
  (acc.1, acc.2 && clauseSat acc.1 c)

lemma foldl_formulaStep (f : Formula) (asg : Assignment) (b : Bool) :
    (f.foldl formulaStep (asg, b)).2 = (b && f.all (clauseSat asg)) := by
  induction f generalizing b with
  | nil => simp
  | cons c f ih => simp [formulaStep, ih, Bool.and_assoc]

lemma foldl_formulaStep_fst (f : Formula) (asg : Assignment) (b : Bool) :
    (f.foldl formulaStep (asg, b)).1 = asg := by
  induction f generalizing b with
  | nil => rfl
  | cons c f ih => simpa [formulaStep] using ih (b && clauseSat asg c)

/-- **The outer fold decides the formula.** -/
lemma foldFun_formula (p : Assignment × Formula) :
    (foldFun formulaList formulaInit formulaStep p).2 = formulaSat p := by
  obtain ⟨asg, f⟩ := p
  change (f.foldl formulaStep (asg, true)).2 = _
  rw [foldl_formulaStep]
  simp [formulaSat]

/-! ### Size bookkeeping

Both accumulators have the same shape — the assignment, carried unchanged, plus one `Bool` — so
both bounds are `n + 6`: linear, because the assignment is a *component of the input*. -/

/-- **The inner accumulator stays linear**: the assignment is carried unchanged. -/
lemma clauseAccSize (p : Assignment × Clause) (j : ℕ) :
    (DataEncode.encode (foldAcc clauseList clauseInit clauseStep p j)).size
      ≤ (DataEncode.encode p).size + 6 := by
  obtain ⟨asg, c⟩ := p
  have hacc : foldAcc clauseList clauseInit clauseStep (asg, c) j
      = ((c.take j).foldl clauseStep (asg, false)) := rfl
  have hfst := foldl_clauseStep_fst (c.take j) asg false
  have hsplit : (DataEncode.encode ((c.take j).foldl clauseStep (asg, false))).size
      = (DataEncode.encode ((c.take j).foldl clauseStep (asg, false)).1).size
        + (DataEncode.encode ((c.take j).foldl clauseStep (asg, false)).2).size + 2 :=
    DataEncode.size_pair _ _
  have hb := DataEncode.size_bool ((c.take j).foldl clauseStep (asg, false)).2
  rw [hacc, hsplit, hfst, DataEncode.size_pair]
  omega

/-- **The outer accumulator stays linear**, for the same reason. -/
lemma formulaAccSize (p : Assignment × Formula) (j : ℕ) :
    (DataEncode.encode (foldAcc formulaList formulaInit formulaStep p j)).size
      ≤ (DataEncode.encode p).size + 6 := by
  obtain ⟨asg, f⟩ := p
  have hacc : foldAcc formulaList formulaInit formulaStep (asg, f) j
      = ((f.take j).foldl formulaStep (asg, true)) := rfl
  have hfst := foldl_formulaStep_fst (f.take j) asg true
  have hsplit : (DataEncode.encode ((f.take j).foldl formulaStep (asg, true))).size
      = (DataEncode.encode ((f.take j).foldl formulaStep (asg, true)).1).size
        + (DataEncode.encode ((f.take j).foldl formulaStep (asg, true)).2).size + 2 :=
    DataEncode.size_pair _ _
  have hb := DataEncode.size_bool ((f.take j).foldl formulaStep (asg, true)).2
  rw [hacc, hsplit, hfst, DataEncode.size_pair]
  omega

/-- Deciding one clause, as a function of the pair. -/
def clauseSatP (p : Assignment × Clause) : Bool := clauseSat p.1 p.2

/-! ### Certificates, bottom up

Each *step* is synthesised by the tactic; each *fold* needs its accumulator bound supplied by
hand, and is then registered so the next level up can be synthesised in turn. -/

/-- Synthesised. -/
def clauseStepBounds : Bounds (Function.uncurry clauseStep) := by bounds

/-- Synthesised. -/
def clauseListBounds : Bounds clauseList := by bounds

/-- Synthesised. -/
def clauseInitBounds : Bounds clauseInit := by bounds

/-- The inner fold; the accumulator bound is the human's contribution. -/
def clauseFoldBounds : Bounds (foldFun clauseList clauseInit clauseStep) :=
  Bounds.fold (list := clauseList) (init := clauseInit) (step := clauseStep)
    clauseListBounds clauseInitBounds clauseStepBounds
    (fun n => n + 6) (fun _ _ h => Nat.add_le_add_right h 6) clauseAccSize

/-- **Deciding one clause.** -/
def clauseSatBounds₀ : Bounds clauseSatP :=
  (Bounds.comp (Bounds.snd : Bounds (Prod.snd : Assignment × Bool → Bool))
    clauseFoldBounds).congr (funext foldFun_clause)

/-- Weakened to a closed form, as for `litSatBounds`. One clause costs a cubic: the fold runs the
quadratic `litSatBounds` once per literal. -/
def clauseSatBounds : Bounds clauseSatP :=
  clauseSatBounds₀.weaken (fun n => 100000 * (n + 1) ^ 3) (fun n => 20000 * (n + 1))
    (fun n => 20 * (n + 1)) (mono_poly 100000 3) (mono_lin 20000) (mono_lin 20)
    (fun n => by
      have b1 := sup_pair_le (Function.uncurry (· || · : Bool → Bool → Bool))
      have c1 := sup_out_le (Function.uncurry (· || · : Bool → Bool → Bool))
      have t := DataEncode.size_bool true
      have u := DataEncode.size_bool false
      have hexp : (n + 1) ^ 3 = n * n * n + 3 * (n * n) + 3 * n + 1 := by ring
      rw [hexp]
      simp only [boundsDefs, clauseSatBounds₀, clauseFoldBounds, clauseStepBounds,
        clauseListBounds, clauseInitBounds, litSatBounds, orBounds, Bounds.ofFintype, Bounds.fold]
      nlinarith [b1, c1, t, u, Nat.zero_le n, sq_nonneg n,
        Nat.mul_le_mul u (le_refl n), Nat.mul_le_mul b1 (le_refl n), Nat.mul_le_mul c1 (le_refl n),
        Nat.mul_le_mul (Nat.mul_le_mul u (le_refl n)) (le_refl n)])
    (fun n => by
      have b1 := sup_pair_le (Function.uncurry (· || · : Bool → Bool → Bool))
      have c1 := sup_out_le (Function.uncurry (· || · : Bool → Bool → Bool))
      have t := DataEncode.size_bool true
      have u := DataEncode.size_bool false
      simp only [boundsDefs, clauseSatBounds₀, clauseFoldBounds, clauseStepBounds,
        clauseListBounds, clauseInitBounds, litSatBounds, orBounds, Bounds.ofFintype, Bounds.fold]
      omega)
    (fun n => by
      have c1 := sup_out_le (Function.uncurry (· || · : Bool → Bool → Bool))
      simp only [boundsDefs, clauseSatBounds₀, clauseFoldBounds, clauseStepBounds,
        clauseListBounds, clauseInitBounds, litSatBounds, orBounds, Bounds.ofFintype, Bounds.fold]
      omega)

attribute [bounds] clauseSatBounds

/-- Synthesised, now that `clauseSatBounds` is a leaf. -/
def formulaStepBounds : Bounds (Function.uncurry formulaStep) := by bounds

/-- Synthesised. -/
def formulaListBounds : Bounds formulaList := by bounds

/-- Synthesised. -/
def formulaInitBounds : Bounds formulaInit := by bounds

/-- The outer fold. -/
def formulaFoldBounds : Bounds (foldFun formulaList formulaInit formulaStep) :=
  Bounds.fold (list := formulaList) (init := formulaInit) (step := formulaStep)
    formulaListBounds formulaInitBounds formulaStepBounds
    (fun n => n + 6) (fun _ _ h => Nat.add_le_add_right h 6) formulaAccSize

/-- **Verifying a CNF assignment — a certificate, with no hypotheses at all.**

Everything it rests on is the framework's assumed primitives; nothing specific to CNF is assumed.
Read the concrete time and space bounds off with `simp [boundsDefs]`. -/
def formulaSatBounds : Bounds formulaSat :=
  (Bounds.comp (Bounds.snd : Bounds (Prod.snd : Assignment × Bool → Bool))
    formulaFoldBounds).congr (funext foldFun_formula)

/-! ### The complexity statements -/

/-- **Verifying a CNF assignment is polynomial time and linear space.**

This is the `SAT ∈ NP` verifier, read off from `formulaSatBounds` with no hypotheses at all: the
certificate chain rests only on the framework's assumed primitives.

The exponent is `4`, and the nesting explains it. The outer fold visits each clause; the inner
fold visits each literal of that clause; evaluating one literal walks the assignment to find the
variable. That is three nested linear scans, and the fold combinator charges the per-step bound at
the *accumulator* size rather than the element size, which contributes the fourth factor. The
constants are deliberately loose — `PolyTimeLinSpace` quotients them away, so there is nothing to
gain by tightening them. -/
theorem formulaSat_polyTimeLinSpace : PolyTimeLinSpace formulaSat :=
  formulaSatBounds.polyTimeLinSpace 10000000000 4 500000
    (fun n => le_trans
      (by
        have b2 := sup_pair_le (Function.uncurry (· && · : Bool → Bool → Bool))
        have c2 := sup_out_le (Function.uncurry (· && · : Bool → Bool → Bool))
        have t := DataEncode.size_bool true
        have u := DataEncode.size_bool false
        have hexp : (n + 1) ^ 4 = n*n*n*n + 4*(n*n*n) + 6*(n*n) + 4*n + 1 := by ring
        rw [hexp]
        simp only [boundsDefs, formulaSatBounds, formulaFoldBounds, formulaStepBounds,
          formulaListBounds, formulaInitBounds, clauseSatBounds, andBounds, Bounds.ofFintype,
          Bounds.fold]
        nlinarith [b2, c2, t, u, Nat.zero_le n, sq_nonneg n,
          Nat.mul_le_mul t (le_refl n), Nat.mul_le_mul c2 (le_refl n),
          Nat.mul_le_mul b2 (le_refl n),
          Nat.mul_le_mul (Nat.mul_le_mul t (le_refl n)) (le_refl n),
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul t (le_refl n)) (le_refl n)) (le_refl n)] :
        formulaSatBounds.time n ≤ 10000000000 * (n + 1) ^ 4)
      (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) 4)))
    (fun n => by
      have b2 := sup_pair_le (Function.uncurry (· && · : Bool → Bool → Bool))
      have c2 := sup_out_le (Function.uncurry (· && · : Bool → Bool → Bool))
      have t := DataEncode.size_bool true
      have u := DataEncode.size_bool false
      simp only [boundsDefs, formulaSatBounds, formulaFoldBounds, formulaStepBounds,
        formulaListBounds, formulaInitBounds, clauseSatBounds, andBounds, Bounds.ofFintype,
        Bounds.fold]
      omega)

end Cnf

end MultiTapeTM

end Turing
