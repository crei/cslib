/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.PB
public import Cslib.Computability.Machines.RoseTreeMachine.V3.DataEncode

/-! # RoseTreeMachine V4 — Tools

Derived program-builder combinators. Because the V4 builder keeps the same HOAS `elim`
signature as the first-order development, these definitions are identical to their
counterparts there; only the underlying semantics (functional `elim`/`while_`) differs.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

/-- Returns the tail of a list-valued builder (`[]` when empty). -/
def PB.tail (x : PB) : PB := .elim x .empty (fun _hd tl => tl)

/-- Returns the head of a list-valued builder (`Data.l []` when empty). -/
def PB.head (x : PB) : PB := .elim x .empty (fun hd _tl => hd)

@[simp]
lemma PB.tail_computes {env : List Data} {x : PB} {dx : Data} (hx : PB.computes env x dx) :
    PB.computes env (.tail x) (Data.l dx.asList.tail) := by
  obtain ⟨dx⟩ := dx
  cases dx with
  | nil => simpa [PB.tail] using PB.elim_nil_computes hx PB.empty_computes
  | cons hd tl =>
    refine PB.elim_cons_computes hx ?_
    intro ext
    simpa [PB.computesFun₂, PB.var] using PB.var_computesFun (binds := [hd, Data.l tl]) (j := 1) ext

@[simp]
lemma PB.head_computes {env : List Data} {x : PB} {dx : Data} (hx : PB.computes env x dx) :
    PB.computes env (PB.head x) (dx.asList.headD (Data.l [])) := by
  obtain ⟨dx⟩ := dx
  cases dx with
  | nil => simpa [PB.head] using PB.elim_nil_computes hx PB.empty_computes
  | cons hd tl =>
    refine PB.elim_cons_computes hx ?_
    intro ext
    simpa [PB.computesFun₂, PB.var] using PB.var_computesFun (binds := [hd, Data.l tl]) (j := 0) ext

/-! ### Further derived combinators (definitions only)

These mirror the first-order development. `letIn`/`fold`/`ifEq` are *derived* in V4 from the
in-place `elim`/`while_` builders, so they stay inside the first-order fragment. -/

/-- First projection (`head`). -/
def PB.fst (x : PB) : PB := PB.head x

/-- Second projection (`head` of `tail`). -/
def PB.snd (x : PB) : PB := PB.head (PB.tail x)

/-- `Option.some` as a singleton list. -/
def PB.some (x : PB) : PB := PB.cons x PB.empty

/-- Eliminate an `Option`: on `none` (empty) run `noneCase`, on `some v` run `someCase v`. -/
def PB.optionElim (x noneCase : PB) (someCase : PB → PB) : PB :=
  PB.elim x noneCase (fun v _ => someCase v)

/-- Build the two-element list `[a, b]` (used as an encoded pair). -/
def PB.toPair (a b : PB) : PB := PB.cons a (PB.cons b PB.empty)

/-- A `let` binding `let x := val; body x`, encoded in the first-order fragment via `elim`:
`val` is wrapped into the singleton `[val]`, whose `cons` branch binds `x := val`. -/
def PB.letIn (val : PB) (body : PB → PB) : PB :=
  PB.elim (PB.cons val PB.empty) PB.empty (fun x _ => body x)

/-- Program that evaluates to the constant `a`. -/
def PB.constant (a : Data) : PB := match a with
  | Data.l [] => .empty
  | Data.l (x :: xs) => .cons (constant x) (constant (Data.l xs))

def PB.constantEnc {α : Type} [DataEncode α] (a : α) : PB := PB.constant (DataEncode.encode a)

/-- `fold body init list`: left fold of `body` (taking `acc` then `el`) over `list`.

Implemented with `while_` over a `[remaining, acc]` pair: the loop halts once `remaining`
(the *head* of the accumulator, which is what `while_` inspects) becomes empty; otherwise it
splits off the first element `el`, updates the accumulator to `[rest, body acc el]`, and
continues. The fold's result is the final `acc` (the second component). -/
def PB.fold (body : PB → PB → PB) (init list : PB) : PB :=
  PB.snd (PB.while_ (PB.toPair list init)
    (fun st => PB.elim (PB.fst st) PB.empty
      (fun el rest => PB.toPair rest (body (PB.snd st) el))))

/-- Structural equality of two rose trees, returning the `true` sentinel `[[]]` (nonempty) or
the `false` sentinel `[]` (empty).

Implemented with a `while_` over a worklist of pairs still to compare, threaded together with
a boolean result in a `[worklist, result]` accumulator. Each iteration pops a pair `[x, y]`
and compares one level: matching empties continue; matching conses push the head-pair and
tail-pair back onto the worklist; any mismatch empties the worklist (forcing the loop to halt)
and sets the result to `false`. The loop also halts naturally once the worklist is exhausted,
leaving the result `true`. -/
def PB.eq (a b : PB) : PB :=
  PB.snd (PB.while_
    (PB.toPair (PB.cons (PB.toPair a b) PB.empty) (PB.some PB.empty))
    (fun acc =>
      PB.elim (PB.fst acc) PB.empty (fun pair rest =>
        PB.elim (PB.fst pair)
          (PB.elim (PB.snd pair)
            (PB.toPair rest (PB.snd acc))
            (fun _ _ => PB.toPair PB.empty PB.empty))
          (fun xh xt =>
            PB.elim (PB.snd pair)
              (PB.toPair PB.empty PB.empty)
              (fun yh yt =>
                PB.toPair
                  (PB.cons (PB.toPair xh yh) (PB.cons (PB.toPair xt yt) rest))
                  (PB.snd acc))))))

/-- If `a` and `b` are structurally equal, run `then_`, otherwise `else_`. -/
def PB.ifEq (a b then_ else_ : PB) : PB :=
  PB.elim (PB.eq a b) else_ (fun _ _ => then_)

end V4

end RoseTreeMachine

end Turing
