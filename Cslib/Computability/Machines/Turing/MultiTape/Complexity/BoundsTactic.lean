/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public meta import Cslib.Computability.Machines.Turing.MultiTape.Complexity.BoundsAttr

/-!
# The `bounds` tactic

Discharges a goal `Bounds f`, for an ordinary Lean function `f`, by decomposing `f`'s term and
applying the `Bounds` combinators. This is what makes the framework usable on a large class of
Lean functions rather than only on functions whose certificates were assembled by hand.

Note the goal is *data*: `Bounds f` is a certificate, not a proposition, so the tactic produces a
term rather than a proof. That is deliberate — the coarse `Prop`-level views (`ComputableUpTo`,
`PolyTimeLinSpace`) are not compositional, because `ComputableUpTo.comp` and `Bounds.fold` need the
*output-size* bound of their arguments in order to state their own bounds. An existential wrapper
would hide exactly the data the next combinator must mention.

## What it handles

The argument, constants, `Prod.mk`, projections (both `Prod.fst`/`Prod.snd` applications and
`Expr.proj`, which is what `whnf` actually produces), `List.cons`,
`List.head?.getD`, `Option.getD`, `cond`, and two application shapes — `g x` and `g x y`
where `g` itself does not mention the argument, resolved through
registered leaves. Anything else is unfolded one step at a time, consulting the leaf table before
each step so a registered function is never unfolded past.

## What it does not handle, on purpose

Folds and loops. `Bounds.fold` and `Bounds.while` take the accumulator bound `A` and trip count
`N`, which a tactic cannot invent. Prove the certificate once and register it with `@[bounds]`;
the tactic then treats it as a leaf. Likewise `if`: a `Decidable` `ite` elaborates to
`Decidable.rec`, which has no certificate — write `cond` instead, which is the framework's own
discipline anyway.

## Reading the bounds back off

A synthesised certificate's fields reduce definitionally (`Bounds.congr` copies them verbatim), so
`simp [boundsDefs]` followed by `omega` / `nlinarith` will bound them. Beware that projections
synthesise as `Bounds.comp Bounds.fst Bounds.id`, so combinators you did not write appear in the
term; `boundsDefs` collects them all.
-/

open Lean Meta Elab Tactic

@[expose] public section

namespace Turing

namespace MultiTapeTM

open RoseTreeMachine

attribute [boundsDefs] Bounds.id Bounds.const Bounds.fst Bounds.snd Bounds.comp Bounds.pair
  Bounds.cons Bounds.ite Bounds.tail Bounds.headD Bounds.isEmpty Bounds.optionGetD
  Bounds.congr Bounds.comp' Bounds.pair'

/-- Try each registered certificate against `target`, synthesising its instance arguments. -/
meta def tryLeaf (target : Expr) : MetaM (Option Expr) := do
  for nm in boundsExt.getState (← getEnv) do
    let r ← observing? do
      let c ← mkConstWithFreshMVarLevels nm
      let (mvars, _, ty) ← forallMetaTelescope (← inferType c)
      guard (← isDefEq ty target)
      for m in mvars do
        let mty ← inferType m
        if (← isClass? mty).isSome then m.mvarId!.assign (← synthInstance mty)
      instantiateMVars (mkAppN c mvars)
    if let some e := r then
      unless e.hasExprMVar do return some e
  return none

/-- A registered certificate for `g` itself. -/
meta def leafFor (g : Expr) : MetaM (Option Expr) := do
  tryLeaf (← mkAppOptM ``Bounds #[none, none, none, none, some g])

/-- Synthesise a `Bounds` certificate for the Lean function `f`. -/
meta partial def synthBounds (fuel : Nat) (f : Expr) : MetaM Expr := do
  let f ← instantiateMVars f
  -- consult the leaf table *before* unfolding, so registered functions are never unfolded past
  if let some e ← leafFor f then return e
  let f ← if f.isLambda then pure f else whnf f
  let f ← if f.isLambda then pure f else etaExpand f
  lambdaTelescope f fun xs body => do
    unless xs.size == 1 do
      throwError "bounds: expected a one-argument function; uncurry it first"
    let a := xs[0]!
    let α ← inferType a
    let β ← inferType body
    if body == a then return ← mkAppOptM ``Bounds.id #[some α, none]
    if !body.containsFVar a.fvarId! then
      return ← mkAppOptM ``Bounds.const #[some α, some β, none, none, some body]
    if let .proj ``Prod i u := body then
      let bu ← synthBounds fuel (← mkLambdaFVars #[a] u)
      let_expr Prod A B := ← whnf (← inferType u) | throwError "bounds: bad projection"
      let head ← if i == 0 then mkAppOptM ``Bounds.fst #[some A, some B, none, none]
                 else mkAppOptM ``Bounds.snd #[some A, some B, none, none]
      return ← mkAppM ``Bounds.comp #[head, bu]
    match_expr body with
    | Prod.mk _ _ u v =>
        return ← mkAppM ``Bounds.pair #[← synthBounds fuel (← mkLambdaFVars #[a] u),
                                        ← synthBounds fuel (← mkLambdaFVars #[a] v)]
    | List.cons _ u v =>
        return ← mkAppM ``Bounds.cons #[← synthBounds fuel (← mkLambdaFVars #[a] u),
                                        ← synthBounds fuel (← mkLambdaFVars #[a] v)]
    | Prod.fst A B u =>
        return ← mkAppM ``Bounds.comp
          #[← mkAppOptM ``Bounds.fst #[some A, some B, none, none],
            ← synthBounds fuel (← mkLambdaFVars #[a] u)]
    | Prod.snd A B u =>
        return ← mkAppM ``Bounds.comp
          #[← mkAppOptM ``Bounds.snd #[some A, some B, none, none],
            ← synthBounds fuel (← mkLambdaFVars #[a] u)]
    | List.tail E u =>
        return ← mkAppM ``Bounds.comp
          #[← mkAppOptM ``Bounds.tail #[some E, none],
            ← synthBounds fuel (← mkLambdaFVars #[a] u)]
    | Option.getD E h d =>
        match_expr h with
        | List.head? _ u =>
            return ← mkAppM ``Bounds.comp
              #[← mkAppOptM ``Bounds.headD #[some E, none, some d],
                ← synthBounds fuel (← mkLambdaFVars #[a] u)]
        | _ =>
            return ← mkAppM ``Bounds.comp
              #[← mkAppOptM ``Bounds.optionGetD #[some E, none, some d],
                ← synthBounds fuel (← mkLambdaFVars #[a] h)]
    | cond _ c t e =>
        return ← mkAppM ``Bounds.ite #[← synthBounds fuel (← mkLambdaFVars #[a] c),
                                       ← synthBounds fuel (← mkLambdaFVars #[a] t),
                                       ← synthBounds fuel (← mkLambdaFVars #[a] e)]
    | _ => pure ()
    -- `g x`, and `g x y`, where `g` itself does not mention the argument
    if let .app g x := body then
      if !g.containsFVar a.fvarId! then
        if let some cert ← leafFor g then
          return ← mkAppM ``Bounds.comp #[cert, ← synthBounds fuel (← mkLambdaFVars #[a] x)]
      if let .app g' y := g then
        if !g'.containsFVar a.fvarId! then
          if let some cert ← leafFor (← mkAppM ``Function.uncurry #[g']) then
            return ← mkAppM ``Bounds.comp
              #[cert, ← mkAppM ``Bounds.pair
                  #[← synthBounds fuel (← mkLambdaFVars #[a] y),
                    ← synthBounds fuel (← mkLambdaFVars #[a] x)]]
    if fuel == 0 then throwError "bounds: out of fuel at{indentExpr body}"
    match ← unfoldDefinition? body with
    | some body' => synthBounds (fuel - 1) (← mkLambdaFVars #[a] (← whnfCore body'))
    | none =>
        throwError "bounds: no rule for{indentExpr body}\n\
          Register a certificate for it with `@[bounds]`, or rewrite it using `cond`."

/-- Synthesise a resource certificate for the function in the goal. -/
elab "bounds" : tactic => do
  let goal ← getMainGoal
  let ty ← whnf (← goal.getType)
  let_expr Bounds _ _ _ _ f := ty | throwError "bounds: goal is not a `Bounds` goal"
  let e ← synthBounds 100 f
  let ety ← inferType e
  unless ← isDefEq ety ty do
    throwError "bounds: synthesised a certificate of type{indentExpr ety}"
  goal.assign e

end MultiTapeTM

end Turing
