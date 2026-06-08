/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.Prog
public import Cslib.Computability.Machines.RoseTreeMachine.V4.PB
public import Cslib.Computability.Machines.RoseTreeMachine.V4.Tools
public import Cslib.Computability.Machines.RoseTreeMachine.V3.DataEncode

/-! # Simulating a Prog in an InPlace Prog
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

section InPlaceSim

open PB


/- ===================== derived data/value combinators ===================== -/
def el0 := PB.head
def el1 (s : PB) : PB := PB.head (PB.tail s)
def el2 (s : PB) : PB := PB.head (PB.tail (PB.tail s))
def el3 (s : PB) : PB := PB.head (PB.tail (PB.tail (PB.tail s)))
def wrap (a : PB) : PB := PB.cons a PB.empty
def triT (a b c : PB) : PB := PB.cons a (PB.cons b (PB.cons c PB.empty))
/-- Build a quadruple of values. -/
def quad (a b c e : PB) : PB := PB.cons a (.cons b (.cons c (.cons e .empty)))
def isNilT (x a b : PB) : PB := iteT x PB.empty a b                  -- x = [] ? a : b
def litT : Data → PB | .l xs => xs.foldr (fun x acc => PB.cons (litT x) acc) PB.empty

def tagT (t : Nat) (x : PB) : PB := PB.toPair (natT t) x               -- tagged = [tag, payload]
def tagOf (v : PB) : PB := el0 v
def payOf (v : PB) : PB := el1 v

/-- Variables are encoded in unary to make environment access easier. -/
def encodeUnary : ℕ → Data
  | 0 => .l []
  | k + 1 => .l [encodeUnary k]

def unarySucc : PB → PB := wrap
def unaryPred : PB → PB := .head

/-- Computes `list.getElem?[index]` where `index` is encoded in unary. -/
def getElemUnary (list index : PB) : PB := .snd (PB.while_ (PB.toPair index list)
  (fun st => PB.elim st .empty (fun index list =>
    .ifEq index (.constant (encodeUnary 0))
       (.head list)
       (.toPair (unaryPred index) (PB.tail list)))))

/- ===================== encodings ===================== -/
def MODE_EVAL : Nat := 0
def MODE_APPLY : Nat := 1
-- value tags
def dvPay (v : PB) : PB := payOf v                                -- the underlying list
def cloBody (v : PB) : PB := el0 (payOf v)
def cloEnv  (v : PB) : PB := el1 (payOf v)

-- frame tags
def FPB.cons:Nat:=0  def FConsH:Nat:=1  def FElim:Nat:=2  def FIfY:Nat:=3
def FIfC:Nat:=4    def FAppF:Nat:=5   def FAppA:Nat:=6  -- FFold:=7, FWhile:=8 (SKETCH)
def frPB.cons (t e : PB) := tagT FPB.cons (PB.toPair t e)
def frConsH (h : PB)   := tagT FConsH (wrap h)
def frElim (em cs e : PB) := tagT FElim (triT em cs e)
def frIfY (y t e ev : PB) := tagT FIfY (quadT y t e ev)
def frIfC (xv t e ev : PB) := tagT FIfC (quadT xv t e ev)
def frAppF (a ev : PB) := tagT FAppF (PB.toPair a ev)
def frAppA (clo : PB)  := tagT FAppA (wrap clo)

-- tags for encoding the inductive type
def tagVar : ℕ := 0
def tagEmpty : ℕ := 1
def tagCons : ℕ := 2
def tagElim : ℕ := 3
def tagWhile : ℕ := 4
def tagFn : ℕ := 5
def tagApp : ℕ := 6

def encodeProg : Prog → Data
  | .var i => .l [DataEncode.encode tagVar, encodeUnary i]
  | .empty => .l [DataEncode.encode tagEmpty]
  | .cons h t => .l [DataEncode.encode tagCons, encodeProg h, encodeProg t]
  | .elim v e c => .l [DataEncode.encode tagElim, encodeProg v, encodeProg e, encodeProg c]
  | .while_ i b => .l [DataEncode.encode tagWhile, encodeProg i, encodeProg b]
  | .fn b => .l [DataEncode.encode tagFn, encodeProg b]
  | .app f a => .l [DataEncode.encode tagApp, encodeProg f, encodeProg a]


instance : DataEncode Prog where
  encode := encodeProg
  h_inj := by sorry

def tagData : ℕ := 0
def tagClosure : ℕ := 1
def encodeValue : Value → Data
  | .data d => .l [DataEncode.encode tagData, d]
  | .closure env body =>
      .l [DataEncode.encode tagClosure, Data.l (env.map encodeValue), encodeProg body]

instance : DataEncode Value where
  encode := encodeValue
  h_inj := by sorry

def mkValueData (x : PB) : PB := .cons (.constantEnc tagData) x
def mkValueClosure (body env : PB) : PB := .cons (.constantEnc tagClosure) (.toPair body env)

inductive Op
  | eval (p : Prog) (env : List Values)
  | cons
  | elim
  | while_
  | fn
  | app

structure State where
   ops : List Op
   values : List Value
   env : List Value

def simulate (s : State) : State :=
  match (s.ops, s.values) with
  | (.eval p env :: rops, values) => sorry
  | (.cons :: rops, (.data hd) :: (.data tl) :: values) =>
      ⟨rops, (.data (Data.l (hd :: tl.asList))) :: values, s.env⟩
  | (.elim :: rops, (.data v) :: (.closure em emEnv) :: (.closure cs csEnv :: values)) =>
       match v with
        | Data.l [] => ⟨(.eval em emEnv) :: rops, values, s.env⟩
        | Data.l (hd :: tl) =>
            let cEnv := [Value.data hd, Value.data (Data.l tl)] ++ s.env
            match cs with
             | .closure cEnv' cBody =>
                 ⟨rops, Value.empty :: values, cEnv ++ cEnv'⟩
             | _ => ⟨rops, Value.empty :: values, s.env⟩
        | _ => ⟨rops, Value.empty :: values, s.env⟩
  match s.prog with
   | .var i => (ops, (env[(i : ℕ)]?.getD (Value.data (.l []))) :: values)
   | .empty => (ops, (.data (Data.l [])) :: values)
   | .cons h t => Data.l [simulate h env, simulate t env]
   | .elim v e c =>
       match simulate v env with
        | Data.l [] => simulate e env
        | Data.l (hd :: tl) =>
            let cVal := simulate c env
            match cVal with
             | Value.closure cEnv cBody =>
                 simulate cBody (Value.data hd :: Value.data (Data.l tl) :: cEnv)
             | _ => Value.empty

/-- Evaluate a program into a stack element. -/
def modeEval : ℕ := 0
/-- Apply the operation on the top of the stack. -/
def modeApply : ℕ := 1

/- ===================== machine ===================== -/
def mkState (m : ℕ) (prog env stack : PB) : PB :=
    quad (PB.constantEnc m) prog env stack
def evalS (cv env stk : PB) := mkState modeEval cv env stk
def pushApply (v stack : PB) := mkState modeApply v PB.empty stack          -- env unused in APPLY
def push (f stk : PB) : PB := PB.cons f stk

def cases (n : PB) (caseList : List (Nat × PB)) (default : PB) : PB := match caseList with
  | [] => default
  | (tag, f) :: rest => PB.ifEq
      n (PB.constantEnc tag) f (cases n rest default)

/-- Flatten the program into the operation stack. -/
def flatten (prog env stack : PB) : PB :=
  cases (.head prog) [
     (tagVar,
  ] (.empty)

def evalStep (prog env stack : PB) : PB :=
  cases (.head prog) [
    (tagVar, pushApply stack (getElemUnary env (.tail prog))),
    (tagEmpty, pushApply (mkValueData PB.empty) stack),
    (Ncons,  letT (payOf cv) (fun p =>                                  -- p = [h, t]
               evalS (el0 p) env (push (frPB.cons (el1 p) env) stk))),
    (Nelim,  letT (payOf cv) (fun p =>                                  -- p = [v, em, cs]
               evalS (el0 p) env (push (frElim (el1 p) (el2 p) env) stk))),
    (NifEq,  letT (payOf cv) (fun p =>                                  -- p = [x, y, t, e]
               evalS (el0 p) env (push (frIfY (el1 p) (el2 p) (el3 p) env) stk))),
    (Nfn,    pushApply (mkValueClosure (payOf prog) env) stack),                          -- capture (copy) env
    (Napply, letT (payOf cv) (fun p =>                                  -- p = [f, a]
               evalS (el0 p) env (push (frAppF (el1 p) env) stk)))
    -- (Nfold, Nwhile): SKETCH — push frFold [body, remaining, acc, env] / frWhile [body, env]
    --   and iterate exactly like a fold/while frame; same pattern as below, see notes.
  ] (pushApply prog PB.empty)                                                  -- stuck ⇒ halt

/-- APPLY mode: `v` flows into the top stack frame. -/
def applyStep (v stk : PB) : PB :=
  letT (PB.head stk) (fun f => letT (PB.tail stk) (fun rest =>
    caseTag f [
      (FPB.cons, letT (payOf f) (fun p =>                                 -- p = [t, env']
                 evalS (el0 p) (el1 p) (push (frConsH v) rest))),
      (FConsH, letT (payOf f) (fun p =>                                 -- p = [hv]; v = tail value
                 applyS (dvT (PB.cons (el0 p) (dvPay v))) rest)),
      (FElim,  letT (payOf f) (fun p =>                                 -- p = [em, cs, env']; v = scrut
                 letT (dvPay v) (fun xs =>
                   isNilT xs
                     (evalS (el0 p) (el2 p) rest)                       -- nil ⇒ em
                     (evalS (el1 p)                                     -- cons ⇒ cs, env' + [hd, tl]
                        (PB.cons (PB.head xs) (PB.cons (dvT (PB.tail xs)) (el2 p))) rest)))),
      (FIfY,   letT (payOf f) (fun p =>                                 -- p = [y, t, e, env']; v = x
                 evalS (el0 p) (el3 p) (push (frIfC v (el1 p) (el2 p) (el3 p)) rest))),
      (FIfC,   letT (payOf f) (fun p =>                                 -- p = [xv, t, e, env']; v = y
                 iteT (el0 p) v (evalS (el1 p) (el3 p) rest)
                                 (evalS (el2 p) (el3 p) rest))),
      (FAppF,  letT (payOf f) (fun p =>                                 -- p = [a, env']; v = closure
                 evalS (el0 p) (el1 p) (push (frAppA v) rest))),
      (FAppA,  letT (payOf f) (fun p =>                                 -- p = [clo]; v = arg value
                 evalS (cloBody (el0 p)) (PB.cons v (cloEnv (el0 p))) rest)) -- enter body, arg::cenv
      -- (FFold, FWhile): SKETCH — step the loop, re-push or fall through.
    ] (applyS v PB.empty)))                                               -- stuck ⇒ halt

/-- final = APPLY mode with empty stack. -/
def isFinalThen (s a b : PB) : PB :=
  iteT (el0 s) (natT MODE_APPLY) (isNilT (el3 s) a b) b

def step (s : PB) : PB :=
  letT (el0 s) (fun mode => letT (el1 s) (fun cv => letT (el2 s) (fun env => letT (el3 s) (fun stk =>
    iteT mode (natT MODE_EVAL) (evalStep cv env stk) (applyStep cv stk)))))

/- ===================== boundary passes (SKETCH) ===================== -/
-- raw input Data ⟶ tagged value (wrap every node as `dvT`); a tree traversal using the
-- same stack-machine pattern as above. Placeholder shown; replace with the traversal.
def wrapVal (x : PB) : PB := mkValueData x          -- SKETCH: only correct for flat lists of nils
def unwrapVal (v : PB) : PB := dvPay v       -- SKETCH: inverse traversal

/- ===================== top-level interpreter ===================== -/
/-- `interpFor p : Prog` runs FProg `p` (baked in as a Data literal) on the input (var 0).
    For a *universal* interpreter, read `p` from the input instead of `litT p`. -/
def interpFor (p : FProg) : Prog :=
  ( letT (evalS (litT (enc p)) (oneT (wrapVal (V 0))) PB.empty) (fun s0 =>
      letT (whileT s0 (fun s => isFinalThen s PB.empty (step s))) (fun fin =>
        unwrapVal (el1 fin))) ) 1

end RTM

end InPlaceSim

end V4

end RoseTreeMachine

end Turing
