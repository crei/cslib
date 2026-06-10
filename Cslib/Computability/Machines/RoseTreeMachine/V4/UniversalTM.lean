/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V4.Tools
public import Cslib.Computability.Machines.RoseTreeMachine.V3.DataEncode
public import Cslib.Foundations.Data.BiTape

/-! # RoseTreeMachine V4 — UniversalTM (definitions only)

A port of the universal single-tape Turing machine to the functional V4 language. This file
contains only the program-builder *definitions* (no correctness or resource proofs); the
removed first-order primitives `fold`/`ifEq`/`let`/`constant` are now the derived combinators
from `V4.Tools`, so the whole construction lives in the in-place fragment.
-/

@[expose] public section

namespace Turing

namespace RoseTreeMachine

namespace V4

/-- Encoding of a direction, reusing the `Bool` encoding. -/
instance : DataEncode Dir where
  encode := fun
    | Dir.left => DataEncode.encode true
    | Dir.right => DataEncode.encode false
  h_inj := by intro a b h; cases a <;> cases b <;> simp_all [DataEncode.encode]

/-- Overwrite the symbol under the head of an encoded bitape. -/
def bitape_write (t v : PB) : PB := PB.cons v t.tail

/-- Prepend an optional symbol to an encoded stack tape, collapsing leading blanks. -/
def stackTape_cons (x st : PB) : PB :=
  PB.optionElim x
    (PB.elim st
      PB.empty
      (fun _ _ => PB.cons x st))
    (fun _ => PB.cons x st)

/-- The head component of an encoded bitape. -/
def bitape_head (t : PB) : PB := t.fst
/-- The left component of an encoded bitape. -/
def bitape_left (t : PB) : PB := t.snd.fst
/-- The right component of an encoded bitape. -/
def bitape_right (t : PB) : PB := t.snd.snd

/-- Move an encoded bitape one cell to the left. -/
def bitape_move_left (t : PB) : PB :=
  toPair (bitape_left t).head
    (toPair
      (bitape_left t).tail
      (stackTape_cons (bitape_head t) (bitape_right t)))

/-- Move an encoded bitape one cell to the right. -/
def bitape_move_right (t : PB) : PB :=
  toPair (bitape_right t).head
    (toPair
      (stackTape_cons (bitape_head t) (bitape_left t))
      (bitape_right t).tail)

/-- Move an encoded bitape in the encoded direction `dir`. -/
def bitape_move (tape dir : PB) : PB :=
  PB.ifEq dir (constant (DataEncode.encode Dir.left))
    (bitape_move_left tape)
    (bitape_move_right tape)

/-- Optionally move an encoded bitape, or leave it unchanged on `none`. -/
def bitape_optionMove (t dir : PB) : PB :=
  PB.optionElim dir
    t
    (fun d => bitape_move t d)

/-- Evaluate a function given as a graph (list of `(x, y)` pairs) at `arg`: returns `some y`
for the first pair whose first component equals `arg`, otherwise `none`. -/
def eval_fun_graph (graph : PB) (arg : PB) : PB :=
  PB.fold
    (fun acc x =>
      PB.optionElim acc
        (PB.ifEq x.fst arg (PB.some x.snd) PB.empty)
        fun _ => acc)
    PB.empty graph

/-- The state component of an encoded configuration. -/
def cfg_state (cfg : PB) : PB := cfg.fst
/-- The bitape component of an encoded configuration. -/
def cfg_bitape (cfg : PB) : PB := cfg.snd

/-- Evaluate the transition function (given as a nested graph) at state `q` and symbol `c`,
returning `((write, dir), q')`. -/
def eval_tr (tr : PB) (q c : PB) : PB :=
  (eval_fun_graph (eval_fun_graph tr q).head c).head

/-- One step of the simulated single-tape TM, given the transition graph `tr` and an encoded
configuration `cfg`. Returns an encoded `Option Cfg` (`none`/empty signals halting). -/
def singleTapeTM_step (tr : PB) (cfg : PB) : PB :=
  PB.optionElim (cfg_state cfg)
    PB.empty
    (fun q' => PB.letIn (cfg_bitape cfg) (fun tape =>
      PB.letIn (eval_tr tr q' tape.head) (fun tr_val =>
        .some (toPair
          tr_val.snd
          (bitape_optionMove (bitape_write tape tr_val.fst.fst) tr_val.fst.snd)))))

/-- The main loop: iterate `singleTapeTM_step` until it returns `none` (halting), keeping the
final configuration as the fixed point. -/
def tm_main_loop (tr : PB) (cfg : PB) : PB :=
  PB.while_ cfg
    (fun acc => PB.optionElim (singleTapeTM_step tr acc) acc (fun next => next))

/-- Reverse an encoded list. -/
def reverse (x : PB) : PB :=
  PB.fold (fun acc el => PB.cons el acc) PB.empty x

/-- Map `f` over an encoded list. -/
def list_map (x : PB) (f : PB → PB) : PB :=
  reverse (PB.fold (fun acc el => PB.cons (f el) acc) PB.empty x)

/-- Discard the `none` elements of an encoded list of options. -/
def list_reduceOption (x : PB) : PB :=
  reverse (PB.fold
    (fun acc el => PB.optionElim el acc (fun y => PB.cons y acc))
    PB.empty x)

/-- The head of an encoded list as an `Option`. -/
def list_head_option (input : PB) : PB :=
  PB.elim input PB.empty (fun hd _tl => PB.some hd)

/-- Turn an encoded input string into the initial encoded bitape. -/
def string_to_tape (input : PB) : PB :=
  toPair (list_head_option input) (toPair .empty (list_map input.tail PB.some))

/-- The initial encoded configuration for start state `q₀` and `input`. -/
def initial_config (q₀ : PB) (input : PB) : PB :=
  toPair (PB.some q₀) (string_to_tape input)

/-- Turn the final configuration into the output, taking the head and right part of the tape
and discarding the blank (`none`) cells. -/
def final_config_to_output (cfg : PB) : PB :=
  list_reduceOption (PB.cons (bitape_head cfg.snd) (bitape_right cfg.snd))

/-- A universal single-tape TM. The input is expected to be `((initialState,
transitionFunction), input)`; if it terminates, the output is the tape contents under and to
the right of the head. -/
def universal_tm (input : PB) : PB :=
  final_config_to_output
    (tm_main_loop input.fst.snd (initial_config input.fst.fst input.snd))

end V4

end RoseTreeMachine

end Turing
