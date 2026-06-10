/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.RoseTreeMachine.V2.Data
public import Cslib.Computability.Machines.RoseTreeMachine.V2.Prog
public import Cslib.Computability.Machines.RoseTreeMachine.V2.DataEncode
public import Cslib.Computability.Machines.RoseTreeMachine.V2.PB
public import Cslib.Computability.Machines.RoseTreeMachine.V2.Tools
public import Cslib.Computability.Machines.RoseTreeMachine.V2.UniversalTM

/-!
# RoseTreeMachine V2

A stack-machine model with `Data` rose-tree values, `Prog` programs (with `meteredEval` /
`eval` / `while_` / `fold`), a `PB` (program-builder) layer with named binders and
`computes_at` reasoning, and a `DataEncode` typeclass for encoding generic types.

The development culminates in `universal_tm`, a `PB` simulating an arbitrary
`SingleTapeTM`, and the theorem `universal_tm_simulates_iff`.

This file is just a re-export of the modules in `V2/`.
-/
