/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing


-- This is an attempt at proving Savitch's theorem. We start by stating a generic
-- space-efficient graph reachability algorithm.

/-

General idea, assume distance is power of two:

def reachable(a, b, t, r):
  if t = 0:
    return r(a, b)
  else:
    for c in vertices:
      if reachable(a, c, t - 1, r) and reachable(c, b, t - 1, r):
        return True
    return False

Until we have a generic mechanism for recursion, let's translate this into a program that
uses "goto", and every variable is a stack:

def reachable(a, b, t, r):
  terminate = 0
  result = 0
  initial_t = t
  section = [:terminate, :fun_start]
  while !terminate:
    match section.pop()
    | :fun_start =>
      if t = 0:
        result = r(a, b)
        section.push(:fun_return)
      else:
        c.push(0)
        section.push(:loop_start)
    | :loop_start =>
      if c.top() = num_vertices:
        c.pop()
        result = 0
        section.push(:fun_return)
      else:
        a.push(a.top())
        b.push(c.top())
        t.push(t.top() - 1)
        section.push(:after_first_rec)
        section.push(:fun_start)
    | :after_first_rec =>
        if result == 1:
          a.push(c.top())
          b.push(b.top())
          t.push(t.top() - 1)
          section.push(:after_second_rec)
          section.push(0)
        else:
          result = 0
          section.push(:loop_continue)
    | :after_second_rec =>
        if result == 1:
          c.pop()
          section.push(:fun_return)
        else:
          section.push(:loop_continue)
    | :loop_continue =>
        c.push(c.top() + 1)
        section.push(:loop_start)
    | :fun_return =>
      a.pop()
      b.pop()
      t.pop()
    | :terminate =>
      terminate = 1
  -- cleanup
  terminate.pop()
  initial_t.pop()


-/


end Turing
