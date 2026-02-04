/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeExtension

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

variable [Inhabited α] [Fintype α]

variable {k : ℕ}

public structure HeadStats where
  --- The minimal (left-most) position of the head during the computation,
  --- relative to the starting position.
  min : ℤ
  --- The maximal (right-most) position of the head during the computation,
  --- relative to the starting position.
  max : ℤ
  --- The final position of the head after the computation, relative to the
  --- starting position.
  final : ℤ
  h_bounds : min ≤ final ∧ final ≤ max ∧ min ≤ 0 ∧ 0 ≤ max

public def headStats (tm : MultiTapeTM k α) (tapes : Fin k → BiTape α) :
  Part (Fin k → HeadStats) := sorry

-- TODO maybe "tape with stats?"
public def MultiTapeTM.evalWithStats (tm : MultiTapeTM k α) (tapes : Fin k → BiTape α) :
  Part ((Fin k → BiTape α) × (Fin k → HeadStats)) := sorry

-- move this somewhere else
def seq (tm₁ tm₂ : MultiTapeTM k α) : MultiTapeTM k α := sorry

lemma seq_evalWithStats (tm₁ tm₂ : MultiTapeTM k α) (tapes : Fin k → BiTape α) (i : Fin k) :
  (seq tm₁ tm₂).evalWithStats tapes = ((tm₁.evalWithStats tapes).bind
    (fun (tapes', stats₁) => (tm₂.evalWithStats tapes').map (fun (tapes'', stats₂) =>
      (tapes'',
      (fun i => (match (stats₁ i, stats₂ i) with
      | (⟨min₁, max₁, final₁, h₁⟩, ⟨min₂, max₂, final₂, h₂⟩) =>
        ⟨min min₁ (min₂ + final₁),
        max max₁ (max₂ + final₁),
        final₁ + final₂,
        by omega⟩)))))) := by sorry

-- Next step: relate space requirements and head stats.

end Turing
