/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.PieceTree

/-!
# Prop 6.1, `q > q'`: the bottom couple

The lowest factor of TARGET (prooflayer1-1) is a single-layer couple in layer `q'`, evaluated at `(q'+1, s)`.
From B2.1 on `[q', q'+1]²`, by the trace at `t = q'+1` (`Layered.restr_trace_transport`), its weighted error and
its weighted leading term are bounded as functions of `s` alone on any target box mapped into the unit box by
`t ↦ t − (·, q')` (`couple_bottom_bounds`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

theorem trace_line_couple (q' : ℕ) (u : Fin 2 → ℝ) (hu : u ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    Function.update u 0 1 + ![(q' : ℝ), q'] ∈ closure (interior (timeBox (q' : ℝ) q')) := by
  rw [closure_interior_timeBox]
  have h1 := hu 1
  refine ⟨?_, ?_⟩
  · rw [update0_add_apply_zero]
    simp only [Matrix.cons_val_zero]
    constructor <;> linarith
  · rw [update0_add_apply_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> linarith [h1.1, h1.2]

section Bottom

variable (P : WTParams) {q' n : ℕ} (Q : RegCpl) (LG : LayeredGarden 2) (H : LeafProfiles 2 P.d)

end Bottom

end WaveTurbulence.PL234
