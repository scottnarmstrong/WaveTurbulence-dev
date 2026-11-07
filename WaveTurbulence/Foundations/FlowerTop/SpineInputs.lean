/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.Stage1BothBridge
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderFourierSTFree
public import WaveTurbulence.Foundations.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.Prefix

/-!
# R61/R77 replacement for the five-field flower spine

These are LG's scalar ST gates and P5's corrected free-clock Fourier gate.
The three old flower-specific gates are absent. This bundle does not include
vector-clock or character-uniform SX2 providers; those are separate obligations.
The adapters below recover only the existing unanchored, stub-free estimates.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine

/-- P5's coarse ST target, with the existing LG parameter-prefix scope. -/
abbrev P5CoarseInput : Prop := WTPrefix CoarseSplicedAtST

/-- P5's R77 corrected free-clock Fourier target; never the all-clock ST gate. -/
abbrev P5LadderInput : Prop := WTPrefix FlowerP5.LadderFourierAtST'

/-- One owner boundary for P5, with both exact pointwise gate bodies. -/
abbrev P5Input : Prop := P5CoarseInput ∧ P5LadderInput

/-- R104: the plain Stage 1 reduction gate of main's spine (the no-stub, no-anchor case of STB2 is all that is used). -/
abbrev Stage1STInput : Prop := LGSpine.Stage1ReductionGate

abbrev LeafCoherentInput : Prop := LeafwiseCoherentApproximationGate
abbrev LeafDecayInput : Prop := LeafwiseIncoherentDecayGate

/-- R61 P9: exactly the shared five inputs, with R77's corrected ladder target. -/
structure FlowerSpineInputsV3 : Prop where
  coarse : P5CoarseInput
  ladder : P5LadderInput
  stage1 : Stage1STInput
  leafCoherent : LeafCoherentInput
  leafDecay : LeafDecayInput

/-- Assemble only the five-field spine interface; no flower estimate is a premise. -/
theorem flowerSpineInputsV3_of_inputs (h5 : P5Input) (hS : Stage1STInput)
    (hC : LeafCoherentInput) (hD : LeafDecayInput) : FlowerSpineInputsV3 :=
  ⟨h5.1, h5.2, hS, hC, hD⟩

/-- No-stub specialization of P5's coarse estimate. -/
theorem FlowerSpineInputsV3.coarseGate (S : FlowerSpineInputsV3) : CoarseSplicedGate :=
  prefix_map (fun P h => coarseSplicedAt_of_ST P h) S.coarse

/-- The corrected free-clock gate recovers the native unpinned ladder estimate. -/
theorem FlowerSpineInputsV3.ladderGate (S : FlowerSpineInputsV3) : LadderFourierGate :=
  prefix_map (fun P h => FlowerP5.ladderFourierAt_of_ST' P h) S.ladder

/-- Empty anchors and stubs recover LG's native Stage 1 reduction. -/
theorem FlowerSpineInputsV3.stage1Gate (S : FlowerSpineInputsV3) : Stage1ReductionGate :=
  S.stage1

/-- Existing ordinary estimates follow; this is not a stub/flower estimate. -/
theorem FlowerSpineInputsV3.nonregularHalf (S : FlowerSpineInputsV3)
    (hcount : FinalCountGateHalf) :
    WTPrefix fun P => 1 / 2 < P.γ → NonregularEstimateAt P :=
  nonregular_prefix_half S.stage1Gate S.coarseGate S.ladderGate hcount

/-- The already established unpinned L0 regular channel, not the missing two-time family theorem. -/
theorem FlowerSpineInputsV3.regularL0 (S : FlowerSpineInputsV3) :
    WTPrefix FlowerReg.RegularCouplesL0At :=
  FlowerReg.regularCouplesL0_of_leafwise S.leafCoherent S.leafDecay

end WaveTurbulence.FlowerTop
