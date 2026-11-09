/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputsS10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SpineInputsS10`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 B1.2 `layergarden` from the named spine inputs (Session 10). The final-count gate (row 6,
TARGET finalcount1, F69b-disputed regime) is kept SEPARATE. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct

/-- The spine inputs of LG-SPINE (rows 1-5 and 7-10 of the SPINE.md table). -/
structure SpineInputs : Prop where
  /-- row 1: Prop 6.1, leafwise (PL234, REGREF upstream) -/
  leafCoherent : LeafwiseCoherentApproximationGate
  /-- row 2: Prop 6.2 (PL234) -/
  taylor : CoherentTaylorGate
  /-- row 3: Prop 5.1 / B2.2, leafwise (wt-torus) -/
  leafDecay : LeafwiseIncoherentDecayGate
  /-- row 4: finalsbest1 (S3 LADDER) -/
  coarse : CoarseSplicedGate
  /-- row 5: ladderl1old (S3 LADDER) -/
  ladder : LadderFourierGate
  /-- rows 7-10: the Stage 1 reduction (S2a/S2/S4) -/
  stage1 : Stage1ReductionGate

/-- B1.2 from the spine inputs, with the final-count gate (row 6) as a separate hypothesis. -/
theorem layergarden_of_spine (S : SpineInputs) (hcount : FinalCountGate) : LGSpine.LayergardenGate :=
  layergarden_of_nonregular S.leafCoherent S.taylor S.leafDecay
    (nonregular_prefix S.stage1 S.coarse S.ladder hcount)

end WaveTurbulence.GammaLow.FinalCount.H
