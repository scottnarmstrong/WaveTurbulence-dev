/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.FinalFamily
public import WaveTurbulence.Foundations.Stage1.Producer
public import WaveTurbulence.Foundations.VineEst.V5Proof

/-! # The flower estimate `layergardenFlower_v3` from three named inputs (PORT FT1)

`layergardenFlower_v3_of_three` is flower-top's `layergardenFlower_v3_of_owners'` (FLOWERTOP EXPORT, session 3;
R103/R104/R108) with its plain Stage-1 input `hStage1 : LGSpine.Stage1ReductionGate` discharged on main by
`Spine.stage1ReductionGate_of_V5' VineEst.vineEstCanonLayerHalfMK` (batches 4b-2 and 4b-3). Its conclusion
`V2Chain.LayergardenFlowerV3Gate` is the body of the frozen anchor `layergardenFlower_v3` (T Prop `flowerest1`,
L2279–L2305), generated from the frozen file. The remaining inputs are definitions, not assumptions of any other
theorem:

* `hFam : WTPrefixP (FC23UniformCut1Input C U)` (`FC23.FC23UniformCut1At`, owner FC23), with `0 < C d`, `0 < U P p`;
* `hCut2 : Cut2EB.PositiveCut2FrozenInput` (positive cut2 at the frozen gain `1/9`, owner C2-E-B);
* `hCut2Zero : Cut2ZeroFrozenInput` (`WTPrefixP (FlowerCaseAt CaseCut2Zero)`, the `j₂ = 0` cut2 clause, owner C2-E-B).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop

/-- **`layergardenFlower_v3` from three named inputs**: `layergardenFlower_v3_of_owners'` with the plain Stage-1
reduction gate supplied by main's S2 producer applied to main's V5 (`vineEstCanonLayerHalfMK`). -/
theorem layergardenFlower_v3_of_three (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p)
    (hFam : WTPrefixP (FC23UniformCut1Input C U))
    (hCut2 : Cut2EB.PositiveCut2FrozenInput)
    (hCut2Zero : Cut2ZeroFrozenInput) : V2Chain.LayergardenFlowerV3Gate :=
  layergardenFlower_v3_of_owners' C U hC hU hFam hCut2 hCut2Zero
    (Spine.stage1ReductionGate_of_V5' VineEst.vineEstCanonLayerHalfMK)

end WaveTurbulence.FlowerTop
