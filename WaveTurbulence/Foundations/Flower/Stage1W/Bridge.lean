/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # STAGE1W-GLUE: Bridge (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 4. Unit weight: the gate specialises to main's plain `Stage1ReductionAt` (non-vacuity) -/

/-- The constant `1` is presented by the Dirac mass at frequency `0` (S2-ST's `gPresented_one`, verbatim proof). -/
theorem gPresented_one {d : ℕ} (J : ℕ) : GPresented J (fun _ : Mom d => (1 : ℂ)) 1 := by
  refine ⟨Unit, inferInstance, ⟨Measure.dirac (), inferInstance, fun _ => 0, measurable_const, fun _ => 1,
    integrable_const _⟩, ?_, fun x => ?_⟩
  · unfold momentMassMom
    simp
  · unfold Cut2A.SpatialMeasure.value
    simp

/-! ## 5. The piece statements (O4 / O3 analogues) and the assembly -/

section Pieces
open WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.ClassCount WaveTurbulence.RedSplice
  WaveTurbulence.VineParamContract

end Pieces


end WaveTurbulence.Flower.Stage1W
