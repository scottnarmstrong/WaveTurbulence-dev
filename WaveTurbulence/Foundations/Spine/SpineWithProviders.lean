/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceProviders
/-! The LG spine with its analytic providers discharged.
Stage 1 and the half-range final count remain the original named gate inputs. -/
public section
open WaveTurbulence.Induct
namespace WaveTurbulence.Spine

/-- Assemble the spine from the remaining Stage-1 reduction. -/
theorem spineInputs_of_stage1 (hstage1 : LGSpine.Stage1ReductionGate) : LGSpine.SpineInputs :=
  ⟨leafwise_coherent_approximation, coherent_taylor, leafwise_incoherent_decay,
    coarse_spliced, ladder_fourier, hstage1⟩

/-- The exact frozen layergarden-v2 conclusion, conditional on the remaining two gates. -/
theorem layergarden_v2_of_stage1_finalCount
    (hstage1 : LGSpine.Stage1ReductionGate) (hcount : LGSpine.FinalCountGateHalf) :
    V2Chain.LayergardenV2Gate :=
  LGSpine.layergarden_v2_of_spine (spineInputs_of_stage1 hstage1) hcount

end WaveTurbulence.Spine
