/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cut2A.SpatialMeasureDefs
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs


/-! The localized upper weight built from a C2-A `SpatialMeasure`, as a definition only: `spatialUpperWeight`.  Body
verbatim from V5-SPACE `VineSpaceK/NodeMeasure.lean`; its theorems (`spatialUpperWeight_norm`,
`enginePullback_spatialUpperWeight`) are not ported.  When V5-SPACE lands, `NodeMeasure` must import this module and
drop its copy. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A
variable {V α : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
  [MeasurableSpace α] {d : ℕ}

def spatialUpperWeight (F : SpatialMeasure V α) (q0 : V)
    (Q : Fin 4 → Mom d →L[ℝ] V) (q : Fin 4 → Mom d) : ℂ :=
  F.value (q0 + ∑ i, Q i (q i))

end WaveTurbulence.VineSpaceK
