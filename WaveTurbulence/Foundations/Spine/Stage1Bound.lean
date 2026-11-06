/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Gate
public import WaveTurbulence.Foundations.Spine.StageOrderGrowth
public import WaveTurbulence.Foundations.Spine.WeightedLeafKernel
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
/-! TARGET (finalprooffin2) for a leaf-modified kernel family: the Stage 1 reduction gate applied to the
carrier sum, then the core bound of the pieces. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

-- AMEND6' (R47-FINAL): `stage1_family_bound` (arbitrary leaf families, old gate) is replaced by `stage1_type_bound` (Stage1TypeBound).

end WaveTurbulence.LGSpine
