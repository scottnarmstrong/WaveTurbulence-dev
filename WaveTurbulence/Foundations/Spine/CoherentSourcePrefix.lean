/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.CoherentSourceConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.LowProfilePrefix
/-! A common literal parameter prefix for the coherent leg, without an additional input gate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem coherent_source_prefix
    (hLeaf : LeafwiseCoherentApproximationGate) (hTaylor : CoherentTaylorGate) :
    WTPrefix (fun P => (LeafwiseCoherentApproximationOrder0At P ∧ SourceCoherentTaylorAt P) ∧
      (TaylorBoundAt P ∧ LowProfileAt P)) := by
  have hleft := prefix_and
    (prefix_map (fun _ h => LeafwiseCoherentApproximationAt.toOrder0 h) (show WTPrefix LeafwiseCoherentApproximationAt from hLeaf))
    (show WTPrefix SourceCoherentTaylorAt from hTaylor)
    leafwiseCoherentApproximation_largeConstantMonotone sourceCoherentTaylor_largeConstantMonotone
  have hright := prefix_and taylorBound_prefix lowProfile_prefix
    taylorBound_largeConstantMonotone lowProfile_largeConstantMonotone
  exact prefix_and hleft hright
    (leafwiseCoherentApproximation_largeConstantMonotone.and sourceCoherentTaylor_largeConstantMonotone)
    (taylorBound_largeConstantMonotone.and lowProfile_largeConstantMonotone)

end WaveTurbulence.LGSpine
