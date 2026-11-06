/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputs
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
/-! Compatibility names for the canonical 30d spine gates. -/
@[expose] public section
open WaveTurbulence.Induct
namespace WaveTurbulence.PL2330Pin
abbrev CoherentApproximationGate : Prop := LGSpine.CoherentApproximationGate
abbrev LeafwiseCoherentApproximationGate : Prop := LGSpine.LeafwiseCoherentApproximationGate
end WaveTurbulence.PL2330Pin
