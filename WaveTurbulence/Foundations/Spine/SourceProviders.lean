/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Gate30
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceApp
public import WaveTurbulence.Foundations.Spine.PL234Draft.CoherentTaylor
public import WaveTurbulence.Foundations.Spine.RA1LW.Gate
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.Gate
public import WaveTurbulence.Foundations.Spine.Final4c
public import WaveTurbulence.Foundations.Spine.LadderDecayFinal
public import WaveTurbulence.Foundations.Spine.GatePinned
public import WaveTurbulence.Frozen.Theorems.RegularAsymptotics
/-! Proved analytic inputs to the current LG spine. -/
public section
open WaveTurbulence.Induct
namespace WaveTurbulence.Spine

/-- Regular asymptotics with a separate profile at each leaf. -/
theorem leafwise_regular_asymptotics : LGSpine.LeafwiseRegularAsymptoticsGate :=
  RA1Leafwise.leafwiseRegularAsymptotics

/-- Prop 6.1 with separate leaf profiles. -/
theorem leafwise_coherent_approximation : LGSpine.LeafwiseCoherentApproximationGate :=
  PL2330.leafwiseCoherentApproximationGate30 regularAsymptotics leafwise_regular_asymptotics

/-- Prop 6.2 with the regular asymptotic inputs discharged. -/
theorem coherent_taylor : LGSpine.CoherentTaylorGate :=
  PL234.coherentTaylorGate regularAsymptotics leafwise_regular_asymptotics

/-- Incoherent decay with separate leaf profiles. -/
theorem leafwise_incoherent_decay : LGSpine.LeafwiseIncoherentDecayGate :=
  IncohLeafwise.leafwiseIncoherentDecay

/-- The ladder Fourier estimate on the source time domain. -/
theorem ladder_fourier : LGSpine.LadderFourierGate := Ladder.ladderFourier_prefix

/-- The coarse estimate on the canonical spliced kernel. -/
theorem coarse_spliced : LGSpine.CoarseSplicedGate := CoarseSpliced.coarseSplicedGatePinned

end WaveTurbulence.Spine
