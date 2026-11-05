/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SpineInputs
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.Spine.SourceLadderInputs
public import WaveTurbulence.Foundations.Spine.SourceLadderDecayInput
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
import WaveTurbulence.Frozen.Theorems.RegularAsymptotics
import WaveTurbulence.Foundations.Spine.PL2330Draft.Gate30C
import WaveTurbulence.Foundations.Spine.RA1LW.Gate
import WaveTurbulence.Foundations.Spine.IncohLeafwise.Gate
import WaveTurbulence.Foundations.Spine.Final4c
import WaveTurbulence.Foundations.Spine.LadderDecayFinal
import WaveTurbulence.Foundations.Spine.GatePinned

/-! # Proved analytic inputs to the molecular spine

The coherent approximation inputs consume the sealed regular-asymptotics theorem and its
proved leafwise counterpart. These results assemble the analytic inputs only; the Stage-1
and final-count inputs are separate proof obligations.
-/

public section
namespace WaveTurbulence.Spine

/-- Regular asymptotics with a separate profile at each leaf. -/
theorem leafwise_regular_asymptotics : LGSpine.LeafwiseRegularAsymptoticsGate :=
  RA1Leafwise.leafwiseRegularAsymptotics

/-- The literal 30d coherent approximation bound, with its asymptotic inputs discharged. -/
theorem coherent_approximation : LGSpine.CoherentApproximationGate :=
  PL2330.coherentApproximationGate30 regularAsymptotics leafwise_regular_asymptotics

/-- The corresponding coherent bound for separate leaf profiles. -/
theorem leafwise_coherent_approximation : LGSpine.LeafwiseCoherentApproximationGate :=
  PL2330.leafwiseCoherentApproximationGate30 regularAsymptotics leafwise_regular_asymptotics

/-- Incoherent decay for separate leaf profiles. -/
theorem leafwise_incoherent_decay : LGSpine.LeafwiseIncoherentDecayGate :=
  IncohLeafwise.leafwiseIncoherentDecay

/-- The ladder Fourier bound on the source time domain. -/
theorem ladder_fourier : LGSpine.LadderFourierGate := Ladder.ladderFourier_prefix

/-- The source ladder decay input. -/
theorem ladder_decay : LGSpine.LadderDecayGate := LadderDecay.ladderDecayGate

/-- The coarse spliced bound with the canonical counting data. -/
theorem coarse_spliced : LGSpine.CoarseSplicedGate := CoarseSpliced.coarseSplicedGatePinned

end WaveTurbulence.Spine
