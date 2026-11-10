/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePieceProfile
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedCode
public import WaveTurbulence.Foundations.Vine.A.VineBatchUnitJoints
public import WaveTurbulence.Foundations.Vine.A.VineMarkedClasses
/-! Complete A4 kernel-relevant profiles on the actual fixed-sigma plain-garden classes. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist LGSpine
variable {R p : ℕ} {kind : Bool}

/-- The successor producer piece at the unique prime representative of a plain garden. -/
noncomputable def normalizedPiece (a : PrescribedPrimeGarden (2 * R)) (d : ℕ)
    (Mk : Set (Stage1.CLVine a.prime.skeleton) := ∅) :=
  NormalizedSplice.stage1PieceOf d a.prime.prime.1 a.layered a.prime.decodes a.totalSigma Mk

/-- The actual normalized garden, layers, hinges, counts and entire gap functional. -/
noncomputable def profile (a : PrescribedPrimeGarden (2 * R)) : PieceProfile (2 * R) :=
  familyPieceProfile a.state a.totalSigma

/-- B1b-3 (Mk-general form of `profile`): the piece profile (gap functional, layers, hinges, counts) of the fine′
state at the marking `mk`. -/
noncomputable def profileMk (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) : PieceProfile (2 * R) :=
  familyPieceProfileMk (a.state mk) a.totalSigma (mk a.prime)

end WaveTurbulence.VineA.PrescribedPrimeGarden
