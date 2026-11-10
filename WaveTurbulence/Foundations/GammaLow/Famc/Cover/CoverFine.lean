/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverAdmissible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverBudget
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverTags
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomKindAtJoints
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomScaleExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCountingCardLimits
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCountingChoiceScales
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSecondCollectionExists
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceFullPairTable
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceGapTableObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceGapTableSelection
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceLadderGapExists
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOrdinaryJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsMain
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePrimaryPairChoices
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceRestrictedCarrier
public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedChoiceScaleAbsorption
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedCircuitRank
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedCoverChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredCountA
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredGates
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredRawBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedAbsoluteSum
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedKernel
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.CoverBudget
public import WaveTurbulence.Foundations.Spine.SplicedCoverChoiceScaleBound
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! TARGET finalsbest2 (L2078) for the spliced kernel of an actual choice datum `Cs`, from the
literal gates `ladderl1old` and `finalcount1` (RULINGS R7). All names are conditional helpers:
`Cs` and `SubproConclusions` (subpro and the C1 half of L2116) are hypotheses; the construction
of `Cs` is S2a and `subpro` is S4. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.CoverFine` (sha256 4c28584e7cc991a55b46bb8886c54a50fc9aebf3a2d615c0faf9842bebd543ea) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.LGSpine
open scoped Classical

theorem exp_form_eq_fine {R : ℕ} (G : Garden (2 * R)) (P : WTParams) (hL : 0 < P.L)
    (hC₁ : 0 < P.C₁) (hδ : 0 < P.δ) (hinges : ℕ) :
    P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + hinges) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) =
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + hinges)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  have hpos : 0 < P.C₁ * P.δ ^ (-10 * P.ν) := mul_pos hC₁ (Real.rpow_pos_of_pos hδ _)
  have hlog : Real.log (P.C₁ * P.δ ^ (-10 * P.ν)) = Real.log P.C₁ - 10 * P.ν * Real.log P.δ := by
    rw [Real.log_mul hC₁.ne' (Real.rpow_pos_of_pos hδ _).ne', Real.log_rpow hδ]; ring
  have h1 : Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ)) =
      (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order := by
    rw [Real.exp_nat_mul, ← hlog, Real.exp_log hpos]
  rw [Real.exp_add, h1, Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hL]
  have : (-P.η ^ 6 * (G.molecule.rho + hinges) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L =
      Real.log P.L * (-P.η ^ 6 * (G.molecule.rho + hinges)) +
        Real.log P.L * (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by ring
  rw [this, Real.exp_add]
  ring

end WaveTurbulence.GammaLow.Famc
