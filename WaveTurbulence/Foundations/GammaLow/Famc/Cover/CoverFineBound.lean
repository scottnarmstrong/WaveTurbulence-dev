/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverAdmissible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverBudget
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverFine
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePrimaryPairTable
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFiniteSupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedKernelFormula
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedAbsoluteSum
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedKernel
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSumIntegral
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.CoverFine
/-! The counting cover assembled: TARGET finalsbest2 (L2078) for the spliced kernel of an actual
choice datum, from `ladderl1old` and `finalcount1` (conditional helper, RULINGS R7). -/
public section
set_option autoImplicit false
-- Ported from main `Spine.CoverFineBound` (sha256 553b7a352fd35d8cbe76edd986506d916f8e0791396f84c0995cfe6c841e308e) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.LGSpine
open scoped Classical

theorem fine_spliced_of_subpro_choices (P : WTParams) (hfam : FamFacts P.γ)
    (hfourier : LadderFourierAt P) (hcount : GammaLow.FinalCount.FinalCountGammaAt P)
    (hL : 2 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (hcap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)) (hb1 : P.L ^ (-P.γ + P.η) ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    (hM : G.molecule.IsMolecule) (hconn : G.molecule.IsConnected)
    (hatoms : G.molecule.atoms.card = G.order) (hbonds : G.molecule.bonds.card + R = 2 * G.order)
    (Cs : SubproChoices P.γ G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hS : SubproConclusionsGamma P.γ G D Cs P.L P.γ P.η base roots) :
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  have hL1 : 1 < P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hC₁0 : 0 < P.C₁ := by linarith
  have hfin := finite_coverIndex hfam G hM D Cs hL0 P.γ P.η hb1 base roots
  letI : Fintype (CoverIndex hfam G hM D Cs P.L P.γ P.η base roots) := Fintype.ofFinite _
  have hcover : ∀ z : GenDecoration G P.d roots 0,
      splicedMomentumAmplitude G D P.L P.γ P.η base z.1 ≠ 0 →
        ∃ j : CoverIndex hfam G hM D Cs P.L P.γ P.η base roots,
          j.choice.Admissible P.L P.γ P.η base (bondIndex G z.1) := by
    intro z hz
    obtain ⟨t, s, hs⟩ := exists_cover_choice_of_subpro_choices hfam G hplain hM D hD Cs hL P.γ P.η
      hcap base roots hS z hz
    exact ⟨⟨⟨t, s⟩, z, hz, hs⟩, hs⟩
  have hbud := norm_splicedKernel_le_choiceScale_budget P hfourier hcount hL1 hδ hC₁ hp hR hRmax
    G hplain hirred hbal hn hnmax D hD hlayer (fun j => j.choice)
    (fun j => hS.hinges) (fun j => coverIndex_geometry_of_subpro_choices hfam G hM hconn hatoms hbonds
      D Cs P.γ P.η base roots hS j) base roots hcover
    (((3 ^ 16 * 17 : ℕ) : ℝ)) (Real.log P.L / Real.log 2 + 2) (by positivity)
    (by have : 0 ≤ Real.log P.L / Real.log 2 :=
          div_nonneg (Real.log_nonneg hL1.le) (Real.log_nonneg (by norm_num))
        linarith) hδ1 ha hb hsmall
  have hw := coverIndex_weight_le_one hfam G hM D Cs hL1.le P.γ P.η hb1 base roots
    (((3 ^ 16 * 17 : ℕ) : ℝ)) le_rfl
  have hpos : 0 ≤ P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + D.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) := by positivity
  rw [← exp_form_eq_fine G P hL0 hC₁0 hδ _]
  refine hbud.trans ?_
  calc _ ≤ (P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + D.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L)) * 1 :=
        mul_le_mul_of_nonneg_left hw hpos
    _ = _ := mul_one _

end WaveTurbulence.GammaLow.Famc
