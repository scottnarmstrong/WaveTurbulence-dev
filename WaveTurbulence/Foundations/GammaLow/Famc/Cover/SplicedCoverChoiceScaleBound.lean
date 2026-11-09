/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedChoiceScaleAbsorption
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedCircuitRank
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
public import WaveTurbulence.Foundations.Spine.SplicedFilteredChoiceScaleBound
public import WaveTurbulence.Foundations.Spine.SplicedFilteredPartition
public import WaveTurbulence.Foundations.Spine.FiniteCoverRefinement
public import WaveTurbulence.Foundations.Spine.FiniteWeightedSumBound
/-! Counting estimates on a finite admissible cover assemble without any disjoint-bin premise. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedCoverChoiceScaleBound` (sha256 ff2af0607ee17ae3196df249bf264c8fafc3369b140605ccf36d005f7f9b35c4) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset

theorem norm_splicedKernel_le_choiceScale_budget (P : WTParams)
    (hfourier : LadderFourierAt P) (hcount : GammaLow.FinalCount.FinalCountGammaAt P)
    (hL : 1 < P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    {J : Type} [Fintype J] (C : J → CountingChoices P.γ G P.d)
    (hhinges : ∀ j, D.hinges = (C j).subpro.hinges)
    (hgeom : ∀ j, CountingGeometry G (C j)) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hcover : ∀ z : GenDecoration G P.d roots 0,
      splicedMomentumAmplitude G D P.L P.γ P.η base z.1 ≠ 0 →
        ∃ j, (C j).Admissible P.L P.γ P.η base (bondIndex G z.1))
    (C₀ scaleCost : ℝ) (hC₀ : 0 < C₀) (hscale : 0 < scaleCost) (hδ1 : P.δ ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log scaleCost ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log C₀ + 5 * P.ν * Real.log P.δ ≤ 0) :
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      (P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + D.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L)) *
      ∑ j, (C₀ ^ G.order * scaleCost ^ (G.molecule.rho + (C j).numCriticalSG))⁻¹ := by
  obtain ⟨s, hsub, hpart⟩ := exists_unique_cover_refinement
    {z : GenDecoration G P.d roots 0 | splicedMomentumAmplitude G D P.L P.γ P.η base z.1 ≠ 0}
    (fun j => splicedSelectedCarrier G D (C j) P.L P.γ P.η base roots) (by
      intro z hz
      obtain ⟨j, hj⟩ := hcover z hz
      exact ⟨j, hz, hj⟩)
  rw [splicedKernel_eq_sum_filtered G hplain D hD (zero_lt_one.trans hL) P.γ P.η P.δ base roots s hpart]
  apply norm_sum_le_of_weighted_bounds
    (fun j => splicedFilteredKernel G D P.L P.γ P.η P.δ base roots (s j))
    (fun j => C₀ ^ G.order * scaleCost ^ (G.molecule.rho + (C j).numCriticalSG))
  · intro j
    exact mul_pos (pow_pos hC₀ _) (pow_pos hscale _)
  · intro j
    have h := norm_spliced_filtered_with_choiceScale_le P hfourier hcount hL hδ hC₁ hp hR hRmax
      G hplain hirred hbal hn hnmax D hD hlayer (C j) (hhinges j) (hgeom j) base roots
      (s j) (hsub j) C₀ scaleCost hC₀ hscale hδ1 ha hb hsmall
    rw [← hhinges j] at h
    simpa only [mul_assoc] using h

end WaveTurbulence.GammaLow.Famc
