/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedChoiceScaleAbsorption
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedCircuitRank
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredCountA
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredGates
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFilteredRawBound
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencyCount
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedFrequencySupport
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedAbsoluteSum
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedSelectedKernel
public import WaveTurbulence.Foundations.Spine.SplicedFilteredRawBound
public import WaveTurbulence.Foundations.Spine.SplicedChoiceScaleAbsorption
/-! Counting half of finalsbest2 on every canonical refined counting piece. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SplicedFilteredChoiceScaleBound` (sha256 9cd927872afcaf12ff92379968ed9b1a19b07246b0dc61d69ff0ea5bde9d4905) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset

theorem norm_spliced_filtered_with_choiceScale_le (P : WTParams)
    (hfourier : LadderFourierAt P) (hcount : GammaLow.FinalCount.FinalCountGammaAt P)
    (hL : 1 < P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    (C : CountingChoices P.γ G P.d) (hhinges : D.hinges = C.subpro.hinges)
    (hgeom : CountingGeometry G C) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (s : Set (GenDecoration G P.d roots 0))
    (hs : s ⊆ splicedSelectedCarrier G D C P.L P.γ P.η base roots)
    (C₀ scaleCost : ℝ) (hC₀ : 0 < C₀) (hscale : 0 < scaleCost) (hδ1 : P.δ ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log scaleCost ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log C₀ + 5 * P.ν * Real.log P.δ ≤ 0) :
    ‖splicedFilteredKernel G D P.L P.γ P.η P.δ base roots s‖ * C₀ ^ G.order *
      scaleCost ^ (G.molecule.rho + C.numCriticalSG) ≤
      P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) := by
  have hh := norm_spliced_filtered_bound_of_source_gates P hfourier hcount (zero_lt_one.trans hL) hδ
    (zero_lt_one.trans_le hC₁) hp hR hRmax G hplain hirred hbal hn hnmax D hD hlayer C hhinges hgeom base roots s hs
  change ‖splicedFilteredKernel G D P.L P.γ P.η P.δ base roots s‖ ≤
    splicedRawPrefactor G C P.L P.γ P.η P.δ P.C₁ P.ν at hh
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity))
    (pow_nonneg hscale.le _)).trans
  exact splicedRawPrefactor_mul_choiceScale_le G C hgeom hn hR hL hδ hδ1 hC₁ hC₀ hscale ha hb hsmall P.γ

end WaveTurbulence.GammaLow.Famc
