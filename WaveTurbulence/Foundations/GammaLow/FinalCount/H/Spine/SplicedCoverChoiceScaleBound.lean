/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedCoverChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedFilteredChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedSelectedKernel
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SplicedCoverChoiceScaleBound`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Counting estimates on a finite admissible cover assemble without any disjoint-bin premise. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset

theorem norm_splicedKernel_le_choiceScale_budget (P : WTParams)
    (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (hL : 1 < P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    {J : Type*} [Fintype J] (C : J → Src.CountingChoices Src.γL G P.d)
    (hhinges : ∀ j, D.hinges = (C j).subpro.hinges)
    (hgeom : ∀ j, Src.CountingGeometry G (C j)) (base : Mom P.d)
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

end WaveTurbulence.GammaLow.FinalCount.H
