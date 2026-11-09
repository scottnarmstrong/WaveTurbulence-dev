/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SpliceGateMonotone`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Large-constant monotonicity of the molecular source gates, so that they combine with the other
spine inputs through `prefix_and`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct

private theorem premises_of_largeConstants {P : WTParams} {c₁ c₂ : ℝ} {R : ℕ} {G : Garden (2 * R)}
    {D : SplicedKernelData G P.d} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (h : SplicedSourcePremises ({P with C₁ := c₁, C₂ := c₂} : WTParams) G D base roots) :
    SplicedSourcePremises P G D base roots :=
  ⟨h.molecule, h.connected, h.atom_count, h.bond_count, h.subpro⟩

theorem coarseSplicedAt_largeConstantMonotone : LargeConstantMonotone CoarseSplicedAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirr hbal hn hnmax D hD hlayer A base
    roots hsrc
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirr hbal hn hnmax D hD hlayer A base roots
    (premises_of_largeConstants hsrc)
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hδ0 : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ P.L := by linarith
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0 _)
  exact mul_le_mul h₂ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
    (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)

end WaveTurbulence.GammaLow.FinalCount.H
