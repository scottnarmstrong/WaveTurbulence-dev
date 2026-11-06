/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LayergardenAssembly
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt
/-! Large-constant monotonicity of the molecular source gates, so that they combine with the other
spine inputs through `prefix_and`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
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

theorem ofReal_mul_mono_any {c c' pr : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    ENNReal.ofReal (c * pr) ≤ ENNReal.ofReal (c' * pr) := by
  by_cases hpr : 0 ≤ pr
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcc hpr)
  · have h1 : c * pr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
    have h2 : c' * pr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc.trans hcc) (by linarith)
    rw [ENNReal.ofReal_of_nonpos h1, ENNReal.ofReal_of_nonpos h2]

theorem ladderFourierAt_largeConstantMonotone : LargeConstantMonotone LadderFourierAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirr hbal hn hnmax D scales hlayer hD
    base roots
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirr hbal hn hnmax D scales hlayer hD base roots
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  apply ofReal_mul_mono_any (by
    have := Real.rpow_nonneg hL0 (P.δ ^ (5 * P.ν) * (G.molecule.rho : ℝ))
    positivity)
  have hδ0 : 0 ≤ P.δ ^ (-1 / 2 - 5 * P.ν) := Real.rpow_nonneg hδ.le _
  have hpow := Real.rpow_nonneg hL0 (P.δ ^ (5 * P.ν) * (G.molecule.rho : ℝ))
  apply mul_le_mul_of_nonneg_right _ hpow
  exact mul_le_mul h₁ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
    (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)

end WaveTurbulence.LGSpine
