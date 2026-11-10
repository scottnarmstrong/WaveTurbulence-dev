/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev4
/-! **FINALCOUNT-G3: the case table of the erasure** (R27, research-remtame-i L4).

For `d ≥ 3`, `γ ∈ (0,1)`, `η` small, `L` large, `C₁ ≥ 1`, `δ ≤ 1`: the erasure deviation
`N · L^{-(d-γ)(deg v - c)} (log L)^6` is at most
`L^{-η³} L^{(2γ₀+5η²)(c-1)} L^{-(2γ₀+5η²)(deg v - 2)} L^{-(4η+16η⁶+C₀η⁵)}`, with `N = 1` (pinned; `deg v ∈ {3,4}`,
`1 ≤ c ≤ deg v`) or `N = (⌊2L⌋+1)^d` (unpinned; `deg v = 4`, `c ≤ 2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount


/-- `γ₀ = min(γ, 1 - γ)`. -/
noncomputable def gam0 (γ : ℝ) : ℝ := min γ (1 - γ)

/-- The slope `2γ₀ + 5η²` of `excesseqn2`. -/
noncomputable def eraseA (γ η : ℝ) : ℝ := 2 * gam0 γ + 5 * η ^ 2

theorem rankFactor_le {d : ℕ} {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) {j : ℤ}
    (hj : 0 ≤ j) : rankFactor d L γ δ C₁ j ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) := by
  unfold rankFactor
  have hb : C₁⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
    have h3 : 0 ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hδ.le _
    nlinarith [inv_nonneg.2 (by linarith : (0 : ℝ) ≤ C₁)]
  have hb0 : 0 < C₁⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < δ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
    have : 0 < C₁⁻¹ := inv_pos.2 (by linarith)
    positivity
  have : (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ j ≤ 1 := zpow_le_one₀ hb0 hb hj
  calc L ^ (-((d : ℝ) - γ) * (j : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ j ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hL.le _)
    _ = _ := mul_one _



end WaveTurbulence.FinalCountG3
