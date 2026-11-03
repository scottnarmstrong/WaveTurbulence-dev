/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.GrowthProfiles
public import WaveTurbulence.Foundations.CountLemmas.StarMonomials

/-! # Eventual scale conditions for the high-γ pair proof -/

public section
open Filter
namespace WaveTurbulence.CountLemmas

/-- The density threshold and radius are chosen independently of δ. Its
fixed value is absorbed only in the eventual lower bound on L. -/
theorem eventually_high_pair_scales (n : ℕ) {δ γ ε : ℝ} (hδ : 0 < δ)
    (hγ : (1 : ℝ)/2 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεgap : ε < 2-2*γ) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ 1 ≤ L*L^(-ε) ∧ 1 ≤ L^ε ∧
      16*((3 : ℝ)^(n+1)*L^ε) ≤ (δ⁻¹*L^(-2*γ))*L^2 ∧
      (δ⁻¹*L^(-2*γ))*L^2 ≤ L := by
  have hscale := eventually_scaled_power_le hεgap
    (by positivity : 0 ≤ 16*(3 : ℝ)^(n+1)) (inv_pos.mpr hδ)
  have hupper := eventually_scaled_power_le (by linarith only [hγ] : 2-2*γ < 1)
    (inv_nonneg.mpr hδ.le) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hscale,hupper,eventually_ge_atTop (1 : ℝ)] with L hs hu hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hW : (δ⁻¹*L^(-2*γ))*L^2 = δ⁻¹*L^(2-2*γ) := by
    simpa only [Real.rpow_two] using bandwidth_mul_rpow hLp δ γ 2
  have hR : L*L^(-ε) = L^(1-ε) := by
    calc
      _ = L^(1 : ℝ)*L^(-ε) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1
  refine ⟨hL,?_,Real.one_le_rpow hL hε.le,?_,?_⟩
  · rw [hR]
    exact Real.one_le_rpow hL (by linarith only [hε1])
  · rw [hW]
    convert hs using 1; ring
  · rw [hW]
    simpa only [one_mul,Real.rpow_one] using hu

end WaveTurbulence.CountLemmas
