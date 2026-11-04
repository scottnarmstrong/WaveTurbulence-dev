/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.StrictPowerAbsorption
public import WaveTurbulence.Foundations.Sumint.ExponentMargins

/-!
# The high-gamma normal block uses the F23 linear bound

For gamma greater than one half, pairing the normal factor with the second
linear estimate leaves the strict reserves 2 gamma - 1 and 1 - gamma.
A later lattice threshold absorbs every fixed coefficient, including the
extra reciprocal delta from F23. This is numerical bookkeeping, not a
replacement for the source factor estimates.
-/

public section

namespace WaveTurbulence.Sumint

/-- The two strict reserves in a high-gamma normal block. -/
theorem high_gamma_normal_reserves {γ : ℝ} (hγ : γ ∈ Set.Ioo (1/2:ℝ) 1) :
    0 < min (2*γ-1) (1-γ) ∧ gammaBase γ = 1-γ := by
  constructor
  · exact lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
  · exact min_eq_right (by linarith [hγ.1])

/-- In the low-gamma branch the stationary contribution is exactly at the normal-block scale. -/
theorem exists_low_gamma_normal_block_power_bound (d : ℕ) {γ : ℝ}
    (hγ : γ ∈ Set.Ioc (0:ℝ) (1/2)) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      L^(d:ℝ)*(L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*gammaBase γ)*Real.log L) ≤
      2*L^(4*((d:ℝ)-γ)) := by
  have hg : gammaBase γ = γ := min_eq_left (by linarith [hγ.2])
  have hgap : 4*(d:ℝ)-3*γ-2*gammaBase γ < 4*((d:ℝ)-γ) := by rw [hg]; linarith [hγ.1]
  obtain ⟨R,hR,hbound⟩ := exists_coefficient_log_power_le 1
    (4*(d:ℝ)-3*γ-2*gammaBase γ) (4*((d:ℝ)-γ)) hgap
  refine ⟨R,hR,?_⟩
  intro L hL
  have hLp : 0 < L := by linarith [hR.trans hL]
  have he₀ : L^(d:ℝ)*L^(3*(d:ℝ)-4*γ) = L^(4*((d:ℝ)-γ)) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have he₁ : L^(d:ℝ)*L^(3*(d:ℝ)-3*γ-2*gammaBase γ) = L^(4*(d:ℝ)-3*γ-2*gammaBase γ) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  rw [mul_add,← mul_assoc,he₀,he₁]
  have hb := hbound L hL
  simp only [one_mul] at hb
  linarith only [hb]

/-- The extra delta loss in the F23 branch is paid by a strict normal-block reserve. -/
theorem exists_high_gamma_normal_block_power_bound (d : ℕ) {γ : ℝ}
    (hγ : γ ∈ Set.Ioo (1/2:ℝ) 1) (K δ ε : ℝ)
    (hδ : 0 < δ) (hε : ε < min (2*γ-1) (1-γ)) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      K*δ^(-3:ℝ)*L^((d:ℝ)+1-2*γ)*
        (L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*gammaBase γ)*Real.log L) ≤
      δ^(-2:ℝ)*L^(4*((d:ℝ)-γ)-ε) := by
  have hg := (high_gamma_normal_reserves hγ).2
  have h₀ : 4*(d:ℝ)+1-6*γ < 4*((d:ℝ)-γ)-ε := by
    linarith [hε.trans_le (min_le_left _ _)]
  have h₁ : 4*(d:ℝ)+1-5*γ-2*gammaBase γ < 4*((d:ℝ)-γ)-ε := by
    rw [hg]
    linarith [hε.trans_le (min_le_right _ _)]
  obtain ⟨R,hR,hbound⟩ := exists_three_power_sum_le (K*δ⁻¹) 0 (K*δ⁻¹)
    (4*(d:ℝ)+1-6*γ) (4*(d:ℝ)+1-6*γ)
    (4*(d:ℝ)+1-5*γ-2*gammaBase γ) (4*((d:ℝ)-γ)-ε) h₀ h₀ h₁
  refine ⟨R,hR,?_⟩
  intro L hL
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hpow : δ^(-3:ℝ) = δ^(-2:ℝ)*δ⁻¹ := by
    rw [← Real.rpow_neg_one δ,← Real.rpow_add hδ]
    norm_num
  have he₀ : L^((d:ℝ)+1-2*γ)*L^(3*(d:ℝ)-4*γ) = L^(4*(d:ℝ)+1-6*γ) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have he₁ : L^((d:ℝ)+1-2*γ)*L^(3*(d:ℝ)-3*γ-2*gammaBase γ) =
      L^(4*(d:ℝ)+1-5*γ-2*gammaBase γ) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  calc
    _ = δ^(-2:ℝ)*((K*δ⁻¹)*L^(4*(d:ℝ)+1-6*γ)+
        (K*δ⁻¹)*L^(4*(d:ℝ)+1-5*γ-2*gammaBase γ)*Real.log L) := by
      rw [hpow,mul_add]
      calc
        _ = δ^(-2:ℝ)*((K*δ⁻¹)*(L^((d:ℝ)+1-2*γ)*L^(3*(d:ℝ)-4*γ))+
          (K*δ⁻¹)*(L^((d:ℝ)+1-2*γ)*L^(3*(d:ℝ)-3*γ-2*gammaBase γ))*Real.log L) := by ring
        _ = _ := by rw [he₀,he₁]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [zero_mul,add_zero] using hbound L hL)
      (Real.rpow_nonneg hδ.le _)

end WaveTurbulence.Sumint
