/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceScalePowers

/-!
# Exact normalization of the two first-pair contributions

The stationary exponent covers case (a), p=1, and case (c), p=1-3 eta.
The physical Weyl-window coefficient K remains fixed when L varies.
This separates coefficient dependence from the strict power reserves.
-/

public section

namespace WaveTurbulence.Sumint

/-- Exact source rescaling of a first-pair stationary/Weyl envelope. -/
theorem first_pair_source_rescale (d : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ η p Cs Cm K : ℝ) :
    (16*sourceHalfScale L γ δ)⁻¹*
      ((16*sourceHalfScale L γ δ)^(-p)*Cs*(4*L)^(2*d)+
        K*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) =
      (Cs*(8:ℝ)^(-(1+p))*δ^(-(1+p))*4^(2*d))*L^(2*(d:ℝ)-2*γ*(1+p))+
      (K*Cm*(8:ℝ)⁻¹*δ⁻¹*4^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))*
        L^(2*(d:ℝ)-2*γ-2*((d:ℝ)-1)*(1-γ)+η) := by
  have hc : 0 < 16*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  have hpow : (16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)^(-p) =
      (16*sourceHalfScale L γ δ)^(-(1+p)) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hc]
    congr 1
    ring
  have hs := source_scale_rpow hL (by norm_num : (0:ℝ) < 16) hδ
    (by norm_num : (0:ℝ) ≤ 4) γ (1+p) (2*d:ℕ)
  have hsn : ((2*d:ℕ):ℝ)-2*γ*(1+p) = 2*(d:ℝ)-2*γ*(1+p) := by push_cast; ring
  simp only [Real.rpow_natCast] at hs
  rw [hsn] at hs
  have hm := source_scale_rpow hL (by norm_num : (0:ℝ) < 16) hδ
    (by norm_num : (0:ℝ) ≤ 4) γ 1 (2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)
  simp only [Real.rpow_neg_one,mul_one] at hm
  have hmn : 2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η-2*γ =
      2*(d:ℝ)-2*γ-2*((d:ℝ)-1)*(1-γ)+η := by ring
  rw [hmn] at hm
  calc
    _ = Cs*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)^(-p))*(4*L)^(2*d)+
      K*Cm*((16*sourceHalfScale L γ δ)⁻¹*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by ring
    _ = Cs*((16*sourceHalfScale L γ δ)^(-(1+p))*(4*L)^(2*d))+
      K*Cm*((16*sourceHalfScale L γ δ)⁻¹*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by rw [hpow]; ring
    _ = _ := by rw [hs,hm]; norm_num; ring

/-- The Weyl-window coefficient in case (c) is independent of L after source rescaling. -/
theorem source_fractional_window_ratio {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ T : ℝ) :
    T*(4*L)^(2*γ)/(16*sourceHalfScale L γ δ) = T*4^(2*γ)/(8*δ) := by
  have hp : L^(2*γ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hL.le]
  unfold sourceHalfScale
  field_simp
  ring

end WaveTurbulence.Sumint
