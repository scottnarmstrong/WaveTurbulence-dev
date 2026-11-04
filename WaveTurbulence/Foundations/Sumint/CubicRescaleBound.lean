/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceScalePowers

/-!
# The two cubic contributions after exact source rescaling

The stationary term has power 3d-4γ. The Weyl term has power
3d-3γ-2γ₀ and one logarithm. All fixed mesh constants are collected before
δ is chosen; the interval-length bound is three.
-/

public section

namespace WaveTurbulence.Sumint

/-- A fixed constant collecting the width-four mesh and bounded interval length. -/
@[expose] noncomputable def cubicRescaleConstant (d : ℕ) (γ Cs Cm : ℝ) : ℝ :=
  1+3*Cs*(((16:ℝ)/2)^(-2:ℝ))*4^(3*d)+
    9*Cm*(((16:ℝ)/2)^(-2:ℝ))*4^(3*(d:ℝ)+γ-2*min γ (1-γ))

/-- The explicit rescaling constant is at least one. -/
theorem one_le_cubicRescaleConstant (d : ℕ) (γ : ℝ) {Cs Cm : ℝ}
    (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) : 1 ≤ cubicRescaleConstant d γ Cs Cm := by
  have hA : 0 ≤ 3*Cs*(((16:ℝ)/2)^(-2:ℝ))*4^(3*d) := by positivity
  have hB : 0 ≤ 9*Cm*(((16:ℝ)/2)^(-2:ℝ))*4^(3*(d:ℝ)+γ-2*min γ (1-γ)) := by positivity
  unfold cubicRescaleConstant
  linarith only [hA,hB]

/-- Both cubic source powers are retained with a constant independent of δ. -/
theorem cubic_source_rescale_le (d : ℕ) (γ : ℝ) {Cs Cm L δ len : ℝ}
    (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hL : 2 ≤ L) (hδ : 0 < δ) (hlen : len ≤ 3) :
    len*(16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
      (Cs*(4*L)^(3*d)+Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L)) ≤
    cubicRescaleConstant d γ Cs Cm * δ^(-2:ℝ) *
      (L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L) := by
  have hLp : 0 < L := by linarith only [hL]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL])
  have hlog4 : 0 ≤ Real.log (4*L) := Real.log_nonneg (by linarith only [hL])
  have hlogBound : Real.log (4*L) ≤ 3*Real.log L := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hLp.ne']
    have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hL
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
      norm_num
    rw [he]
    linarith only [h2]
  let κ := ((16:ℝ)/2)^(-2:ℝ)
  let A := 3*Cs*κ*4^(3*d)
  let B := 9*Cm*κ*4^(3*(d:ℝ)+γ-2*min γ (1-γ))
  have hA : 0 ≤ A := by dsimp [A,κ]; positivity
  have hB : 0 ≤ B := by dsimp [B,κ]; positivity
  have hAK : A ≤ cubicRescaleConstant d γ Cs Cm := by
    change A ≤ 1+A+B
    linarith only [hB]
  have hBK : B ≤ cubicRescaleConstant d γ Cs Cm := by
    change B ≤ 1+A+B
    linarith only [hA]
  have hs := source_scale_inv_sq_mul_nat_pow hLp (by norm_num : (0:ℝ) < 16) hδ
    (by norm_num : (0:ℝ) ≤ 4) γ (3*d)
  have hm := source_scale_inv_sq_mul_rpow hLp (by norm_num : (0:ℝ) < 16) hδ
    (by norm_num : (0:ℝ) ≤ 4) γ (3*(d:ℝ)+γ-2*min γ (1-γ))
  have hexp : ((3*d:ℕ):ℝ)-4*γ = 3*(d:ℝ)-4*γ := by push_cast; ring
  have hexp' : 3*(d:ℝ)+γ-2*min γ (1-γ)-4*γ = 3*(d:ℝ)-3*γ-2*min γ (1-γ) := by ring
  rw [hexp] at hs
  rw [hexp'] at hm
  have hscale : 0 < sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  let T := (16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
    (Cs*(4*L)^(3*d)+Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  calc
    _ = len*T := by dsimp [T]; ring
    _ ≤ 3*T := mul_le_mul_of_nonneg_right hlen hT
    _ = δ^(-2:ℝ)*(A*L^(3*(d:ℝ)-4*γ)+
        (3*Cm*κ*4^(3*(d:ℝ)+γ-2*min γ (1-γ)))*
          L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log (4*L)) := by
      dsimp [T,A,κ]
      have he (X Y q : ℝ) :
          3*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*(Cs*X+Cm*Y*q)) =
          3*Cs*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*X)+
            3*Cm*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*Y)*q := by ring
      rw [he,hs,hm]
      ring
    _ ≤ δ^(-2:ℝ)*(A*L^(3*(d:ℝ)-4*γ)+B*L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
      apply add_le_add le_rfl
      have hW : 0 ≤ (3*Cm*κ*4^(3*(d:ℝ)+γ-2*min γ (1-γ)))*
          L^(3*(d:ℝ)-3*γ-2*min γ (1-γ)) := by dsimp [κ]; positivity
      exact (mul_le_mul_of_nonneg_left hlogBound hW).trans_eq (by dsimp [B]; ring)
    _ ≤ δ^(-2:ℝ)*(cubicRescaleConstant d γ Cs Cm*L^(3*(d:ℝ)-4*γ)+
        cubicRescaleConstant d γ Cs Cm*(L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg hLp.le (3*(d:ℝ)-4*γ))
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hBK
          (mul_nonneg (Real.rpow_nonneg hLp.le (3*(d:ℝ)-3*γ-2*min γ (1-γ))) hlog)
    _ = _ := by ring

end WaveTurbulence.Sumint
