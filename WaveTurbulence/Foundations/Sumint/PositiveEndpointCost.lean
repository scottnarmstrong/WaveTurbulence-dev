/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFiniteKernelPositive

/-!
# Numerical finite-output cost at the positive Fourier endpoint

A polynomial factor in the number M of source inputs is absorbed by a
constant to power M. The finite output count adds 4d to the 9d trace
loss, fitting strictly within the reserved 14d positive-endpoint loss.
-/

public section
namespace WaveTurbulence.Sumint

/-- One scalar coefficient and the input-count factor fit a constant to the literal input count. -/
theorem coefficient_mul_count_pow_le {C G : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G)
    {m : ℕ} (hm : 0 < m) : C*(m:ℝ)*G^m ≤ (2*C*G)^m := by
  have hn : (m:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast (show m < 2^m from Nat.lt_two_pow_self).le
  have hc : C ≤ C^m := by simpa only [pow_one] using pow_le_pow_right₀ hC (Nat.succ_le_iff.mpr hm)
  calc
    _ ≤ C^m*2^m*G^m := mul_le_mul_of_nonneg_right
      (mul_le_mul hc hn (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hC) _)) (pow_nonneg hG _)
    _ = _ := by rw [mul_pow,mul_pow]; ring

/-- The finite output cardinality and eight-input trace counting loss fit the reserved positive endpoint power. -/
theorem finite_positive_endpoint_cost_le {d m : ℕ} {C G L δ v E : ℝ}
    (hC : 1 ≤ C) (hG : 1 ≤ G) (hL : 1 ≤ L) (hδ : 0 < δ) (hm : 0 < m)
    (hv : v ≤ (3*L)^(4*d)) :
    C*(2*(m:ℝ)*v)*(3*L^(9*(d:ℝ))*(G^m*δ^(-(m:ℝ)/2)*L^E)) ≤
      (12*C*3^(4*d)*G)^m*δ^(-(m:ℝ)/2)*L^(E+14*(d:ℝ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hCn : 0 ≤ C := zero_le_one.trans hC
  have hGn : 0 ≤ G := zero_le_one.trans hG
  have hQ : (1:ℝ) ≤ (3:ℝ)^(4*d) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)
  have hC' : 1 ≤ 6*C*3^(4*d) := by nlinarith only [hC,hQ]
  have hcoef := coefficient_mul_count_pow_le hC' hGn hm
  have hpoly : v*L^(9*(d:ℝ)) ≤ 3^(4*d)*L^(13*(d:ℝ)) := by
    calc
      _ ≤ (3*L)^(4*d)*L^(9*(d:ℝ)) := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        rw [mul_pow,← Real.rpow_natCast L, mul_assoc,← Real.rpow_add hLp]
        congr 2
        push_cast
        ring
  have hscale : L^(13*(d:ℝ))*L^E ≤ L^(E+14*(d:ℝ)) := by
    rw [← Real.rpow_add hLp]
    apply Real.rpow_le_rpow_of_exponent_le hL
    have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
    linarith only [hd0]
  calc
    _ = (6*C*(m:ℝ)*G^m)*δ^(-(m:ℝ)/2)*(v*L^(9*(d:ℝ)))*L^E := by ring
    _ ≤ (6*C*(m:ℝ)*G^m)*δ^(-(m:ℝ)/2)*(3^(4*d)*L^(13*(d:ℝ)))*L^E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) (Real.rpow_nonneg hLp.le _)
    _ = ((6*C*3^(4*d))*(m:ℝ)*G^m)*δ^(-(m:ℝ)/2)*(L^(13*(d:ℝ))*L^E) := by ring
    _ ≤ (2*(6*C*3^(4*d))*G)^m*δ^(-(m:ℝ)/2)*(L^(13*(d:ℝ))*L^E) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hδ.le _)) (by positivity)
    _ ≤ (2*(6*C*3^(4*d))*G)^m*δ^(-(m:ℝ)/2)*L^(E+14*(d:ℝ)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by congr 3; ring

end WaveTurbulence.Sumint
