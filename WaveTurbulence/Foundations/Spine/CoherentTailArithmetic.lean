/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GeometricTail
public import WaveTurbulence.Foundations.Spine.StageOrderLower
/-! Scalar absorption of the explicit coherent absolute bound at high orders. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem coherent_absolute_le_geometric (A C δ L a : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (ha : 0 ≤ a) (hn : 1 ≤ n) :
    A ^ n * (C * (C * δ) ^ n * L ^ (-a) +
      2 ^ n * δ ^ n * (C * C ^ n) ^ 2) ≤
      ((C + C ^ 2) * (A * (2 * C ^ 2 * δ))) ^ n := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hr0 : 0 ≤ 2 * C ^ 2 * δ := by positivity
  have hsmall : C * δ ≤ 2 * C ^ 2 * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    nlinarith
  have hLpow : L ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr ha)
  have hfirst : C * (C * δ) ^ n * L ^ (-a) ≤ C * (2 * C ^ 2 * δ) ^ n := by
    apply (mul_le_of_le_one_right (by positivity) hLpow).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hC0 hδ) hsmall n) hC0
  have hsecond : 2 ^ n * δ ^ n * (C * C ^ n) ^ 2 =
      C ^ 2 * (2 * C ^ 2 * δ) ^ n := by
    simp only [mul_pow, ← pow_mul]
    ring
  have hsum : C * (C * δ) ^ n * L ^ (-a) + 2 ^ n * δ ^ n * (C * C ^ n) ^ 2 ≤
      (C + C ^ 2) * (2 * C ^ 2 * δ) ^ n := by
    rw [hsecond]
    nlinarith
  calc
    _ ≤ A ^ n * ((C + C ^ 2) * (2 * C ^ 2 * δ) ^ n) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hA n)
    _ = (C + C ^ 2) * (A * (2 * C ^ 2 * δ)) ^ n := by rw [mul_pow]; ring
    _ ≤ (C + C ^ 2) ^ n * (A * (2 * C ^ 2 * δ)) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg hA hr0) n)
      exact le_self_pow₀ (by nlinarith) (by omega)
    _ = _ := (mul_pow _ _ _).symm

end WaveTurbulence.LGSpine
