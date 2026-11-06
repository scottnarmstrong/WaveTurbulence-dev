/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentPrefactorAlgebra
/-! Small delta absorbs only low-norm exponential costs; the fixed high cost is paid at large L. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

 theorem coherent_spatial_prefactor_absorbed {M C δ D U a ε L b : ℝ} (n k : ℕ)
    (hM : 0 ≤ M) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hsmall : 64 * M * C ^ 4 * δ ≤ Real.sqrt δ)
    (hlarge : (2 * D * C ^ 3 * U ^ k) * (a + ε) ≤ L ^ (-b)) :
    M ^ n * (((C * (C * δ) ^ n * a) * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k))) +
      ((2 : ℝ) ^ (2 * n + 1) * (((2 : ℝ) ^ n * δ ^ n * (C * C ^ n) ^ 2) *
        (ε * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k)))))) ≤
      δ ^ ((n : ℝ) / 2) * L ^ (-b) := by
  have hbound := coherent_prefactor_le_common_base n k hM hC hδ hD hU ha hε
  have hpow := pow_le_pow_left₀ (show 0 ≤ 64 * M * C ^ 4 * δ by positivity) hsmall n
  have hsqrt : Real.sqrt δ ^ n = δ ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ]
    congr 1
    ring
  rw [hsqrt] at hpow
  apply hbound.trans
  calc
    _ ≤ (2 * D * C ^ 3 * U ^ k) * δ ^ ((n : ℝ) / 2) * (a + ε) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (add_nonneg ha hε)
    _ = δ ^ ((n : ℝ) / 2) * ((2 * D * C ^ 3 * U ^ k) * (a + ε)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hδ _)

end WaveTurbulence.LGSpine
