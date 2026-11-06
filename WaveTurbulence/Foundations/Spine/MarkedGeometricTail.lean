/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GeometricTail
/-! Retain a small-delta power while a separate geometric factor absorbs the large-L tail. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem marked_geometric_tail_le {r δ L B H : ℝ}
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hL : 0 < L) (hH : 0 ≤ H) (hHL : H ≤ L)
    (hsmall : r ≤ Real.sqrt δ * Real.exp (-1)) (n : ℕ)
    (hn : (B + 1) * Real.log L ≤ (n : ℝ)) :
    H * r ^ n ≤ δ ^ ((n : ℝ) / 2) * L ^ (-B) := by
  have hpow := pow_le_pow_left₀ hr hsmall n
  have htail := geometric_tail_le_rpow (le_of_lt (Real.exp_pos (-1))) le_rfl hL n hn
  have hsqrt : Real.sqrt δ ^ n = δ ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ]
    congr 1
    ring
  calc
    _ ≤ H * (Real.sqrt δ * Real.exp (-1)) ^ n := mul_le_mul_of_nonneg_left hpow hH
    _ = δ ^ ((n : ℝ) / 2) * (H * Real.exp (-1) ^ n) := by rw [mul_pow, hsqrt]; ring
    _ ≤ δ ^ ((n : ℝ) / 2) * (L * L ^ (-(B + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hHL htail (by positivity) hL.le) (Real.rpow_nonneg hδ _)
    _ = _ := by
      have he : L * L ^ (-(B + 1)) = L ^ (-B) := by
        calc
          _ = L ^ (1 : ℝ) * L ^ (-(B + 1)) := by rw [Real.rpow_one]
          _ = L ^ ((1 : ℝ) + -(B + 1)) := (Real.rpow_add hL _ _).symm
          _ = _ := by congr 1; ring
      rw [he]

end WaveTurbulence.LGSpine
