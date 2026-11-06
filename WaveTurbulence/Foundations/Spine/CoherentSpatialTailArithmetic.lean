/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentTailArithmetic
/-! Coherent tail arithmetic with the high-order cost outside the order-dependent powers. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem coherent_spatial_absolute_le_geometric {M C δ L a D U : ℝ} (n k : ℕ)
    (hM : 0 ≤ M) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hU : 0 ≤ U) (hn : 1 ≤ n) :
    M ^ n * ((C * (C * δ) ^ n * L ^ (-a) +
      2 ^ n * δ ^ n * (C * C ^ n) ^ 2) * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k))) ≤
    (D * C * U ^ k) * ((C + C ^ 2) * ((M * 8 * C ^ 2) * (2 * C ^ 2 * δ))) ^ n := by
  have he : M ^ n * ((C * (C * δ) ^ n * L ^ (-a) +
      2 ^ n * δ ^ n * (C * C ^ n) ^ 2) * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k))) =
      (D * C * U ^ k) * ((M * 8 * C ^ 2) ^ n *
        (C * (C * δ) ^ n * L ^ (-a) + 2 ^ n * δ ^ n * (C * C ^ n) ^ 2)) := by
    simp only [mul_pow, pow_add, pow_mul, pow_one]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (coherent_absolute_le_geometric (M * 8 * C ^ 2) C δ L a n (by positivity) hC hδ hL ha hn)
    (by positivity)

end WaveTurbulence.LGSpine
