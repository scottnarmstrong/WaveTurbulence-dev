/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EnumerationSum
/-! The incoherent sum starts at g=1, retaining one full power of the incoherency gain. -/
public section
namespace WaveTurbulence.LGSpine
open Finset

theorem sum_positive_powers_eq (r : ℝ) (n : ℕ) :
    (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), r ^ g) =
      r * ∑ g ∈ range n, r ^ g := by
  rw [sum_filter, sum_range_succ']
  simp [pow_succ', mul_sum]

theorem sum_positive_powers_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (n : ℕ) :
    (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), r ^ g) ≤ 2 * r := by
  rw [sum_positive_powers_eq]
  exact (mul_le_mul_of_nonneg_left (sum_powers_le_two hr0 hr n) hr0).trans_eq (mul_comm _ _)

end WaveTurbulence.LGSpine
