/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompactFourier

/-! # Compact support from coordinate bounds in finite-dimensional momentum space -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- A coordinate box is contained in an explicit Euclidean ball. -/
theorem norm_le_of_coordinate_box {ι : Type*} [Fintype ι]
    {x : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 ≤ R) (hx : ∀ i, |x i| ≤ R) :
    ‖x‖ ≤ (Fintype.card ι : ℝ)*R^2+1 := by
  have hs : ‖x‖^2 ≤ (Fintype.card ι : ℝ)*R^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : ι, R^2 := sum_le_sum (fun i hi => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i)) hR).mpr (hx i))
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hC : 0 ≤ (Fintype.card ι : ℝ)*R^2 := by positivity
  nlinarith only [hs, hC, norm_nonneg x, sq_nonneg ((Fintype.card ι : ℝ)*R^2)]

/-- A joint cutoff supported in a fixed coordinate box has compact support. -/
theorem hasCompactSupport_of_coordinate_box {ι : Type*} [Fintype ι]
    (χ : EuclideanSpace ℝ ι → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ R) : HasCompactSupport χ := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ ι)
    ((Fintype.card ι : ℝ)*R^2+1))
  intro x hx
  by_contra hh
  exact hx (by simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_of_coordinate_box hR (hbox x hh))

end WaveTurbulence.WeylSums
