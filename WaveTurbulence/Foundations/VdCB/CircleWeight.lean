/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLatticeRegularity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The circle dual curvature weight

The square root of the dual curvature is positive and decreasing on the
positive frequency axis. Its dyadic size is `sqrt(R)*h*Y^(-3/2)`.
-/

public section

open Set

namespace WaveTurbulence.VdCB

/-- Explicit positive stationary weight for the circle dual. -/
@[expose] noncomputable def circleDualWeight (R h ν : ℝ) : ℝ :=
  Real.sqrt R * h * (h ^ 2 + ν ^ 2) ^ (-(3 / 4) : ℝ)

theorem hasDerivAt_circleDualWeight (R : ℝ) {h : ℝ} (hh : 0 < h) (ν : ℝ) :
    HasDerivAt (circleDualWeight R h)
      ((-(3 / 2) : ℝ) * Real.sqrt R * h * ν * (h ^ 2 + ν ^ 2) ^ (-(7 / 4) : ℝ)) ν := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  have hd : HasDerivAt (fun x : ℝ => h ^ 2 + x ^ 2) (2 * ν) ν := by
    convert (hasDerivAt_const ν (h ^ 2)).add ((hasDerivAt_id ν).pow 2) using 1
    · funext x
      rfl
    · norm_num
  have hp := (hd.rpow_const (p := -(3 / 4 : ℝ)) (Or.inl hD.ne')).const_mul (Real.sqrt R * h)
  convert hp using 1
  · funext x
    rfl
  · simp only [show -(3 / 4 : ℝ) - 1 = -(7 / 4) by norm_num]
    ring

/-- The actual circle stationary weight is decreasing on positive frequencies. -/
theorem antitoneOn_circleDualWeight {R h : ℝ} (hh : 0 < h) :
    AntitoneOn (circleDualWeight R h) (Ici 0) := by
  have hd : Differentiable ℝ (circleDualWeight R h) :=
    fun x => (hasDerivAt_circleDualWeight R hh x).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hd.continuous.continuousOn hd.differentiableOn
  intro x hx
  rw [(hasDerivAt_circleDualWeight R hh x).deriv]
  have hx0 : 0 ≤ x := (interior_subset hx : x ∈ Ici 0)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-(3 / 2) : ℝ) ≤ 0) (Real.sqrt_nonneg R)) hh.le |>
        fun hmul => mul_nonpos_of_nonpos_of_nonneg hmul hx0)
    (Real.rpow_nonneg (by positivity) _)

/-- Uniform dyadic size of the stationary curvature weight. -/
theorem circleDualWeight_le {R h Y ν : ℝ} (hh : 0 < h) (hY : 0 < Y) (hν : Y ≤ ν) :
    circleDualWeight R h ν ≤ Real.sqrt R * h * Y ^ (-(3 / 2) : ℝ) := by
  have hD : Y ^ 2 ≤ h ^ 2 + ν ^ 2 := by nlinarith only [hν, hY.le, sq_nonneg h]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hY) hD (by norm_num : (-(3 / 4) : ℝ) ≤ 0)
  have heq : (Y ^ 2) ^ (-(3 / 4) : ℝ) = Y ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hY.le]
    norm_num
  rw [heq] at hp
  exact mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.sqrt_nonneg R) hh.le)

end WaveTurbulence.VdCB
