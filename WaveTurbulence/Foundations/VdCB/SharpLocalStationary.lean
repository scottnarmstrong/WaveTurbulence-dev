/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.FresnelInterval
public import WaveTurbulence.Foundations.VdCB.LocalStationary

/-!
# Sharp local stationary phase

The actual third derivative controls the cubic comparison error, and the
actual second derivative controls the explicit Fresnel tail. No smooth
amplitude is inserted into the source integral.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Sharp stationary phase on a symmetric neighborhood of an actual
nondegenerate stationary point. The cutoff radius remains free for later
optimization against nonstationary tails. -/
theorem norm_integral_local_stationary_sub_main_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (c : ℝ) (hc : deriv f c = 0) (hq : 0 < deriv (deriv f) c)
    {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (c - r) (c + r), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∫ x in c - r..c + r, expPhase (f x)) -
      expPhase (f c + 1 / 8) / (Real.sqrt (deriv (deriv f) c) : ℂ)‖ ≤
        2 * Real.pi / 3 * M * r ^ 4 + 2 / (Real.pi * (deriv (deriv f) c * r)) := by
  let q := deriv (deriv f) c
  have hlocal := norm_integral_sub_stationary_quadratic_le hf c hc hr.le hM0 hM
  have hshift : (∫ x in c - r..c + r, expPhase (q / 2 * (x - c) ^ 2)) =
      ∫ x in -r..r, expPhase (q * x ^ 2 / 2) := by
    have hh := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => expPhase (q / 2 * (x - c) ^ 2)) (a := -r) (b := r) c
    rw [show -r + c = c - r by ring, show r + c = c + r by ring] at hh
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    congr 1
    ring
  change ‖(∫ x in c - r..c + r, expPhase (f x)) - expPhase (f c) *
    ∫ x in c - r..c + r, expPhase (q / 2 * (x - c) ^ 2)‖ ≤ _ at hlocal
  rw [hshift] at hlocal
  have hquad := norm_integral_quadratic_sub_fresnel_le hq hr
  have hmain : ‖expPhase (f c) * (∫ x in -r..r, expPhase (q * x ^ 2 / 2)) -
      expPhase (f c + 1 / 8) / (Real.sqrt q : ℂ)‖ ≤ 2 / (Real.pi * (q * r)) := by
    rw [expPhase_add, mul_div_assoc, ← mul_sub, norm_mul, norm_expPhase, one_mul]
    exact hquad
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (expPhase (f c) * ∫ x in -r..r, expPhase (q * x ^ 2 / 2)) _).trans
      (add_le_add hlocal hmain)

end WaveTurbulence.VdCB
