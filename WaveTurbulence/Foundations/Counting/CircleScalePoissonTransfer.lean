/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CurvaturePoissonTransfer
public import WaveTurbulence.Foundations.NumberTheory.CircleTotalPoissonErrorScale
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# The quantitative B approximation at the circle source scales

Actual curvature and third-derivative bounds imply a stationary dual
approximation with error at the improved local circle powers. The radius,
frequency selection, critical points and all three error contributions are
constructed internally. The resulting dual still has to be identified and
estimated for the actual circle phase.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.Counting

/-- Quantitative stationary dual approximation at the actual circle
scales. No stationary-phase conclusion or exponential-sum estimate is an input. -/
theorem exists_stationary_dual_approximation_at_circle_scales {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) {a b : ℕ} (hab : a ≤ b) (N : ℕ) {w U : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2)
    (hwidth : 2*stationaryBalancingRadius w U ≤ (b:ℝ)-a)
    (hrange : ∀ x ∈ Icc (a:ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hN : (N:ℝ)+1 ≤ 3*(w*U^(-((1:ℝ)/2))))
    (hcurv : ∀ x ∈ Icc (a:ℝ) b,
      w*U^(-((3:ℝ)/2))/8 ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ w*U^(-((3:ℝ)/2)))
    (hthird : ∀ x ∈ Icc (a:ℝ) b, |iteratedDeriv 3 f x| ≤ 3*w*U^(-((5:ℝ)/2))) :
    let r := stationaryBalancingRadius w U
    let S := (Finset.Icc 0 (N:ℤ)).filter (fun (nu : ℤ) =>
      deriv f ((a:ℝ)+r) ≤ (nu:ℝ) ∧ (nu:ℝ) ≤ deriv f ((b:ℝ)-r))
    ∃ c : ℤ → ℝ,
      (∀ nu ∈ S, c nu ∈ Icc ((a:ℝ)+r) ((b:ℝ)-r) ∧ deriv f (c nu) = nu) ∧
      ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1)))-
        ∑ nu ∈ S, expPhase (f (c nu)-(nu:ℝ)*c nu+1/8) /
          (Real.sqrt (deriv (deriv f) (c nu)) : ℂ)‖ ≤
        2320*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  let r := stationaryBalancingRadius w U
  let mu : ℝ := w*U^(-((3:ℝ)/2))/8
  let M : ℝ := 3*w*U^(-((5:ℝ)/2))
  have hr : 0 < r := stationaryBalancingRadius_pos hwp hUp
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨c,hc,hbound⟩ := exists_stationary_dual_approximation_of_curvature_bounds hf hab N
    hr hwidth hmu hM hrange hcurv hthird
  refine ⟨c,hc,?_⟩
  exact hbound.trans (circle_scale_total_poisson_error_le hw hU hUw hwU N hN)

end WaveTurbulence.Counting
