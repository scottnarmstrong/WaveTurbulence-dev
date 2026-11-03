/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.GaussianTail
public import WaveTurbulence.Foundations.VdCB.FresnelCoefficient
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The damped quadratic integral and its sharp truncation

The complex Gaussian formula evaluates the total integral. Evenness and
the uniform tail estimate compare it with a sharp symmetric interval.
-/

public section

open MeasureTheory Set Filter
open WaveTurbulence.NumberTheory
open scoped FourierTransform Topology

namespace WaveTurbulence.VdCB

/-- Gaussian-damped quadratic character. -/
@[expose] noncomputable def dampedQuadratic (q ε x : ℝ) : ℂ :=
  expPhase (q * x ^ 2 / 2) * (Real.exp (-Real.pi * ε * x ^ 2) : ℂ)

theorem dampedQuadratic_eq_gaussian (q ε x : ℝ) :
    dampedQuadratic q ε x =
      Complex.exp (-Real.pi * ((ε : ℂ) - (q : ℂ) * Complex.I) * (x : ℂ) ^ 2) := by
  unfold dampedQuadratic expPhase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_dampedQuadratic (q ε : ℝ) : Continuous (dampedQuadratic q ε) := by
  unfold dampedQuadratic
  exact ((contDiff_expPhase 0).continuous.comp (by fun_prop)).mul (by fun_prop)

theorem dampedQuadratic_neg (q ε x : ℝ) : dampedQuadratic q ε (-x) = dampedQuadratic q ε x := by
  simp only [dampedQuadratic, neg_sq]

theorem integrable_dampedQuadratic (q : ℝ) {ε : ℝ} (hε : 0 < ε) : Integrable (dampedQuadratic q ε) := by
  rw [show dampedQuadratic q ε = (fun x : ℝ =>
    Complex.exp (-Real.pi * ((ε : ℂ) - (q : ℂ) * Complex.I) * (x : ℂ) ^ 2)) from
      funext (dampedQuadratic_eq_gaussian q ε)]
  have hp : 0 < ((Real.pi : ℂ) * ((ε : ℂ) - (q : ℂ) * Complex.I)).re := by
    simpa using mul_pos Real.pi_pos hε
  simpa only [neg_mul, mul_assoc] using integrable_cexp_neg_mul_sq hp

/-- Exact Gaussian evaluation before taking the oscillatory limit. -/
theorem integral_dampedQuadratic (q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ, dampedQuadratic q ε x) =
      1 / ((ε : ℂ) - (q : ℂ) * Complex.I) ^ (1 / 2 : ℂ) := by
  have hp : 0 < ((ε : ℂ) - (q : ℂ) * Complex.I).re := by simpa using hε
  have hh := congrFun (fourier_gaussian_pi hp) 0
  rw [Real.fourier_eq] at hh
  simp_rw [dampedQuadratic_eq_gaussian]
  simpa [neg_mul] using hh

/-- The sharp symmetric cutoff differs from the total damped integral
by at most two uniform half-line tails. -/
theorem norm_integral_dampedQuadratic_sub_interval_le {q ε r : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (hr : 0 < r) :
    ‖(∫ x : ℝ, dampedQuadratic q ε x) - ∫ x in -r..r, dampedQuadratic q ε x‖ ≤
      2 / (Real.pi * (q * r)) := by
  let G := dampedQuadratic q ε
  have hGi := integrable_dampedQuadratic q hε
  have hGc := continuous_dampedQuadratic q ε
  have heven (T : ℝ) : (∫ x in -T..(-r), G x) = ∫ x in r..T, G x := by
    have hh := intervalIntegral.integral_comp_neg (f := G) (a := r) (b := T)
    simpa only [G, dampedQuadratic_neg] using hh.symm
  have hbound (T : ℝ) (hT : r ≤ T) :
      ‖(∫ x in -T..T, G x) - ∫ x in -r..r, G x‖ ≤ 2 / (Real.pi * (q * r)) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hGc.intervalIntegrable (μ := volume) (-T) (-r)) (hGc.intervalIntegrable (μ := volume) (-r) r)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hGc.intervalIntegrable (μ := volume) (-T) r) (hGc.intervalIntegrable (μ := volume) r T)
    have heq : (∫ x in -T..T, G x) - ∫ x in -r..r, G x =
        (∫ x in r..T, G x) + ∫ x in r..T, G x := by
      rw [← h2, ← h1, heven]
      ring
    rw [heq]
    have hh := norm_integral_damped_quadratic_tail_le hq hε.le hr hT
    change ‖∫ x in r..T, G x‖ ≤ 1 / (Real.pi * (q * r)) at hh
    calc
      _ ≤ ‖∫ x in r..T, G x‖ + ‖∫ x in r..T, G x‖ := norm_add_le _ _
      _ ≤ 1 / (Real.pi * (q * r)) + 1 / (Real.pi * (q * r)) := add_le_add hh hh
      _ = _ := by ring
  have hl := (intervalIntegral_tendsto_integral hGi tendsto_neg_atTop_atBot tendsto_id).sub_const
    (∫ x in -r..r, G x)
  apply le_of_tendsto hl.norm
  filter_upwards [eventually_ge_atTop r] with T hT
  exact hbound T hT

end WaveTurbulence.VdCB
