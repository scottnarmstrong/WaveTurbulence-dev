/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothInterval
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Unit mass of a smooth step's derivative

The transition width does not affect this mass. This is the bounded variation
control needed for literal interval fibers in TARGET (incohproof27)–(incohproof28).
-/

public section
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- A translated and rescaled monotone smooth step. -/
@[expose] def smoothStep (ε a t : ℝ) : ℝ := Real.smoothTransition ((t - a) / ε)

@[fun_prop] theorem contDiff_smoothStep (ε a : ℝ) : ContDiff ℝ ∞ (smoothStep ε a) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem monotone_smoothStep {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Monotone (smoothStep ε a) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hε.le

theorem deriv_smoothStep_eq_zero_left {ε a t : ℝ} (hε : 0 < ε) (ht : t < a) :
    deriv (smoothStep ε a) t = 0 := by
  have he : smoothStep ε a =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.le) hε.le)
  rw [he.deriv_eq, deriv_const]

theorem deriv_smoothStep_eq_zero_right {ε a t : ℝ} (hε : 0 < ε) (ht : a + ε < t) :
    deriv (smoothStep ε a) t = 0 := by
  have he : smoothStep ε a =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by have hx' : a + ε < x := hx; linarith))
  rw [he.deriv_eq, deriv_const]

theorem hasCompactSupport_deriv_smoothStep {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    HasCompactSupport (deriv (smoothStep ε a)) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := a + ε))
  intro t ht
  rcases not_and_or.mp ht with ha | hb
  · exact deriv_smoothStep_eq_zero_left hε (lt_of_not_ge ha)
  · exact deriv_smoothStep_eq_zero_right hε (lt_of_not_ge hb)

theorem integral_deriv_smoothStep {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (∫ t, deriv (smoothStep ε a) t) = 1 := by
  have hd : Differentiable ℝ (smoothStep ε a) :=
    (contDiff_smoothStep ε a).differentiable (by norm_num)
  have hc : Continuous (deriv (smoothStep ε a)) :=
    (contDiff_smoothStep ε a).continuous_deriv (by norm_num)
  have hs : Function.support (deriv (smoothStep ε a)) ⊆ Ioc (a - 1) (a + ε + 1) := by
    intro t ht
    constructor
    · by_contra hn
      exact ht (deriv_smoothStep_eq_zero_left hε (by linarith [not_lt.mp hn]))
    · by_contra hn
      exact ht (deriv_smoothStep_eq_zero_right hε (by linarith [not_le.mp hn]))
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hd t) (hc.intervalIntegrable _ _)]
  have hl : smoothStep ε a (a - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
  have hr : smoothStep ε a (a + ε + 1) = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith))
  rw [hl, hr, sub_zero]

/-- Each smoothed interval has total variation at most two, uniformly in its width. -/
theorem integral_norm_deriv_smoothInterval_le {ε : ℝ} (hε : 0 < ε) (a b : ℝ)
    (hab : a ≤ b) : (∫ t, ‖deriv (smoothInterval ε a b) t‖) ≤ 2 := by
  have hi (c : ℝ) : Integrable (deriv (smoothStep ε c)) :=
    ((contDiff_smoothStep ε c).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      (hasCompactSupport_deriv_smoothStep hε c)
  have hw : Integrable (fun t => ‖deriv (smoothInterval ε a b) t‖) :=
    (((contDiff_smoothInterval ε a b).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
      (hasCompactSupport_smoothInterval hε hab).deriv).norm
  have he (t : ℝ) : deriv (smoothInterval ε a b) t =
      deriv (smoothStep ε a) t - deriv (smoothStep ε b) t := by
    change deriv (fun u => smoothStep ε a u - smoothStep ε b u) t = _
    exact deriv_sub ((contDiff_smoothStep ε a).differentiable (by norm_num) t)
      ((contDiff_smoothStep ε b).differentiable (by norm_num) t)
  calc
    _ ≤ ∫ t, deriv (smoothStep ε a) t + deriv (smoothStep ε b) t := by
      apply integral_mono hw ((hi a).add (hi b))
      intro t
      dsimp only [Pi.add_apply]
      rw [he]
      exact (norm_sub_le _ _).trans_eq (by
        rw [Real.norm_of_nonneg ((monotone_smoothStep hε a).deriv_nonneg),
          Real.norm_of_nonneg ((monotone_smoothStep hε b).deriv_nonneg)])
    _ = 2 := by rw [integral_add (hi a) (hi b), integral_deriv_smoothStep hε,
        integral_deriv_smoothStep hε]; norm_num

end WaveTurbulence.Incoh
