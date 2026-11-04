/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BoundedTimeStrip
public import WaveTurbulence.Foundations.Sumint.CubicTimeKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The half-moment normal incoherence strip

A third-time interval of length at most three gives a square-root
strip gain. The radial exponent d-1/2 is strictly greater than two for
dimension at least three, so the needed moment is integrable.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The exact half moment absorbs the square root of the rescaled time gap. -/
theorem cubic_half_moment_pointwise {d : ℕ} {ρ c h : ℝ}
    (hρ : 0 ≤ ρ) (hc : 0 < c) (_hh : 0 ≤ h) :
    (Real.sqrt h+Real.sqrt (ρ/c))*(1+ρ)^(-(d:ℝ)) ≤
      (Real.sqrt h+c^(-(1/2:ℝ)))*(1+ρ)^(-((d:ℝ)-1/2)) := by
  have hbase : 1 ≤ 1+ρ := by linarith only [hρ]
  have hbp : 0 < 1+ρ := zero_lt_one.trans_le hbase
  have hk : (1+ρ)^(-(d:ℝ)) ≤ (1+ρ)^(-((d:ℝ)-1/2)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hroot : Real.sqrt (ρ/c) ≤ c^(-(1/2:ℝ))*(1+ρ)^(1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.div_rpow hρ hc.le,div_eq_inv_mul,← Real.rpow_neg hc.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hρ (by linarith) (by norm_num)) (Real.rpow_nonneg hc.le _)
  have he : (c^(-(1/2:ℝ))*(1+ρ)^(1/2:ℝ))*(1+ρ)^(-(d:ℝ)) =
      c^(-(1/2:ℝ))*(1+ρ)^(-((d:ℝ)-1/2)) := by
    rw [mul_assoc,← Real.rpow_add hbp]
    congr 2
    ring
  calc
    _ = Real.sqrt h*(1+ρ)^(-(d:ℝ))+Real.sqrt (ρ/c)*(1+ρ)^(-(d:ℝ)) := by ring
    _ ≤ Real.sqrt h*(1+ρ)^(-((d:ℝ)-1/2))+
        c^(-(1/2:ℝ))*(1+ρ)^(-((d:ℝ)-1/2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg _))
        ((mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hbp.le _)).trans_eq he)
    _ = _ := by ring

/-- The normal incoherence strip gains the square root of the enlarged width or inverse scale. -/
theorem cubic_half_moment_strip_le (d : ℕ) (hd : 3 ≤ d) {c h : ℝ}
    (hc : 0 < c) (hh : 0 ≤ h) (e v w : ℝ) (hlen : w-v ≤ 3) :
    (∫⁻ t in Icc v w, ∫⁻ z : ℝ × ℝ,
      if |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
        ENNReal.ofReal ((1+|z.1|+|z.2|)^(-(d:ℝ))) else 0) ≤
      ENNReal.ofReal (8*(Real.sqrt h+c^(-(1/2:ℝ)))) *
        ENNReal.ofReal (∫ z : ℝ × ℝ, (1+|z.1|+|z.2|)^(-((d:ℝ)-1/2))) := by
  let ρ := fun z : ℝ × ℝ => |z.1|+|z.2|
  let K := fun z : ℝ × ℝ => (1+ρ z)^(-(d:ℝ))
  let J := fun z : ℝ × ℝ => (1+ρ z)^(-((d:ℝ)-1/2))
  have hρ (z : ℝ × ℝ) : 0 ≤ ρ z := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hK : Measurable (fun z => ENNReal.ofReal (K z)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    apply Continuous.rpow_const
    · dsimp [ρ]
      fun_prop
    · intro z
      exact Or.inl (by have := hρ z; positivity)
  have hR : Measurable (fun z : ℝ × ℝ => 2*h+ρ z/c) := by
    dsimp [ρ]
    fun_prop
  have hJ : Integrable J := by
    have hp : (2:ℝ) < (d:ℝ)-1/2 := by
      have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    simpa only [J,ρ,add_assoc] using integrable_cubicTimeKernel hp
  have hscale (z : ℝ × ℝ) : 1+|z.1|+|z.2| = 1+ρ z := by dsimp [ρ]; ring
  simp_rw [hscale]
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (K z)*ENNReal.ofReal (min 3 (2*(2*h+ρ z/c))) :=
      lintegral_bounded_time_strip_le _ hK _ hR e v w hlen
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (8*(Real.sqrt h+c^(-(1/2:ℝ))))*ENNReal.ofReal (J z) := by
      apply lintegral_mono
      intro z
      change ENNReal.ofReal (K z)*ENNReal.ofReal (min 3 (2*(2*h+ρ z/c))) ≤
        ENNReal.ofReal (8*(Real.sqrt h+c^(-(1/2:ℝ))))*ENNReal.ofReal (J z)
      have hkp : 0 ≤ K z := Real.rpow_nonneg (by have := hρ z; positivity) _
      have hconst : 0 ≤ 8*(Real.sqrt h+c^(-(1/2:ℝ))) := by positivity
      rw [← ENNReal.ofReal_mul hkp,← ENNReal.ofReal_mul hconst]
      apply ENNReal.ofReal_le_ofReal
      have hm := min_three_width_le_sqrt hh (div_nonneg (hρ z) hc.le)
      have ht := cubic_half_moment_pointwise (d := d) (hρ z) hc hh
      calc
        _ = min 3 (4*h+2*(ρ z/c))*K z := by
          have he : 2*(2*h+ρ z/c) = 4*h+2*(ρ z/c) := by ring
          rw [he,mul_comm]
        _ ≤ (8*(Real.sqrt h+Real.sqrt (ρ z/c)))*K z := mul_le_mul_of_nonneg_right hm hkp
        _ ≤ _ := by
          dsimp only [K,J]
          nlinarith only [ht]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal hJ (ae_of_all _ (fun z =>
          Real.rpow_nonneg (by have := hρ z; positivity) _))]

end WaveTurbulence.Sumint
