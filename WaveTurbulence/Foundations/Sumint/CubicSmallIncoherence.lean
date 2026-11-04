/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CubicHalfMomentStrip
public import WaveTurbulence.Foundations.Sumint.CubicWeylBridge

/-!
# The actual cubic lattice sum on the normal incoherence strip

The stationary-phase majorant is applied before time integration. Its
uniformity permits arbitrary modulations depending on all the times.
The bounded third-time interval supplies the integrable half moment.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint's normal small-region incoherence gain for the actual cubic sum. -/
theorem exists_cubic_small_incoherence_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ {c h : ℝ}, 0 < c → 0 ≤ h →
      ∀ (sel : Bool) (a b p : Mom d) (ξ ζ ω : ℝ → (ℝ × ℝ) → Mom d) (e v w : ℝ),
      w-v ≤ 3 →
      (∫⁻ t in Icc v w, ∫⁻ z : ℝ × ℝ,
        if |z.1| ≤ L ∧ |z.2| ≤ L ∧ |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
          ‖WeylSums.cubicLatticeSum L z.1 z.2 sel a b p (ξ t z) (ζ t z) (ω t z)‖ₑ else 0) ≤
      ENNReal.ofReal (C*L^(3*d)*(Real.sqrt h+c^(-(1/2:ℝ)))) := by
  obtain ⟨Cs,hCs,hsmall⟩ := exists_cubic_weyl_small_bound d
  let J := ∫ z : ℝ × ℝ, (1+|z.1|+|z.2|)^(-((d:ℝ)-1/2))
  have hJ : 0 ≤ J := integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
  refine ⟨8*Cs*J,mul_nonneg (mul_nonneg (by norm_num) hCs) hJ,?_⟩
  intro L hL c h hc hh sel a b p ξ ζ ω e v w hlen
  have hK : 0 ≤ Cs*L^(3*d) := mul_nonneg hCs (pow_nonneg (zero_le_one.trans hL) _)
  calc
    _ ≤ ∫⁻ t in Icc v w, ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (Cs*L^(3*d))*
        (if |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
          ENNReal.ofReal ((1+|z.1|+|z.2|)^(-(d:ℝ))) else 0) := by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro z
      change (if |z.1| ≤ L ∧ |z.2| ≤ L ∧ |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
          ‖WeylSums.cubicLatticeSum L z.1 z.2 sel a b p (ξ t z) (ζ t z) (ω t z)‖ₑ else 0) ≤
        ENNReal.ofReal (Cs*L^(3*d))*(if |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
          ENNReal.ofReal ((1+|z.1|+|z.2|)^(-(d:ℝ))) else 0)
      by_cases hz : |z.1| ≤ L ∧ |z.2| ≤ L ∧ |t-e| ≤ 2*h+(|z.1|+|z.2|)/c
      · rw [ite_eq_left hz,ite_eq_left hz.2.2,← ofReal_norm,← ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        have hb := hsmall hL z.2 z.1 hz.2.1 hz.1 sel a b p (ξ t z) (ζ t z) (ω t z)
        apply hb.trans_eq
        rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+|z.1|+|z.2|),Real.rpow_natCast]
        have hs : 1+|z.2|+|z.1| = 1+|z.1|+|z.2| := by ring
        rw [hs,div_eq_mul_inv]
      · rw [ite_eq_right hz]
        exact bot_le
    _ = ENNReal.ofReal (Cs*L^(3*d)) *
        (∫⁻ t in Icc v w, ∫⁻ z : ℝ × ℝ,
          if |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
            ENNReal.ofReal ((1+|z.1|+|z.2|)^(-(d:ℝ))) else 0) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Cs*L^(3*d)) *
        (ENNReal.ofReal (8*(Real.sqrt h+c^(-(1/2:ℝ))))*ENNReal.ofReal J) :=
      mul_le_mul' le_rfl (cubic_half_moment_strip_le d hd hc hh e v w hlen)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8*(Real.sqrt h+c^(-(1/2:ℝ)))),
        ← ENNReal.ofReal_mul hK]
      congr 1
      ring

end WaveTurbulence.Sumint
