/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RationalArcCover
public import WaveTurbulence.Foundations.WeylSums.ArcAlgebra
public import WaveTurbulence.Foundations.WeylSums.SmoothCutoff

/-!
# A common positive majorant for smooth quadratic Weyl sums

Dirichlet approximation and the proved log-free Gauss estimate select one
term of the rational-arc envelope. The resulting majorant is uniform in
both the center and the linear frequency, before either supremum is taken.
-/

public section

open MeasureTheory Finset
open scoped BigOperators ContDiff

namespace WaveTurbulence.WeylSums

/-- Uniform rational-arc envelope on a unit interval. The constant depends
only on the smooth compactly supported cutoff, not on the real exponent. -/
theorem exists_smooth_rationalArcEnvelope_bound (χ : ℝ → ℂ)
    (hc : HasCompactSupport χ) (hs : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (p t r : ℝ) (h : ℤ),
      0 ≤ p → t ∈ Set.Icc (0 : ℝ) 1 →
      ‖smoothGaussSum χ N t r h‖ ^ p ≤
        (C * N) ^ p * rationalArcEnvelope N (p / 2) N t := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_smoothGaussSum_le χ hc hs
  refine ⟨C, hC, ?_⟩
  intro N hN p t r h hp ht
  obtain ⟨a, q, hq, hqN, ha, hanum, happ⟩ := exists_approx_unit_interval t hN ht
  have hN' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hgauss := hbound N t r h a q hN' hq (Nat.cast_le.mpr hqN) ha happ
  have hprofile := rpow_le_scaledArcProfile ‖smoothGaussSum χ N t r h‖ (C * N) N q
    |t - (a : ℝ) / q| p (norm_nonneg _) (mul_nonneg hC.le (Nat.cast_nonneg _))
    (Nat.cast_nonneg _) hq' (abs_nonneg _) hp hgauss
  have hterm : (q : ℝ) ^ (-p / 2) * scaledArcProfile N (p / 2) ((a : ℝ) / q) t ≤
      rationalArcEnvelope N (p / 2) N t := by
    have hinner : scaledArcProfile N (p / 2) ((a : ℝ) / q) t ≤
        ∑ b ∈ Icc (-1 : ℤ) ((q : ℤ) + 1), scaledArcProfile N (p / 2) ((b : ℝ) / q) t :=
      single_le_sum (fun (b : ℤ) _ => scaledArcProfile_nonneg (N : ℝ) (p / 2) ((b : ℝ) / q) t) hanum
    refine (mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hq'.le _)).trans ?_
    rw [show (-p / 2 : ℝ) = -(p / 2) by ring]
    unfold rationalArcEnvelope
    apply single_le_sum _ (mem_Icc.mpr ⟨hq, hqN⟩)
    intro k hk
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    apply sum_nonneg
    intro b hb
    exact scaledArcProfile_nonneg _ _ _ _

  rw [scaledArcProfile_eq] at hterm
  refine hprofile.trans ?_
  have hh := mul_le_mul_of_nonneg_left hterm (Real.rpow_nonneg (mul_nonneg hC.le (Nat.cast_nonneg N)) p)
  exact (mul_assoc _ _ _).le.trans hh

/-- Measurability of a quadratic cutoff sum in the quadratic frequency. -/
theorem measurable_smoothGaussSum (χ : ℝ → ℂ) (L r : ℝ) (h : ℤ) :
    Measurable (fun t : ℝ => smoothGaussSum χ L t r h) := by
  unfold smoothGaussSum
  apply Measurable.tsum
  intro n
  exact measurable_const.mul (continuous_e.measurable.comp (by fun_prop))

end WaveTurbulence.WeylSums
