/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.SmoothArcEnvelope
public import WaveTurbulence.Foundations.Fourier.Chi0
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The supremum Weyl sum

The supremum is over all real linear frequencies and all integer centers,
as in TARGET (wyel). Integer translation reduces the centers to zero.
Finite support gives continuity before taking the supremum, hence lower
semicontinuity and measurability of the supremum itself.
-/

public section

open MeasureTheory Finset
open scoped BigOperators ContDiff

namespace WaveTurbulence.WeylSums

/-- The paper's fixed one-dimensional cutoff, viewed as complex valued. -/
@[expose] noncomputable def weylCutoff (x : ℝ) : ℂ := Fourier.chi0 x

/-- The supremum in TARGET (wyel), with the supremum inside the integral. -/
@[expose] noncomputable def weylSupremum (L t : ℝ) : ℝ :=
  ⨆ r : ℝ, ‖smoothGaussSum weylCutoff L t r 0‖

theorem weylCutoff_hasCompactSupport : HasCompactSupport weylCutoff :=
  Fourier.chi0_hasCompactSupport.comp_left (by simp)

theorem weylCutoff_contDiff : ContDiff ℝ ∞ weylCutoff :=
  Complex.ofRealCLM.contDiff.comp Fourier.chi0_contDiff

/-- A common finite summation range, independent of either frequency. -/
theorem weyl_sum_eq_finite {L : ℝ} (hL : 0 < L) (t r : ℝ) :
    smoothGaussSum weylCutoff L t r 0 =
      ∑ n ∈ Icc (-⌈L⌉ : ℤ) ⌈L⌉, weylCutoff ((n : ℝ) / L) * e (t * (n : ℝ)^2 + r*n) := by
  unfold smoothGaussSum
  simp only [Int.cast_zero, sub_zero]
  apply tsum_eq_sum
  intro n hn
  have hout : 1 ≤ |(n : ℝ) / L| := by
    by_contra hh
    have ha := abs_lt.mp (lt_of_not_ge hh)
    have hb : -(L : ℝ) < n ∧ (n : ℝ) < L :=
      ⟨by have := (lt_div_iff₀ hL).mp ha.1; linarith,
       by simpa only [one_mul] using (div_lt_iff₀ hL).mp ha.2⟩
    apply hn
    apply mem_Icc.mpr
    have hc := Int.le_ceil L
    constructor
    · exact_mod_cast (by push_cast; linarith : ((-⌈L⌉ : ℤ) : ℝ) ≤ (n : ℝ))
    · exact_mod_cast hb.2.le.trans hc
  simp [weylCutoff, Fourier.chi0_eq_zero hout]

/-- A finite uniform bound for the complete family of linear frequencies. -/
theorem weyl_family_bddAbove {L : ℝ} (hL : 0 < L) (t : ℝ) :
    BddAbove (Set.range fun r : ℝ => ‖smoothGaussSum weylCutoff L t r 0‖) := by
  refine ⟨∑ n ∈ Icc (-⌈L⌉ : ℤ) ⌈L⌉, ‖weylCutoff ((n : ℝ) / L)‖, ?_⟩
  rintro _ ⟨r, rfl⟩
  change ‖smoothGaussSum weylCutoff L t r 0‖ ≤ _
  rw [weyl_sum_eq_finite hL]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, norm_e, mul_one])

/-- Every translated smooth Weyl sum is bounded by the same supremum. -/
theorem norm_smoothGaussSum_le_weylSupremum {L : ℝ} (hL : 0 < L)
    (t r : ℝ) (h : ℤ) : ‖smoothGaussSum weylCutoff L t r h‖ ≤ weylSupremum L t := by
  rw [norm_smoothGaussSum_shift]
  exact le_ciSup (weyl_family_bddAbove hL t) _

theorem weylSupremum_nonneg {L : ℝ} (hL : 0 < L) (t : ℝ) : 0 ≤ weylSupremum L t :=
  (norm_nonneg _).trans (norm_smoothGaussSum_le_weylSupremum hL t 0 0)

theorem lowerSemicontinuous_weylSupremum {L : ℝ} (hL : 0 < L) :
    LowerSemicontinuous (weylSupremum L) := by
  apply lowerSemicontinuous_ciSup (weyl_family_bddAbove hL)
  intro r
  have heq : (fun t : ℝ => ‖smoothGaussSum weylCutoff L t r 0‖) =
      fun t => ‖∑ n ∈ Icc (-⌈L⌉ : ℤ) ⌈L⌉,
        weylCutoff ((n : ℝ) / L) * e (t * (n : ℝ)^2 + r*n)‖ := by
    funext t
    rw [weyl_sum_eq_finite hL]
  rw [heq]
  apply Continuous.lowerSemicontinuous
  apply Continuous.norm
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul (continuous_e.comp (by fun_prop))

theorem measurable_weylSupremum {L : ℝ} (hL : 0 < L) : Measurable (weylSupremum L) :=
  (lowerSemicontinuous_weylSupremum hL).measurable

end WaveTurbulence.WeylSums
