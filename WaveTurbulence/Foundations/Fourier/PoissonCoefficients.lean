/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CoordinateSchwartz
public import WaveTurbulence.Foundations.Fourier.LatticeTiling
import Mathlib.Tactic

/-!
# Fourier coefficients of a multidimensional periodization

The coefficient of the periodization at an integer frequency is the
ordinary Fourier transform at that frequency. This is the central
identity for TARGET's Poisson summations (L1035, L1541, L1575).
-/

public section

open MeasureTheory Set
open scoped SchwartzMap

namespace WaveTurbulence.Fourier

/-- Normal convergence also permits integrating the absolute lattice sum
on the unit box. -/
theorem schwartz_translates_integral_norm_summable {d : ℕ}
    (f : 𝓢((Fin d → ℝ), ℂ)) :
    Summable fun n : Fin d → ℤ =>
      ∫ x in Icc (0 : Fin d → ℝ) 1, ‖f (x + fun i => (n i : ℝ))‖ := by
  let K : TopologicalSpace.Compacts (Fin d → ℝ) := ⟨Icc 0 1, isCompact_Icc⟩
  let F := fun n : Fin d → ℤ => f.toContinuousMap.comp
    (ContinuousMap.addRight (fun i => (n i : ℝ)))
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    (schwartz_translates_locally_summable f K)
  have hb := norm_setIntegral_le_of_norm_le_const_ae (μ := (volume : Measure (Fin d → ℝ)))
    (s := Icc (0 : Fin d → ℝ) 1) (f := fun x => ‖f (x + fun i => (n i : ℝ))‖)
    (C := ‖(F n).restrict K‖) (isCompact_Icc.measure_lt_top) ?_
  · simpa only [F, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      Measure.real, Real.volume_Icc_pi, Pi.one_apply, Pi.zero_apply, sub_zero,
      ENNReal.ofReal_one, Finset.prod_const_one, ENNReal.toReal_one, mul_one] using hb
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hm := ContinuousMap.norm_coe_le_norm ((F n).restrict K) ⟨x, hx⟩
    change ‖f (x + fun i => (n i : ℝ))‖ ≤ ‖(F n).restrict K‖ at hm
    simpa only [norm_norm] using hm

/-- The paper's negative torus character is the coordinate Fourier phase. -/
theorem torusChar_neg_eq_fourierChar {d : ℕ} (m : Fin d → ℤ) (x : Fin d → ℝ) :
    WaveTurbulence.torusChar 1 (-m) x =
      (Real.fourierChar (-timePairing d x (fun i => (m i : ℝ))) : ℂ) := by
  have he : (∑ j, ((-m j : ℤ) : ℝ) / 1 * x j) = -(∑ j, x j * (m j : ℝ)) := by
    simp only [Int.cast_neg, div_one, neg_mul, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  change Complex.exp ((2 * Real.pi * (∑ j, ((-m j : ℤ) : ℝ) / 1 * x j) : ℝ) * Complex.I) =
    Complex.exp ((2 * Real.pi * (-(∑ j, x j * (m j : ℝ))) : ℝ) * Complex.I)
  rw [he]

/-- Fourier coefficients commute with periodization and unfold to the
ordinary Fourier integral. -/
theorem torusFourierCoeff_schwartzPeriodization {d : ℕ}
    (f : 𝓢((Fin d → ℝ), ℂ)) (m : Fin d → ℤ) :
    WaveTurbulence.torusFourierCoeff 1 (schwartzPeriodization f) m =
      timeFourier f (fun i => (m i : ℝ)) := by
  have hFi (n : Fin d → ℤ) : IntegrableOn
      (fun x => f (x + fun i => (n i : ℝ))) (Icc (0 : Fin d → ℝ) 1) :=
    (f.continuous.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  rw [show (schwartzPeriodization f : (Fin d → ℝ) → ℂ) =
      (fun x => ∑' n : Fin d → ℤ, f (x + fun i => (n i : ℝ))) from
    funext (schwartzPeriodization_apply f)]
  have hsum := WaveTurbulence.torusFourierCoeff_tsum (L := (1 : ℝ)) hFi
    (schwartz_translates_integral_norm_summable f) m
  change WaveTurbulence.torusFourierCoeff 1
    (fun x => ∑' n : Fin d → ℤ, f (x + fun i => (n i : ℝ))) m = _ at hsum
  rw [hsum]
  let g := fun x => f x * WaveTurbulence.torusChar 1 (-m) x
  have hg : Integrable g := Integrable.mul_bdd f.integrable
    (WaveTurbulence.continuous_torusChar 1 (-m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (WaveTurbulence.norm_torusChar 1 (-m) x).le)
  have ht := integral_eq_tsum_unitBox g hg
  have hterm (n : Fin d → ℤ) :
      WaveTurbulence.torusFourierCoeff 1 (fun x => f (x + fun i => (n i : ℝ))) m =
        ∫ x in Icc (0 : Fin d → ℝ) 1, g (x + fun i => (n i : ℝ)) := by
    simp only [WaveTurbulence.torusFourierCoeff_eq_integral, Real.one_rpow,
      Complex.ofReal_one, inv_one, one_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp [g]
      have hp : WaveTurbulence.torusChar 1 (-m) (x + fun i => (n i : ℝ)) =
          WaveTurbulence.torusChar 1 (-m) x := by
        simpa only [mul_one] using
          (WaveTurbulence.isTorusPeriodic_torusChar (by norm_num : (1 : ℝ) ≠ 0) (-m)).add_int_mul n x
      rw [hp]
  simp_rw [hterm]
  rw [← ht]
  change (∫ x, f x * WaveTurbulence.torusChar 1 (-m) x) = _
  simp only [timeFourier, VectorFourier.fourierIntegral]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [torusChar_neg_eq_fourierChar, Circle.smul_def, smul_eq_mul, mul_comm]

end WaveTurbulence.Fourier
