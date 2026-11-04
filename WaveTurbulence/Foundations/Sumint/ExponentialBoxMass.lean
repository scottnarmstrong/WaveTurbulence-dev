/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ExponentialBoxIntegrability
public import WaveTurbulence.Foundations.Sumint.ExponentialBoxPointwise
import Mathlib.Tactic

/-!
# Uniform absolute mass of the rectangular extension kernel

The kernel is real and nonnegative. Its absolute integral is therefore
controlled by the already established Fourier estimate at frequency zero.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The complex kernel takes only nonnegative real values. -/
theorem norm_exponentialBox_eq_re (a b u : ℝ) (z : Fin 3 → ℝ) :
    ‖exponentialBox a b u z‖ = (exponentialBox a b u z).re := by
  rw [exponentialBox_eq_ite]
  split_ifs
  · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.ofReal_re]
  · simp

/-- The kernel's absolute mass is uniformly bounded independently of all exit times. -/
theorem integral_norm_exponentialBox_le {a b u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : u ≤ 0) : (∫ z, ‖exponentialBox a b u z‖) ≤ 2 := by
  have hi := integrable_exponentialBox a b u
  have hz : Fourier.timeFourier (exponentialBox a b u) 0 = ∫ z, exponentialBox a b u z := by
    simp [Fourier.timeFourier, VectorFourier.fourierIntegral, Fourier.timePairing]
  calc
    _ = (∫ z, exponentialBox a b u z).re := by
      simp_rw [norm_exponentialBox_eq_re]
      exact integral_re hi
    _ ≤ ‖∫ z, exponentialBox a b u z‖ := Complex.re_le_norm _
    _ ≤ 2 := by
      rw [← hz]
      simpa [scalarBracket] using norm_timeFourier_exponentialBox_le ha hab hu (0 : Fin 3 → ℝ)

/-- Reversed finite endpoints make the whole rectangular kernel vanish. -/
theorem exponentialBox_eq_zero_of_lt {a b : ℝ} (hab : b < a) (u : ℝ) :
    exponentialBox a b u = 0 := by
  funext z
  rw [exponentialBox_eq_ite]
  have hh : ¬ (z 0 ∈ Set.Icc a b ∧ z 1 < u ∧ z 2 < u) := by
    intro hh
    exact (not_le.mpr hab) (hh.1.1.trans hh.1.2)
  simp only [ite_eq_right hh, Pi.zero_apply]

/-- The mass bound holds even when the intersection of input intervals is empty. -/
theorem integral_norm_exponentialBox_le_all {a b u : ℝ} (ha : 0 ≤ a) (hu : u ≤ 0) :
    (∫ z, ‖exponentialBox a b u z‖) ≤ 2 := by
  by_cases hab : a ≤ b
  · exact integral_norm_exponentialBox_le ha hab hu
  · rw [exponentialBox_eq_zero_of_lt (lt_of_not_ge hab)]
    simp

/-- The Fourier kernel bound includes empty exit intervals. -/
theorem norm_timeFourier_exponentialBox_le_all {a b u : ℝ} (ha : 0 ≤ a)
    (hu : u ≤ 0) (ξ : Fin 3 → ℝ) :
    ‖Fourier.timeFourier (exponentialBox a b u) ξ‖ ≤
      2 * ∏ j, (1 / scalarBracket (ξ j)) := by
  by_cases hab : a ≤ b
  · exact norm_timeFourier_exponentialBox_le ha hab hu ξ
  · rw [exponentialBox_eq_zero_of_lt (lt_of_not_ge hab)]
    simp only [Fourier.timeFourier, VectorFourier.fourierIntegral, Pi.zero_apply,
      smul_zero, integral_zero, norm_zero]
    exact mul_nonneg (by norm_num) (Finset.prod_nonneg (fun j _ =>
      div_nonneg (by norm_num) (zero_le_one.trans (one_le_scalarBracket _))))

end WaveTurbulence.Sumint
