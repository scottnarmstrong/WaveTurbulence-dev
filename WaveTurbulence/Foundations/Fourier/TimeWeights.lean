/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-!
# Time-frequency weights

Basic estimates for the maximum Japanese bracket in TARGET `(normX1)`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

theorem one_le_timeBracket {r : ℕ} (ξ : Fin r → ℝ) : 1 ≤ timeBracket ξ := by
  exact Finset.le_sup' (f := fun i : Option (Fin r) =>
    match i with | none => (1 : ℝ) | some j => Real.sqrt (1 + ξ j ^ 2))
    (Finset.mem_univ none)

theorem bracket_le_timeBracket {r : ℕ} (ξ : Fin r → ℝ) (j : Fin r) :
    Real.sqrt (1 + ξ j ^ 2) ≤ timeBracket ξ := by
  exact Finset.le_sup' (f := fun i : Option (Fin r) =>
    match i with | none => (1 : ℝ) | some j => Real.sqrt (1 + ξ j ^ 2))
    (Finset.mem_univ (some j))

theorem timeBracket_pos {r : ℕ} (ξ : Fin r → ℝ) : 0 < timeBracket ξ :=
  zero_lt_one.trans_le (one_le_timeBracket ξ)

theorem timeBracket_le {r : ℕ} {ξ : Fin r → ℝ} {a : ℝ}
    (ha : 1 ≤ a) (hξ : ∀ j, Real.sqrt (1 + ξ j ^ 2) ≤ a) : timeBracket ξ ≤ a := by
  apply Finset.sup'_le
  intro i _
  cases i with
  | none => exact ha
  | some j => exact hξ j

@[fun_prop] theorem timeBracket_continuous (r : ℕ) :
    Continuous (timeBracket (r := r)) := by
  apply Continuous.finset_sup'_apply
  intro i _
  cases i with
  | none => exact continuous_const
  | some j => fun_prop

@[fun_prop] theorem timeWeight_measurable {r : ℕ} (θ : ℝ) :
    Measurable (timeWeight (r := r) θ) := by
  apply ENNReal.measurable_ofReal.comp
  exact (timeBracket_continuous r).measurable.pow_const θ

theorem timeWeight_mono {r : ℕ} {θ θ' : ℝ} (h : θ ≤ θ') (ξ : Fin r → ℝ) :
    timeWeight θ ξ ≤ timeWeight θ' ξ :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (one_le_timeBracket ξ) h)

theorem timeFourierNorm_mono {r : ℕ} {θ θ' : ℝ} (h : θ ≤ θ')
    (f : (Fin r → ℝ) → ℂ) : timeFourierNorm θ f ≤ timeFourierNorm θ' f := by
  classical
  unfold timeFourierNorm
  split_ifs
  · exact lintegral_mono fun ξ => mul_le_mul_left (timeWeight_mono h ξ) _
  · exact le_rfl

private theorem scalarBracket_add_le (x y : ℝ) :
    Real.sqrt (1 + (x + y) ^ 2) ≤ Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2) := by
  have hx := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hy := Real.sq_sqrt (show 0 ≤ 1 + y ^ 2 by positivity)
  have hxy := Real.sq_sqrt (show 0 ≤ 1 + (x + y) ^ 2 by positivity)
  have hnx := Real.sqrt_nonneg (1 + x ^ 2)
  have hny := Real.sqrt_nonneg (1 + y ^ 2)
  have hnxy := Real.sqrt_nonneg (1 + (x + y) ^ 2)
  have hax : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have hay : |y| ≤ Real.sqrt (1 + y ^ 2) := by
    have := sq_abs y
    nlinarith [abs_nonneg y]
  have hp := mul_le_mul hax hay (abs_nonneg y) hnx
  have hxyabs : x * y ≤ |x| * |y| := by simpa only [abs_mul] using le_abs_self (x * y)
  nlinarith

/-- The maximum Japanese bracket is subadditive. -/
theorem timeBracket_add_le {r : ℕ} (ξ η : Fin r → ℝ) :
    timeBracket (ξ + η) ≤ timeBracket ξ + timeBracket η := by
  apply timeBracket_le
  · linarith [one_le_timeBracket ξ, one_le_timeBracket η]
  · intro j
    exact (scalarBracket_add_le (ξ j) (η j)).trans
      (add_le_add (bracket_le_timeBracket ξ j) (bracket_le_timeBracket η j))

/-- Submultiplicativity up to the absolute factor two. -/
theorem timeBracket_add_le_mul {r : ℕ} (ξ η : Fin r → ℝ) :
    timeBracket (ξ + η) ≤ 2 * timeBracket ξ * timeBracket η := by
  have hξ := one_le_timeBracket ξ
  have hη := one_le_timeBracket η
  have hp : 0 ≤ (timeBracket ξ - 1) * (timeBracket η - 1) :=
    mul_nonneg (sub_nonneg.mpr hξ) (sub_nonneg.mpr hη)
  apply (timeBracket_add_le ξ η).trans
  nlinarith

/-- The weighted convolution estimate uses this pointwise inequality. -/
theorem timeWeight_add_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (ξ η : Fin r → ℝ) :
    timeWeight θ (ξ + η) ≤ ENNReal.ofReal (2 ^ θ) * timeWeight θ ξ * timeWeight θ η := by
  unfold timeWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (timeBracket_pos ξ).le _))]
  apply ENNReal.ofReal_le_ofReal
  calc
    timeBracket (ξ + η) ^ θ ≤ (2 * timeBracket ξ * timeBracket η) ^ θ :=
      Real.rpow_le_rpow (timeBracket_pos _).le (timeBracket_add_le_mul ξ η) hθ
    _ = _ := by
      rw [Real.mul_rpow (mul_nonneg (by norm_num) (timeBracket_pos ξ).le) (timeBracket_pos _).le,
        Real.mul_rpow (by norm_num) (timeBracket_pos _).le]

end WaveTurbulence.Fourier
