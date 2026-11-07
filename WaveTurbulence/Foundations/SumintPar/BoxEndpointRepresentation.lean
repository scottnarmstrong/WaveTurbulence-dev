/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ExponentialBoxFourier
public import WaveTurbulence.Foundations.SumintPar.SourceExitWeights

/-!
# Exact endpoint numerator for the actual rectangular Fourier kernel

The interval-order indicator handles the empty intersection exactly.
Both endpoint contributions then split by the measurable averaging
weights over their attaining source coordinates. The denominator is
never zero and carries exactly three inverse frequency brackets.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- One finite-interval endpoint together with the two common half-line endpoints. -/
@[expose] noncomputable def boxEndpointTerm (e u : ℝ) (ξ : Fin 3 → ℝ) : ℂ :=
  Complex.exp (exponentialRate (-1) (ξ 0)*e)*
    Complex.exp (exponentialRate 1 (ξ 1)*u)*Complex.exp (exponentialRate 1 (ξ 2)*u)

/-- The complete nonvanishing rectangular Fourier denominator. -/
@[expose] noncomputable def boxEndpointDenominator (ξ : Fin 3 → ℝ) : ℂ :=
  exponentialRate (-1) (ξ 0)*exponentialRate 1 (ξ 1)*exponentialRate 1 (ξ 2)

/-- The actual numerator, including the order indicator for an empty finite interval. -/
@[expose] noncomputable def boxEndpointNumerator (a b u : ℝ) (ξ : Fin 3 → ℝ) : ℂ :=
  if a ≤ b then boxEndpointTerm b u ξ-boxEndpointTerm a u ξ else 0

/-- The denominator is nonzero at every frequency. -/
theorem boxEndpointDenominator_ne_zero (ξ : Fin 3 → ℝ) : boxEndpointDenominator ξ ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (exponentialRate_ne_zero (by norm_num) _)
    (exponentialRate_ne_zero (by norm_num) _)) (exponentialRate_ne_zero (by norm_num) _)

/-- Exact rectangular Fourier endpoint representation, valid also for empty input intersections. -/
theorem timeFourier_exponentialBox_eq_endpoint_quotient (a b u : ℝ) (ξ : Fin 3 → ℝ) :
    Fourier.timeFourier (exponentialBox a b u) ξ =
      boxEndpointNumerator a b u ξ/boxEndpointDenominator ξ := by
  by_cases hab : a ≤ b
  · rw [timeFourier_exponentialBox,integral_exp_neg_char_Icc hab,
      integral_exp_pos_char_Iio,integral_exp_pos_char_Iio]
    unfold boxEndpointNumerator
    rw [ite_eq_left hab,div_mul_div_comm,div_mul_div_comm]
    unfold boxEndpointTerm boxEndpointDenominator
    ring
  · have he : Icc a b = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hab)
    rw [timeFourier_exponentialBox,he]
    simp [boxEndpointNumerator,hab]

/-- The actual numerator splits exactly over the attaining lower and upper source coordinates. -/
theorem source_boxEndpointNumerator_eq_weighted_sums {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (u : D.S.TVar → ℝ) (ξ : Fin 3 → ℝ) :
    boxEndpointNumerator (lowerTimeExit D hI u) (upperTimeExit D hI u) (u (firstTime D hI)) ξ =
      if lowerTimeExit D hI u ≤ upperTimeExit D hI u then
        (∑ v, (timeExitWeight D hI true v u:ℂ)*
          boxEndpointTerm (timeExitCoordinate D true v u) (u (firstTime D hI)) ξ)-
        (∑ v, (timeExitWeight D hI false v u:ℂ)*
          boxEndpointTerm (timeExitCoordinate D false v u) (u (firstTime D hI)) ξ)
      else 0 := by
  have hu := timeExit_formula_eq_weighted_sum D hI true u (fun e => boxEndpointTerm e (u (firstTime D hI)) ξ)
  have hl := timeExit_formula_eq_weighted_sum D hI false u (fun e => boxEndpointTerm e (u (firstTime D hI)) ξ)
  change boxEndpointTerm (upperTimeExit D hI u) (u (firstTime D hI)) ξ = _ at hu
  change boxEndpointTerm (lowerTimeExit D hI u) (u (firstTime D hI)) ξ = _ at hl
  unfold boxEndpointNumerator
  rw [hu,hl]

end WaveTurbulence.SumintPar
