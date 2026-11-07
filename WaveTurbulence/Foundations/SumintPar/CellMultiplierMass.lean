/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CellInverseExponential
public import WaveTurbulence.Foundations.SumintPar.ScalarProductMass
public import WaveTurbulence.Foundations.SumintPar.TensorScalarMass

/-!
# Uniform weighted Fourier mass of the actual compact cell multiplier

Scalar dilation costs h inverse and cell translation costs nothing.
The scalar product estimate and exact tensor factorization therefore
give a fixed step-dependent constant times h inverse, independently
of the cell center and of the number of source inputs.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- The fixed scalar-mass constant for the inverse exponential and source partition profile. -/
@[expose] noncomputable def cellMultiplierMassConstant (N : ℕ) : ℝ≥0∞ :=
  2*scalarFourierMass timePartitionScalar*
    ∏ k : Fin 3, scalarFourierMass (timeInverseExpScalar N (if k = 0 then 1 else -1))

/-- The actual compact cell multiplier has the uniform h-inverse weighted Fourier norm. -/
theorem timeFourierNorm_cellInverseExponential_le (N : ℕ) {h θ : ℝ}
    (hh : h ∈ Ioc (0:ℝ) 1) (hθ : θ ≤ 1) (j : ℤ) :
    Fourier.timeFourierNorm θ (cellInverseExponential N h j) ≤
      cellMultiplierMassConstant N*ENNReal.ofReal h⁻¹ := by
  have hκ : cellInverseExponential N h j = fun z => ∏ k, cellInverseExponentialFactor N h j k (z k) :=
    funext (cellInverseExponential_eq_tensor N h j)
  rw [hκ]
  apply (timeFourierNorm_tensor_le_scalarMass hθ _ (integrable_cellInverseExponentialFactor N h j)).trans
  have hb (k : Fin 3) : scalarFourierMass (cellInverseExponentialFactor N h j k) ≤
      if k = 0 then 2*scalarFourierMass (timeInverseExpScalar N 1)*
        (ENNReal.ofReal h⁻¹*scalarFourierMass timePartitionScalar)
      else scalarFourierMass (timeInverseExpScalar N (-1)) := by
    by_cases hk : k = 0
    · subst k
      have he : cellInverseExponentialFactor N h j 0 =
          fun t => timeInverseExpScalar N 1 t*(timeCellProfile h j t:ℂ) := by funext t; rfl
      rw [ite_eq_left rfl,he]
      exact (scalarFourierMass_mul_le (hasCompactSupport_timeInverseExpScalar N 1)
        (contDiff_timeInverseExpScalar N 1) (hasCompactSupport_complex_timeCellProfile hh.1 j)
        (contDiff_complex_timeCellProfile h j)).trans
          (mul_le_mul' le_rfl (scalarFourierMass_timeCellProfile_le hh j))
    · have he : cellInverseExponentialFactor N h j k = timeInverseExpScalar N (-1) := by
        funext t
        simp only [cellInverseExponentialFactor,ite_eq_right hk,mul_one]
      rw [ite_eq_right hk,he]
  apply (Finset.prod_le_prod (fun k _ => hb k)).trans_eq
  unfold cellMultiplierMassConstant
  norm_num only [Fin.prod_univ_three,Fin.isValue,ite_true,show (1:Fin 3) ≠ 0 by decide,
    show (2:Fin 3) ≠ 0 by decide,ite_false]
  ring

/-- At every multiplier exponent of absolute value at most one, the actual cell cutoff costs a uniform h-inverse factor. -/
theorem cutoffMultiplierConstant_cell_le (N : ℕ) {h θ : ℝ}
    (hh : h ∈ Ioc (0:ℝ) 1) (hθ : |θ| ≤ 1) (j : ℤ) :
    Fourier.cutoffMultiplierConstant θ (cellInverseExponential N h j) ≤
      (2*cellMultiplierMassConstant N)*ENNReal.ofReal h⁻¹ := by
  have htwo : ENNReal.ofReal ((2:ℝ)^|θ|) ≤ 2 := by
    apply (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hθ)).trans_eq
    norm_num
  exact (mul_le_mul' htwo (timeFourierNorm_cellInverseExponential_le N hh hθ j)).trans_eq (by simp only [mul_assoc])

end WaveTurbulence.SumintPar
