/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InverseExponentialCutoff
public import WaveTurbulence.Foundations.SumintPar.TimeCellScalarMass

/-!
# The explicit compact cell multiplier restoring the original source integral

The fixed inverse exponential is multiplied by the actual scalar time
partition profile in the first coordinate. Its exact tensor factors
are retained for the uniform Fourier mass estimate.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical ContDiff
namespace WaveTurbulence.SumintPar

/-- The explicit inverse-exponential multiplier localized to one actual source time cell. -/
@[expose] noncomputable def cellInverseExponential (N : ℕ) (h : ℝ) (j : ℤ) (z : Fin 3 → ℝ) : ℂ :=
  inverseExponentialCutoff N z*(timeCellProfile h j (z 0):ℂ)

/-- The actual cell multiplier is compactly supported in all native time coordinates. -/
theorem hasCompactSupport_cellInverseExponential (N : ℕ) (h : ℝ) (j : ℤ) :
    HasCompactSupport (cellInverseExponential N h j) :=
  (hasCompactSupport_inverseExponentialCutoff N).mul_right

/-- The actual cell multiplier has ordinary C-infinity smoothness. -/
theorem contDiff_cellInverseExponential (N : ℕ) (h : ℝ) (j : ℤ) :
    ContDiff ℝ ∞ (cellInverseExponential N h j) :=
  (contDiff_inverseExponentialCutoff N).mul
    ((contDiff_complex_timeCellProfile h j).comp (by fun_prop))

/-- The literal scalar tensor factors of the actual cell multiplier. -/
@[expose] noncomputable def cellInverseExponentialFactor (N : ℕ) (h : ℝ) (j : ℤ) (k : Fin 3) (t : ℝ) : ℂ :=
  timeInverseExpScalar N (if k = 0 then 1 else -1) t * (if k = 0 then (timeCellProfile h j t:ℂ) else 1)

/-- The cell multiplier equals the product of its literal scalar factors. -/
theorem cellInverseExponential_eq_tensor (N : ℕ) (h : ℝ) (j : ℤ) (z : Fin 3 → ℝ) :
    cellInverseExponential N h j z = ∏ k, cellInverseExponentialFactor N h j k (z k) := by
  unfold cellInverseExponential cellInverseExponentialFactor inverseExponentialCutoff
  rw [Finset.prod_mul_distrib]
  congr 1
  simp

/-- Each scalar tensor factor is compactly supported. -/
theorem hasCompactSupport_cellInverseExponentialFactor (N : ℕ) (h : ℝ) (j : ℤ) (k : Fin 3) :
    HasCompactSupport (cellInverseExponentialFactor N h j k) :=
  (hasCompactSupport_timeInverseExpScalar N _).mul_right

/-- Each scalar tensor factor has ordinary C-infinity smoothness. -/
theorem contDiff_cellInverseExponentialFactor (N : ℕ) (h : ℝ) (j : ℤ) (k : Fin 3) :
    ContDiff ℝ ∞ (cellInverseExponentialFactor N h j k) := by
  change ContDiff ℝ ∞ (fun t => timeInverseExpScalar N (if k = 0 then 1 else -1) t *
    (if k = 0 then (timeCellProfile h j t:ℂ) else 1))
  by_cases hk : k = 0
  · simp only [ite_eq_left hk]
    exact (contDiff_timeInverseExpScalar N 1).mul (contDiff_complex_timeCellProfile h j)
  · simp only [ite_eq_right hk,mul_one]
    exact contDiff_timeInverseExpScalar N (-1)

/-- Each scalar tensor factor is genuinely integrable. -/
theorem integrable_cellInverseExponentialFactor (N : ℕ) (h : ℝ) (j : ℤ) (k : Fin 3) :
    Integrable (cellInverseExponentialFactor N h j k) :=
  (contDiff_cellInverseExponentialFactor N h j k).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_cellInverseExponentialFactor N h j k)

end WaveTurbulence.SumintPar
