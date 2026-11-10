/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeOperatorRegularity
import Mathlib.Tactic

/-!
# Difference phases and simultaneous time translation

The phases in TARGET A.3 have balanced coefficients: their sum is zero.
They have modulus one and are constant under simultaneous translation,
regardless of the size or momentum dependence of their coefficients.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- A linear oscillatory phase in the paper's `exp(iφ)` convention. -/
@[expose] noncomputable def linearTimePhase {n : ℕ} (a v : Fin n → ℝ) : ℂ :=
  Complex.exp (((∑ j, a j * v j) : ℝ) * Complex.I)

/-- Real linear phases have modulus one. -/
@[simp] theorem norm_linearTimePhase {n : ℕ} (a v : Fin n → ℝ) :
    ‖linearTimePhase a v‖ = 1 := by simp [linearTimePhase, Complex.norm_exp]

/-- Real linear phases are smooth. -/
theorem linearTimePhase_contDiff {n : ℕ} (a : Fin n → ℝ) :
    ContDiff ℝ ∞ (linearTimePhase a) :=
  contDiff_exp_real_phase (by fun_prop)

/-- Balanced coefficients make the phase invariant under simultaneous translation. -/
theorem linearTimePhase_translate {n : ℕ} {a : Fin n → ℝ} (ha : ∑ j, a j = 0)
    (v : Fin n → ℝ) (c : ℝ) : linearTimePhase a (fun j => v j + c) = linearTimePhase a v := by
  unfold linearTimePhase
  congr 2
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ha, zero_mul, add_zero]

/-- Simultaneous translation differentiates a balanced phase to zero. -/
theorem hasDerivAt_linearTimePhase_diagonal {n : ℕ} {a : Fin n → ℝ}
    (ha : ∑ j, a j = 0) (v : Fin n → ℝ) (c : ℝ) :
    HasDerivAt (fun u => linearTimePhase a (fun j => v j + u)) 0 c := by
  have he : (fun u => linearTimePhase a (fun j => v j + u)) = fun _ : ℝ => linearTimePhase a v :=
    funext (fun u => linearTimePhase_translate ha v u)
  rw [he]
  exact hasDerivAt_const c _

end WaveTurbulence.Fourier
