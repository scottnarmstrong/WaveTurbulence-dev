/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CoordinateCutoff
public import WaveTurbulence.Foundations.Fourier.CutoffControl
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Simultaneous-translation derivative of a product cutoff

The finite product rule gives a frequency-independent derivative bound.
Only the scalar cutoff and its first derivative enter this amplitude bound.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The finite product-rule derivative of the coordinate cutoff along simultaneous translation. -/
@[expose] noncomputable def coordinateCutoffDiagonal {n : ℕ} (χ : ℝ → ℝ) (v : Fin n → ℝ) : ℂ :=
  ∑ j, ((deriv χ (v j) : ℝ) : ℂ) * ∏ k ∈ Finset.univ.erase j, (χ (v k) : ℂ)

/-- Uniform pointwise bound for a product of cutoff factors. -/
theorem norm_coordinateCutoff_le {n : ℕ} {χ : ℝ → ℝ} (h : CutoffControl χ) (v : Fin n → ℝ) :
    ‖coordinateCutoff χ v‖ ≤ h.bound ^ n := by
  unfold coordinateCutoff
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : Fin n, h.bound := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      simpa only [Complex.norm_real, Real.norm_eq_abs] using h.abs_le (v j)
    _ = _ := by simp

/-- The derivative of the product cutoff along a simultaneous translation. -/
theorem hasDerivAt_coordinateCutoff_diagonal {n : ℕ} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (v : Fin n → ℝ) :
    HasDerivAt (fun c : ℝ => coordinateCutoff χ (fun j => v j + c))
      (coordinateCutoffDiagonal χ v) 0 := by
  have hj (j : Fin n) : HasDerivAt (fun c : ℝ => (χ (v j + c) : ℂ))
      ((deriv χ (v j) : ℝ) : ℂ) 0 := by
    have h := (((hχ.differentiable (by simp)) (v j + (0 : ℝ))).hasDerivAt.comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add (v j))).ofReal_comp
    simpa only [Function.comp_def, add_zero, mul_one, Complex.ofReal_mul, Complex.ofReal_one] using h
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hj j)
  simpa only [coordinateCutoff, coordinateCutoffDiagonal, add_zero, smul_eq_mul, mul_comm] using hp

/-- The diagonal cutoff derivative has an explicit coarse bound through the first scalar derivative. -/
theorem norm_coordinateCutoffDiagonal_le {n : ℕ} {χ : ℝ → ℝ}
    (h : CutoffControl χ) (v : Fin n → ℝ) :
    ‖coordinateCutoffDiagonal χ v‖ ≤ (n : ℝ) * h.bound ^ (n + 1) := by
  classical
  unfold coordinateCutoffDiagonal
  calc
    _ ≤ ∑ j : Fin n, ‖((deriv χ (v j) : ℝ) : ℂ) *
        ∏ k ∈ Finset.univ.erase j, (χ (v k) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, h.bound ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro j _
      have hd : ‖((deriv χ (v j) : ℝ) : ℂ)‖ ≤ h.bound := by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using h.abs_deriv_le (v j)
      have hp : ‖∏ k ∈ Finset.univ.erase j, (χ (v k) : ℂ)‖ ≤ h.bound ^ n := by
        rw [norm_prod]
        calc
          _ ≤ ∏ _k ∈ (Finset.univ : Finset (Fin n)).erase j, h.bound := by
            apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            intro k _
            simpa only [Complex.norm_real, Real.norm_eq_abs] using h.abs_le (v k)
          _ ≤ _ := by
            rw [Finset.prod_const]
            apply pow_le_pow_right₀ h.one_le_bound
            simp
      rw [norm_mul]
      exact (mul_le_mul hd hp (norm_nonneg _) (by linarith [h.one_le_bound])).trans_eq
        (by rw [pow_succ]; ring)
    _ = _ := by simp

end WaveTurbulence.Fourier
