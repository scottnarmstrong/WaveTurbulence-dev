/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BalancedPhase
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoffDerivative
public import WaveTurbulence.Foundations.Fourier.DirectionalFourierMoments

/-!
# A product of coordinate factors and its common-clock derivative

Unlike a mixed derivative in all coordinates, the common-clock derivative
uses each factor's first derivative only. This is the landed moment route
for hard rectangular bounds on every selected tree clock.
-/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Independent scalar factors in all selected clocks. -/
@[expose] def coordinateFactorProduct {m : ℕ} (f : Fin m → ℝ → ℝ) (v : Fin m → ℝ) : ℂ :=
  ∏ j, (f j (v j) : ℂ)

/-- Pointwise scalar bounds tensorize over the selected clocks. -/
theorem norm_coordinateFactorProduct_le {m : ℕ} (f : Fin m → ℝ → ℝ)
    {C : ℝ} (hf : ∀ j x, ‖f j x‖ ≤ C) (v : Fin m → ℝ) :
    ‖coordinateFactorProduct f v‖ ≤ C ^ m := by
  rw [coordinateFactorProduct, norm_prod]
  calc
    _ ≤ ∏ _j : Fin m, C := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      simpa only [Complex.norm_real] using hf j (v j)
    _ = _ := by simp

/-- The actual finite product-rule derivative along common clock translation. -/
@[expose] def coordinateFactorDiagonal {m : ℕ} (f : Fin m → ℝ → ℝ) (v : Fin m → ℝ) : ℂ :=
  ∑ j, ((deriv (f j) (v j) : ℝ) : ℂ) * ∏ k ∈ Finset.univ.erase j, (f k (v k) : ℂ)

@[fun_prop] theorem contDiff_coordinateFactorProduct {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) : ContDiff ℝ ∞ (coordinateFactorProduct f) := by
  apply contDiff_prod
  intro j _
  exact Complex.ofRealCLM.contDiff.comp ((hf j).comp (by fun_prop))

/-- The derivative is obtained by differentiating each scalar factor once. -/
theorem hasDerivAt_coordinateFactorProduct_diagonal {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (v : Fin m → ℝ) :
    HasDerivAt (fun c : ℝ => coordinateFactorProduct f (fun j => v j + c))
      (coordinateFactorDiagonal f v) 0 := by
  have hj (j : Fin m) : HasDerivAt (fun c : ℝ => (f j (v j + c) : ℂ))
      ((deriv (f j) (v j) : ℝ) : ℂ) 0 := by
    have h := ((((hf j).differentiable (by simp)) (v j + (0 : ℝ))).hasDerivAt.comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add (v j))).ofReal_comp
    simpa only [Function.comp_def, add_zero, mul_one, Complex.ofReal_mul, Complex.ofReal_one] using h
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hj j)
  simpa only [coordinateFactorProduct, coordinateFactorDiagonal, add_zero, smul_eq_mul, mul_comm] using hp

/-- Add an arbitrary balanced phase and a smooth translation-invariant weight. -/
@[expose] def invariantProductAmplitude {m : ℕ} (f : Fin m → ℝ → ℝ)
    (phase : Fin m → ℝ) (H : (Fin m → ℝ) → ℂ) (v : Fin m → ℝ) : ℂ :=
  coordinateFactorProduct f v * Fourier.linearTimePhase phase v * H v

@[fun_prop] theorem contDiff_invariantProductAmplitude {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (phase : Fin m → ℝ) {H : (Fin m → ℝ) → ℂ}
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (invariantProductAmplitude f phase H) :=
  ((contDiff_coordinateFactorProduct hf).mul (Fourier.linearTimePhase_contDiff phase)).mul hH

/-- Balanced phases and translation-invariant ordering weights contribute no diagonal derivative. -/
theorem timeDirectionalDerivative_invariantProductAmplitude {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) {phase : Fin m → ℝ} (hphase : ∑ j, phase j = 0)
    {H : (Fin m → ℝ) → ℂ} (hH : ContDiff ℝ ∞ H)
    (hshift : ∀ v c, H (fun j => v j + c) = H v) (v : Fin m → ℝ) :
    Fourier.timeDirectionalDerivative (fun _ => 1) (invariantProductAmplitude f phase H) v =
      coordinateFactorDiagonal f v * Fourier.linearTimePhase phase v * H v := by
  have hHC : HasDerivAt (fun c : ℝ => H (fun j => v j + c)) 0 0 := by
    rw [show (fun c : ℝ => H (fun j => v j + c)) = fun _ => H v from funext (hshift v)]
    exact hasDerivAt_const 0 _
  have hp := ((hasDerivAt_coordinateFactorProduct_diagonal hf v).mul
    (Fourier.hasDerivAt_linearTimePhase_diagonal hphase v 0)).mul hHC
  have hs := Fourier.hasDerivAt_diagonal_translation
    ((contDiff_invariantProductAmplitude hf phase hH).differentiable (by simp)) v
  simpa only [invariantProductAmplitude, add_zero, Pi.mul_apply, mul_zero, zero_add] using hs.unique hp

end WaveTurbulence.Incoh
