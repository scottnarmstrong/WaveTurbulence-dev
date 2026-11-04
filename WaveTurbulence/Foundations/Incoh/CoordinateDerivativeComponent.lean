/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.NestedDerivativeNorm
public import WaveTurbulence.Foundations.Incoh.SpatialInputBounds

/-!
# Actual coordinate derivative components with finite smoothness

Evaluation of a multilinear derivative on coordinate unit vectors is a
norm-at-most-one linear map. Higher derivatives of this actual component
are controlled by the original total derivative.
-/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Literal coordinate-unit-vector evaluation of a multilinear derivative. -/
@[expose] def coordinateDerivativeEvaluation {d j : ℕ} (ρ : Fin j → Fin d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => Mom d) ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun A => A (fun i => EuclideanSpace.single (ρ i) 1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1 (fun A => by
        change ‖A (fun i => EuclideanSpace.single (ρ i) 1)‖ ≤ 1 * ‖A‖
        simpa only [EuclideanSpace.single, PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one, one_mul] using
          A.le_opNorm (fun i => EuclideanSpace.single (ρ i) 1))

/-- Coordinate derivative evaluation has no operator-norm loss. -/
theorem norm_coordinateDerivativeEvaluation_le {d j : ℕ} (ρ : Fin j → Fin d) :
    ‖coordinateDerivativeEvaluation ρ‖ ≤ 1 := by
  apply (coordinateDerivativeEvaluation ρ).opNorm_le_bound zero_le_one
  intro A
  change ‖A (fun i => EuclideanSpace.single (ρ i) 1)‖ ≤ 1 * ‖A‖
  simpa only [EuclideanSpace.single, PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one, one_mul] using
    A.le_opNorm (fun i => EuclideanSpace.single (ρ i) 1)

/-- An actual coordinate derivative retains every source derivative still available. -/
theorem contDiff_momentumDerivative {d N j K : ℕ} {f : Mom d → ℂ}
    (hf : ContDiff ℝ N f) (h : j + K ≤ N) (ρ : Fin j → Fin d) :
    ContDiff ℝ K (Fourier.momentumDerivative ρ f) := by
  change ContDiff ℝ K (coordinateDerivativeEvaluation ρ ∘ iteratedFDeriv ℝ j f)
  exact (coordinateDerivativeEvaluation ρ).contDiff.comp
    (hf.iteratedFDeriv_right (by exact_mod_cast (show K + j ≤ N by omega)))

/-- Higher actual operator derivatives of a coordinate component have no extra norm loss. -/
theorem norm_iteratedFDeriv_momentumDerivative_le {d N j k : ℕ} {f : Mom d → ℂ}
    (hf : ContDiff ℝ N f) (h : j + k ≤ N) (ρ : Fin j → Fin d) (x : Mom d) :
    ‖iteratedFDeriv ℝ k (Fourier.momentumDerivative ρ f) x‖ ≤
      ‖iteratedFDeriv ℝ (j + k) f x‖ := by
  have hc : ContDiff ℝ k (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show k + j ≤ N by omega))
  change ‖iteratedFDeriv ℝ k (coordinateDerivativeEvaluation ρ ∘ iteratedFDeriv ℝ j f) x‖ ≤ _
  calc
    _ ≤ ‖coordinateDerivativeEvaluation ρ‖ * ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ j f) x‖ :=
      (coordinateDerivativeEvaluation ρ).norm_iteratedFDeriv_comp_left hc.contDiffAt (le_refl (k : ℕ∞ω))
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ j f) x‖ :=
      mul_le_mul_of_nonneg_right (norm_coordinateDerivativeEvaluation_le ρ) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact norm_iteratedFDeriv_iteratedFDeriv_le hf j k h x

/-- The same bound holds after evaluating a second coordinate derivative word. -/
theorem norm_momentumDerivative_momentumDerivative_le {d N j k : ℕ} {f : Mom d → ℂ}
    (hf : ContDiff ℝ N f) (h : j + k ≤ N) (ρ : Fin j → Fin d) (σ : Fin k → Fin d) (x : Mom d) :
    ‖Fourier.momentumDerivative σ (Fourier.momentumDerivative ρ f) x‖ ≤
      ‖iteratedFDeriv ℝ (j + k) f x‖ := by
  apply le_trans _ (norm_iteratedFDeriv_momentumDerivative_le hf h ρ x)
  simpa only [Fourier.momentumDerivative, EuclideanSpace.single, PiLp.norm_single, norm_one,
    Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ k (Fourier.momentumDerivative ρ f) x).le_opNorm
        (fun i => EuclideanSpace.single (σ i) 1)

end WaveTurbulence.Incoh
