/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.IteratedDerivativeIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-! # Spatial norms of actual dominated parameter integrals

Conditional transport used in Proposition 5.1 assembly. The derivative
and weight bounds are on the actual amplitude, not formal derivatives.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional weighted spatial norm bound for a parameter integral. -/
theorem spatialNorm_integral_le_of_uniform_derivative_envelope {d N M : ℕ} {U : Type*}
    [MeasurableSpace U] (μ : Measure U) (A : Mom d → U → ℂ) (v : U → ℝ)
    (hA : ∀ u, ContDiff ℝ N (fun k => A k u))
    (hmeas : ∀ j ≤ N, ∀ k, AEStronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A k u) k) μ)
    (hv : Integrable v μ)
    (hb : ∀ j ≤ N, ∀ k u, Fourier.momentumBracket k ^ M *
      ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ≤ v u) :
    Fourier.spatialNorm N M (fun k => ∫ u, A k u ∂μ) ≤ ENNReal.ofReal (∫ u, v u ∂μ) := by
  have hnorm (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U) :
      ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ≤ v u := by
    have hw : 1 ≤ Fourier.momentumBracket k ^ M := one_le_pow₀ (one_le_momentumBracket k)
    exact (le_mul_of_one_le_left (norm_nonneg _) hw).trans (hb j hj k u)
  have hC := contDiff_integral_of_uniform_derivative_bounds μ N A (fun _ => v) hA hmeas
    (fun _ _ => hv) hnorm
  rw [Fourier.spatialNorm, ite_eq_left (Or.inr hC)]
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro ρ
  unfold Fourier.momentumSupNorm
  apply iSup_le
  intro k
  have hi : Integrable (fun u => iteratedFDeriv ℝ j (fun k => A k u) k) μ :=
    hv.mono' (hmeas j hj k) (ae_of_all _ (fun u => hnorm j hj k u))
  have he := congrFun (iteratedFDeriv_integral_of_uniform_derivative_bounds μ N A (fun _ => v)
    hA hmeas (fun _ _ => hv) hnorm j hj) k
  have hcoord : ‖Fourier.momentumDerivative ρ (fun k => ∫ u, A k u ∂μ) k‖ ≤
      ‖iteratedFDeriv ℝ j (fun k => ∫ u, A k u ∂μ) k‖ := by
    simpa only [Fourier.momentumDerivative, EuclideanSpace.single, PiLp.norm_single,
      norm_one, Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ j (fun k => ∫ u, A k u ∂μ) k).le_opNorm
        (fun i => EuclideanSpace.single (ρ i) 1)
  have hw : 0 ≤ Fourier.momentumBracket k ^ M :=
    pow_nonneg (zero_le_one.trans (one_le_momentumBracket k)) M
  have hreal : Fourier.momentumBracket k ^ M *
      ‖Fourier.momentumDerivative ρ (fun k => ∫ u, A k u ∂μ) k‖ ≤ ∫ u, v u ∂μ := by
    calc
      _ ≤ Fourier.momentumBracket k ^ M *
          ‖iteratedFDeriv ℝ j (fun k => ∫ u, A k u ∂μ) k‖ := mul_le_mul_of_nonneg_left hcoord hw
      _ = Fourier.momentumBracket k ^ M * ‖∫ u, iteratedFDeriv ℝ j (fun k => A k u) k ∂μ‖ := by rw [he]
      _ ≤ Fourier.momentumBracket k ^ M * (∫ u, ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ∂μ) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw
      _ = ∫ u, Fourier.momentumBracket k ^ M * ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ∂μ :=
        (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono (hi.norm.const_mul _) hv (fun u => hb j hj k u)
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw]
  exact ENNReal.ofReal_le_ofReal hreal

end WaveTurbulence.Incoh
