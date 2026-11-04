/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialNormParameterIntegral

/-! # Spatial norms of literal spectral integrals with a scalar kernel -/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional transport through a scalar spectral multiplier. The conclusion integrates its
actual size; its uniform bound is used only to justify finite differentiation under the integral. -/
theorem spatialNorm_spectralIntegral_le {d N M : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (A : Mom d → U → ℂ) (v : U → ℝ) (ψ : U → ℂ)
    (hA : ∀ u, ContDiff ℝ N (fun k => A k u))
    (hmeas : ∀ j ≤ N, ∀ k, AEStronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A k u) k) μ)
    (hv : Integrable v μ) (hvn : ∀ u, 0 ≤ v u)
    (hb : ∀ j ≤ N, ∀ k u, Fourier.momentumBracket k ^ M *
      ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ≤ v u)
    (hψ : AEStronglyMeasurable ψ μ) {H : ℝ} (hψb : ∀ u, ‖ψ u‖ ≤ H) :
    Fourier.spatialNorm N M (fun k => ∫ u, ψ u * A k u ∂μ) ≤
      ∫⁻ u, ENNReal.ofReal (v u) * ‖ψ u‖ₑ ∂μ := by
  let B := fun k u => ψ u • A k u
  have hB (u : U) : ContDiff ℝ N (fun k => B k u) := (hA u).const_smul (ψ u)
  have he (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U) :
      iteratedFDeriv ℝ j (fun k => B k u) k = ψ u • iteratedFDeriv ℝ j (fun k => A k u) k :=
    iteratedFDeriv_const_smul_apply' ((hA u).of_le (by exact_mod_cast hj)).contDiffAt
  have hmB (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => B k u) k) μ := by
    simp_rw [he j hj k]
    exact hψ.smul (hmeas j hj k)
  have hi : Integrable (fun u => ‖ψ u‖ * v u) μ :=
    hv.bdd_mul hψ.norm (ae_of_all _ (fun u => by simpa only [norm_norm] using hψb u))
  have hbound (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U) :
      Fourier.momentumBracket k ^ M * ‖iteratedFDeriv ℝ j (fun k => B k u) k‖ ≤ ‖ψ u‖ * v u := by
    rw [he j hj k u, norm_smul]
    calc
      _ = ‖ψ u‖ * (Fourier.momentumBracket k ^ M * ‖iteratedFDeriv ℝ j (fun k => A k u) k‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj k u) (norm_nonneg _)
  have hb' := spatialNorm_integral_le_of_uniform_derivative_envelope μ B (fun u => ‖ψ u‖ * v u)
    hB hmB hi hbound
  change Fourier.spatialNorm N M (fun k => ∫ u, B k u ∂μ) ≤ _
  apply hb'.trans_eq
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun u => mul_nonneg (norm_nonneg _) (hvn u)))]
  apply lintegral_congr
  intro u
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_comm]

end WaveTurbulence.Incoh
