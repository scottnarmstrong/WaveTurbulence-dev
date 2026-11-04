/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.IteratedDerivativeIntegral

/-! # Finite derivative transport through locally modelled parameter integrals

The tree root partition gives a single finite cell model throughout each
momentum neighborhood. Global uniform envelopes are needed only for that
finite model, avoiding an artificial summability requirement over all roots.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

universe u

/-- Conditional smoothness transport using actual local models with genuine global derivative
envelopes. No derivative identity for the integral is assumed. -/
theorem contDiff_integral_of_local_models {E F : Type u} {U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace U] (μ : Measure U) (N : ℕ)
    (A : E → U → F) (A₀ : E → E → U → F) (v : E → ℕ → U → ℝ)
    (hloc : ∀ p, ∀ᶠ k in 𝓝 p, ∀ u, A k u = A₀ p k u)
    (hA₀ : ∀ p u, ContDiff ℝ N (fun k => A₀ p k u))
    (hm : ∀ p j, j ≤ N → ∀ k, AEStronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A₀ p k u) k) μ)
    (hv : ∀ p j, j ≤ N → Integrable (v p j) μ)
    (hb : ∀ p j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => A₀ p k u) k‖ ≤ v p j u) :
    ContDiff ℝ N (fun k => ∫ u, A k u ∂μ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hC := contDiff_integral_of_uniform_derivative_bounds μ N (A₀ p) (v p)
    (hA₀ p) (hm p) (hv p) (hb p)
  apply hC.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hloc p] with k hk
  exact integral_congr_ae (ae_of_all _ hk)

/-- Actual finite derivatives commute with the locally modelled integral. The proof uses local
agreement and the proved global-model differentiation theorem. -/
theorem iteratedFDeriv_integral_of_local_models {E F : Type u} {U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace U] (μ : Measure U) (N : ℕ)
    (A : E → U → F) (A₀ : E → E → U → F) (v : E → ℕ → U → ℝ)
    (hloc : ∀ p, ∀ᶠ k in 𝓝 p, ∀ u, A k u = A₀ p k u)
    (hA₀ : ∀ p u, ContDiff ℝ N (fun k => A₀ p k u))
    (hm : ∀ p j, j ≤ N → ∀ k, AEStronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A₀ p k u) k) μ)
    (hv : ∀ p j, j ≤ N → Integrable (v p j) μ)
    (hb : ∀ p j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => A₀ p k u) k‖ ≤ v p j u)
    (j : ℕ) (hj : j ≤ N) (p : E) :
    iteratedFDeriv ℝ j (fun k => ∫ u, A k u ∂μ) p =
      ∫ u, iteratedFDeriv ℝ j (fun k => A k u) p ∂μ := by
  have he : (fun k => ∫ u, A k u ∂μ) =ᶠ[𝓝 p] (fun k => ∫ u, A₀ p k u ∂μ) := by
    filter_upwards [hloc p] with k hk
    exact integral_congr_ae (ae_of_all _ hk)
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds,
    congrFun (iteratedFDeriv_integral_of_uniform_derivative_bounds μ N (A₀ p) (v p)
      (hA₀ p) (hm p) (hv p) (hb p) j hj) p]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  have hu : (fun k => A k u) =ᶠ[𝓝 p] (fun k => A₀ p k u) := (hloc p).mono (fun k hk => hk u)
  exact (hu.iteratedFDeriv ℝ j).self_of_nhds.symm

end WaveTurbulence.Incoh
