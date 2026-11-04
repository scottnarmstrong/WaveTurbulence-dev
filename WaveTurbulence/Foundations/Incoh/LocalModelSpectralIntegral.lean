/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalModelParameterIntegral
public import WaveTurbulence.Frozen.Defs.Mom

/-! # Actual spatial derivatives of locally modelled spectral integrals -/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- Conditional actual finite-smoothness transport for locally modelled amplitudes and a bounded
scalar spectral multiplier. The integral derivative identity is proved, not assumed. -/
theorem localModel_spectralIntegral_derivatives {d N : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (A : Mom d → U → ℂ) (A₀ : Mom d → Mom d → U → ℂ)
    (v : Mom d → ℕ → U → ℝ)
    (hloc : ∀ p, ∀ᶠ k in 𝓝 p, ∀ u, A k u = A₀ p k u)
    (hA₀ : ∀ p u, ContDiff ℝ N (fun k => A₀ p k u))
    (hm : ∀ p j, j ≤ N → ∀ k, AEStronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A₀ p k u) k) μ)
    (hv : ∀ p j, j ≤ N → Integrable (v p j) μ)
    (hb : ∀ p j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => A₀ p k u) k‖ ≤ v p j u)
    (ψ : U → ℂ) (hψ : AEStronglyMeasurable ψ μ) {H : ℝ} (hH : 0 ≤ H)
    (hψb : ∀ u, ‖ψ u‖ ≤ H) :
    ContDiff ℝ N (fun k => ∫ u, ψ u * A k u ∂μ) ∧
      ∀ j ≤ N, ∀ k, iteratedFDeriv ℝ j (fun k => ∫ u, ψ u * A k u ∂μ) k =
        ∫ u, ψ u • iteratedFDeriv ℝ j (fun k => A k u) k ∂μ := by
  let B := fun k u => ψ u • A k u
  let B₀ := fun p k u => ψ u • A₀ p k u
  let w := fun p j u => H * v p j u
  have hlocB (p : Mom d) : ∀ᶠ k in 𝓝 p, ∀ u, B k u = B₀ p k u :=
    (hloc p).mono (fun k hk u => by dsimp only [B, B₀]; rw [hk u])
  have hCB (p : Mom d) (u : U) : ContDiff ℝ N (fun k => B₀ p k u) :=
    (hA₀ p u).const_smul (ψ u)
  have he (p : Mom d) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U) :
      iteratedFDeriv ℝ j (fun k => B₀ p k u) k = ψ u • iteratedFDeriv ℝ j (fun k => A₀ p k u) k :=
    iteratedFDeriv_const_smul_apply' ((hA₀ p u).of_le (by exact_mod_cast hj)).contDiffAt
  have hmB (p : Mom d) (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => B₀ p k u) k) μ := by
    simp_rw [he p j hj k]
    exact hψ.smul (hm p j hj k)
  have hvB (p : Mom d) (j : ℕ) (hj : j ≤ N) : Integrable (w p j) μ := (hv p j hj).const_mul H
  have hbB (p : Mom d) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U) :
      ‖iteratedFDeriv ℝ j (fun k => B₀ p k u) k‖ ≤ w p j u := by
    rw [he p j hj k u, norm_smul]
    exact mul_le_mul (hψb u) (hb p j hj k u) (norm_nonneg _) hH
  have hCA (u : U) : ContDiff ℝ N (fun k => A k u) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hA₀ p u).contDiffAt.congr_of_eventuallyEq ((hloc p).mono (fun k hk => hk u))
  refine ⟨contDiff_integral_of_local_models μ N B B₀ w hlocB hCB hmB hvB hbB, ?_⟩
  intro j hj k
  change iteratedFDeriv ℝ j (fun k => ∫ u, B k u ∂μ) k = _
  rw [iteratedFDeriv_integral_of_local_models μ N B B₀ w hlocB hCB hmB hvB hbB j hj k]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  exact iteratedFDeriv_const_smul_apply' ((hCA u).of_le (by exact_mod_cast hj)).contDiffAt

end WaveTurbulence.Incoh
