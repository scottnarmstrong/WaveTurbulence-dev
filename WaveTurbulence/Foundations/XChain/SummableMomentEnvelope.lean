/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real
/-! An integrable absolute-moment envelope justifies every decoration-series interchange. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem summable_integral_norm_of_finite_sum_bound {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : α → Ω → ℂ) (hI : ∀ a, Integrable (F a) μ)
    (M : Ω → ℝ) (hM : Integrable M μ)
    (hbound : ∀ u : Finset α, ∀ᵐ ω ∂μ, ∑ a ∈ u, ‖F a ω‖ ≤ M ω) :
    Summable (fun a => ∫ ω, ‖F a ω‖ ∂μ) := by
  apply summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro u
  have hsum := integral_finsetSum u (fun a _ => (hI a).norm)
  rw [← hsum]
  exact integral_mono_ae (integrable_finsetSum u (fun a _ => (hI a).norm)) hM (hbound u)

end WaveTurbulence.Induct
