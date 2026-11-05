/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.IndependentDecorationSums
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Countable multilinearity of a finite product moment under absolute-moment summability. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem integral_prod_tsum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    (hI : ∀ a : (i : ι) → α i, Integrable (fun ω => ∏ i, F i (a i) ω) μ)
    (hS : Summable (fun a : (i : ι) → α i => ∫ ω, ‖∏ i, F i (a i) ω‖ ∂μ)) :
    (∫ ω, ∏ i, ∑' a, F i a ω ∂μ) = ∑' a : (i : ι) → α i, ∫ ω, ∏ i, F i (a i) ω ∂μ := by
  have he : (fun ω => ∏ i, ∑' a, F i a ω) = fun ω => ∑' a : (i : ι) → α i, ∏ i, F i (a i) ω := by
    funext ω
    exact (tsum_independent_prod (fun i a => F i a ω)).symm
  rw [he]
  exact (integral_tsum_of_summable_integral_norm hI hS).symm

end WaveTurbulence.Induct
