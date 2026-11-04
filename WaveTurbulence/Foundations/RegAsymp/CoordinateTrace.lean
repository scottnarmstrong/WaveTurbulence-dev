/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.MCSob

/-! # One-coordinate traces for the Wick exceptional set

The trace costs one derivative, independently of the number of remaining
coefficient variables. This avoids the dimension-dependent full Sobolev bound.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory
open scoped ENNReal

/-- Restriction of one variable to a point is controlled by one derivative
in that variable, with no dimension factor. -/
theorem lintegral_coordinate_trace_le {X E : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : ℝ × X → E} (x : ℝ)
    (hs : ∀ β, ContDiff ℝ 1 (fun r => H (r,β)))
    (hm : Measurable (fun p : ℝ × X => ‖H p‖ₑ+‖deriv (fun r => H (r,p.2)) p.1‖ₑ)) :
    (∫⁻ β, ‖H (x,β)‖ₑ ∂μ) ≤
      ∫⁻ p : ℝ × X, (‖H p‖ₑ+‖deriv (fun r => H (r,p.2)) p.1‖ₑ) ∂(volume.prod μ) := by
  calc
    _ ≤ ∫⁻ β, (∫⁻ r : ℝ, (‖H (r,β)‖ₑ+‖deriv (fun s => H (s,β)) r‖ₑ)) ∂μ := by
      apply lintegral_mono
      intro β
      exact (ClassJR.enorm_le_lintegral_Icc (hs β) x).trans (setLIntegral_le_lintegral _ _)
    _ = ∫⁻ r : ℝ, ∫⁻ β, (‖H (r,β)‖ₑ+‖deriv (fun s => H (s,β)) r‖ₑ) ∂μ :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = _ := (lintegral_prod _ hm.aemeasurable).symm

end WaveTurbulence.RegAsymp
