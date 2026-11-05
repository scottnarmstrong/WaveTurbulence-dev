/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantAbsoluteSeries
/-! Absolute block moments also prove absolute convergence of the cumulant series itself. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem summable_assigned_cumulant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    (s : Finset ι)
    (hS : ∀ J ⊆ s, Summable (fun a : (i : ↥J) → α i.1 =>
      ∫ ω, ‖∏ i : ↥J, F i.1 (a i) ω‖ ∂μ)) :
    Summable (fun a : (i : ↥s) → α i.1 => cumulant μ (assignedFamily F s a) s) := by
  have hP (P : Finpartition s) := summable_partitionSeriesMoment μ F P (fun B => hS B.1 (P.le B.2))
  have he : (fun a : (i : ↥s) → α i.1 => cumulant μ (assignedFamily F s a) s) =
      fun a => ∑ P : Finpartition s, ((-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ)) *
        partitionSeriesMoment μ F P a := by
    funext a
    exact cumulant_assignedFamily_eq μ F s a
  rw [he]
  exact summable_sum (fun P _ => (hP P).mul_left _)

end WaveTurbulence.Induct
