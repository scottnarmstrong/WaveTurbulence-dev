/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantPiTsum
public import WaveTurbulence.Foundations.XChain.IndependentSummability
/-! The cumulant decoration expansion needs only absolute block moments, with no hidden sum gate. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem summable_partitionSeriesMoment {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    {s : Finset ι} (P : Finpartition s)
    (hS : ∀ B : P.parts, Summable (fun a : (i : ↥B.1) → α i.1 =>
      ∫ ω, ‖∏ i : ↥B.1, F i.1 (a i) ω‖ ∂μ)) :
    Summable (partitionSeriesMoment μ F P) := by
  have hb (B : P.parts) : Summable (blockSeriesMoment μ F B.1) :=
    (hS B).of_norm_bounded (fun a => norm_integral_le_integral_norm _)
  have hp := summable_independent_prod (fun B : P.parts => blockSeriesMoment μ F B.1) hb
  have he : Summable (fun a : (i : ↥s) → α i.1 =>
      ∏ B : P.parts, blockSeriesMoment μ F B.1 (partitionLabelEquiv P α a B)) :=
    ((partitionLabelEquiv P α).summable_iff
      (f := fun b : (B : P.parts) → (i : ↥B.1) → α i.1 =>
        ∏ B : P.parts, blockSeriesMoment μ F B.1 (b B))).mpr hp
  apply he.congr
  intro a
  apply prod_congr rfl
  intro B _
  exact congrArg (blockSeriesMoment μ F B.1)
    (funext (fun i => partitionLabelEquiv_apply P α a B i))

theorem cumulant_pi_tsum_of_absolute_moments {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    (s : Finset ι)
    (hI : ∀ J ⊆ s, ∀ a : (i : ↥J) → α i.1,
      Integrable (fun ω => ∏ i : ↥J, F i.1 (a i) ω) μ)
    (hS : ∀ J ⊆ s, Summable (fun a : (i : ↥J) → α i.1 =>
      ∫ ω, ‖∏ i : ↥J, F i.1 (a i) ω‖ ∂μ)) :
    cumulant μ (fun i ω => ∑' a, F i a ω) s =
      ∑' a : (i : ↥s) → α i.1, cumulant μ (assignedFamily F s a) s :=
  cumulant_pi_tsum μ F s hI hS (fun P =>
    summable_partitionSeriesMoment μ F P (fun B => hS B.1 (P.le B.2)))

end WaveTurbulence.Induct
