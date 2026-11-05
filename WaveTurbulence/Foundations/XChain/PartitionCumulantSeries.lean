/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantSeriesSummability
/-! Absolute convergence of products of input cumulants on the blocks of a fixed partition. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def partitionCumulantProduct {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    {s : Finset ι} (P : Finpartition s) (a : (i : ↥s) → α i.1) : ℂ :=
  ∏ B : P.parts, cumulant μ (assignedFamily F B.1 (fun i => a ⟨i.1, P.le B.2 i.2⟩)) B.1

theorem summable_partitionCumulantProduct {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    {s : Finset ι} (P : Finpartition s)
    (hS : ∀ J ⊆ s, Summable (fun a : (i : ↥J) → α i.1 =>
      ∫ ω, ‖∏ i : ↥J, F i.1 (a i) ω‖ ∂μ)) :
    Summable (partitionCumulantProduct μ F P) := by
  let f := fun (B : P.parts) (a : (i : ↥B.1) → α i.1) => cumulant μ (assignedFamily F B.1 a) B.1
  have hb (B : P.parts) : Summable (f B) :=
    summable_assigned_cumulant μ F B.1 (fun J hJ => hS J (hJ.trans (P.le B.2)))
  have hp := summable_independent_prod f hb
  have he : Summable (fun a : (i : ↥s) → α i.1 => ∏ B : P.parts, f B (partitionLabelEquiv P α a B)) :=
    ((partitionLabelEquiv P α).summable_iff
      (f := fun b : (B : P.parts) → (i : ↥B.1) → α i.1 => ∏ B : P.parts, f B (b B))).mpr hp
  apply he.congr
  intro a
  apply prod_congr rfl
  intro B _
  exact congrArg (f B) (funext (fun i => partitionLabelEquiv_apply P α a B i))

end WaveTurbulence.Induct
