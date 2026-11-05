/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MomentTsum
public import WaveTurbulence.Foundations.XChain.PartitionLabelEquiv
/-! Exact partition-wise countable decoration expansion of cumulant moments. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped Classical

noncomputable def assignedFamily {Ω ι : Type*} {α : ι → Type*}
    (F : (i : ι) → α i → Ω → ℂ) (s : Finset ι) (a : (i : ↥s) → α i.1) : ι → Ω → ℂ :=
  fun i ω => if hi : i ∈ s then F i (a ⟨i, hi⟩) ω else 0

noncomputable def blockSeriesMoment {Ω ι : Type*} [MeasurableSpace Ω] {α : ι → Type*}
    (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ) (J : Finset ι)
    (a : (i : ↥J) → α i.1) : ℂ := ∫ ω, ∏ i : ↥J, F i.1 (a i) ω ∂μ

noncomputable def partitionSeriesMoment {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    {s : Finset ι} (P : Finpartition s) (a : (i : ↥s) → α i.1) : ℂ :=
  ∏ B : P.parts, blockSeriesMoment μ F B.1 (fun i => a ⟨i.1, P.le B.2 i.2⟩)

theorem integral_assignedFamily_prod {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    (s J : Finset ι) (hJ : J ⊆ s) (a : (i : ↥s) → α i.1) :
    (∫ ω, ∏ i ∈ J, assignedFamily F s a i ω ∂μ) =
      blockSeriesMoment μ F J (fun i => a ⟨i.1, hJ i.2⟩) := by
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    dsimp only
    rw [← prod_coe_sort J (fun i => assignedFamily F s a i ω)]
    apply prod_congr rfl
    intro i _
    exact dif_pos (hJ i.2))

theorem cumulant_assignedFamily_eq {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    (s : Finset ι) (a : (i : ↥s) → α i.1) :
    cumulant μ (assignedFamily F s a) s =
      ∑ P : Finpartition s, ((-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ)) *
        partitionSeriesMoment μ F P a := by
  unfold cumulant partitionSeriesMoment
  apply sum_congr rfl
  intro P _
  apply congrArg (fun z : ℂ => ((-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ)) * z)
  rw [← prod_coe_sort P.parts (fun J => ∫ ω, ∏ i ∈ J, assignedFamily F s a i ω ∂μ)]
  exact prod_congr rfl (fun B _ => integral_assignedFamily_prod μ F s B.1 (P.le B.2) a)

theorem partitionMoment_pi_tsum {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    {s : Finset ι} (P : Finpartition s)
    (hI : ∀ B : P.parts, ∀ a : (i : ↥B.1) → α i.1,
      Integrable (fun ω => ∏ i : ↥B.1, F i.1 (a i) ω) μ)
    (hS : ∀ B : P.parts, Summable (fun a : (i : ↥B.1) → α i.1 =>
      ∫ ω, ‖∏ i : ↥B.1, F i.1 (a i) ω‖ ∂μ)) :
    (∏ J ∈ P.parts, ∫ ω, ∏ i ∈ J, ∑' a, F i a ω ∂μ) =
      ∑' a : (i : ↥s) → α i.1, partitionSeriesMoment μ F P a := by
  have hb (B : P.parts) : (∫ ω, ∏ i ∈ B.1, ∑' a, F i a ω ∂μ) =
      ∑' a, blockSeriesMoment μ F B.1 a := by
    have he : (fun ω => ∏ i ∈ B.1, ∑' a, F i a ω) =
        fun ω => ∏ i : ↥B.1, ∑' a, F i.1 a ω := by
      funext ω
      exact (prod_coe_sort B.1 (fun i => ∑' a, F i a ω)).symm
    rw [he]
    exact integral_prod_tsum μ (fun i : ↥B.1 => F i.1) (hI B) (hS B)
  rw [← prod_coe_sort P.parts (fun J => ∫ ω, ∏ i ∈ J, ∑' a, F i a ω ∂μ)]
  have hp := prod_congr (s₁ := (univ : Finset P.parts)) rfl (fun B _ => hb B)
  exact hp.trans (tsum_partition_labels P α (fun B => blockSeriesMoment μ F B.1)).symm

end WaveTurbulence.Induct
