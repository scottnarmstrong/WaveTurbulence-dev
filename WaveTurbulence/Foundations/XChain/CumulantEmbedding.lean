/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EmbeddingPartitionEquiv
public import WaveTurbulence.Foundations.Cumulant.Basic
/-! A finite cumulant is invariant under exact reindexing of its actual variables. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem cumulant_map_embedding {Ω α β : Type*} [MeasurableSpace Ω] [DecidableEq α] [DecidableEq β]
    (μ : Measure Ω) (X : β → Ω → ℂ) (f : α ↪ β) (s : Finset α) :
    cumulant μ (fun i ω => X (f i) ω) s = cumulant μ X (s.map f) := by
  unfold cumulant
  apply Fintype.sum_equiv (embeddingPartitionEquiv f s)
  intro P
  change (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
      (∏ A ∈ P.parts, ∫ ω, ∏ i ∈ A, X (f i) ω ∂μ) =
    (-1 : ℂ) ^ ((embeddingPartition f P).parts.card - 1) *
      (((embeddingPartition f P).parts.card - 1).factorial : ℂ) *
      ∏ A ∈ (embeddingPartition f P).parts, ∫ ω, ∏ i ∈ A, X i ω ∂μ
  simp only [embeddingPartition_parts, card_map, prod_map]
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) * z)
  apply prod_congr rfl
  intro A _
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => (Finset.prod_map A f (fun i => X i ω)).symm)

end WaveTurbulence.Induct
