/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantEmbedding
public import WaveTurbulence.Foundations.XChain.BlockRootMembership
/-! The source's actual leaf-block cumulant equals its precise ordered Fin block.card enumeration. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def blockLeafEmbedding {α : Type*} (B : Finset α) : Fin B.card ↪ α where
  toFun k := (B.equivFin.symm k).1
  inj' a b h := (B.equivFin.symm).injective (Subtype.ext h)

theorem blockLeafEmbedding_map_univ {α : Type*} [DecidableEq α] (B : Finset α) :
    (univ : Finset (Fin B.card)).map (blockLeafEmbedding B) = B := by
  ext a
  constructor
  · intro h
    obtain ⟨k, _, rfl⟩ := mem_map.mp h
    exact (B.equivFin.symm k).2
  · intro h
    exact mem_map.mpr ⟨B.equivFin ⟨a, h⟩, mem_univ _,
      congrArg (fun b : ↥B => b.1) (B.equivFin.symm_apply_apply ⟨a, h⟩)⟩

theorem cumulant_ordered_block {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    (μ : Measure Ω) (X : α → Ω → ℂ) (B : Finset α) :
    cumulant μ (fun k ω => X ((B.equivFin.symm k).1) ω) univ = cumulant μ X B := by
  have he := cumulant_map_embedding μ X (blockLeafEmbedding B) univ
  exact he.trans (congrArg (cumulant μ X) (blockLeafEmbedding_map_univ B))

theorem cumulant_blockRootEquiv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w : ℕ} (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (X : GLeaf top → Ω → ℂ) (B : P.parts) :
    cumulant μ (fun k ω => X ((blockRootEquiv top P).symm ⟨B, k⟩) ω) univ = cumulant μ X B.1 := by
  have he : (fun k ω => X ((blockRootEquiv top P).symm ⟨B, k⟩) ω) =
      fun k ω => X ((B.1.equivFin.symm k).1) ω := by
    funext k ω
    exact congrArg (fun l => X l ω) (blockRootEquiv_symm_eq top P B k)
  rw [he]
  exact cumulant_ordered_block μ X B.1

end WaveTurbulence.Induct
