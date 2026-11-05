/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerEmbeddings
/-! Exact leaf sets below lower nodes, needed for canonicality and irreducibility transport. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem mem_lower_leavesBelow_iff {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GNode (low B).tree) (ℓ : GLeaf (low B).tree) :
    lowerLeafEmbedding top P low B ℓ ∈ (lowerNodeEmbedding top P low B a).leavesBelow ↔
      ℓ ∈ a.leavesBelow := by
  simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and]
  have he := gardenLeaf_toNode_lower top P low B ℓ
  have h := garden_lower_isDesc_iff top P low B a ℓ.toNode
  exact (congrArg (fun x : GNode (graftForest top (blockGraftTrees top P low)) =>
    (lowerNodeEmbedding top P low B a).IsDesc x) he).to_iff.trans h

theorem not_mem_lower_leavesBelow_of_blocks_ne {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B C : P.parts) (hBC : B ≠ C) (a : GNode (low B).tree) (ℓ : GLeaf (low C).tree) :
    lowerLeafEmbedding top P low C ℓ ∉ (lowerNodeEmbedding top P low B a).leavesBelow := by
  intro h
  have hd := (Finset.mem_filter.mp h).2
  have he := gardenLeaf_toNode_lower top P low C ℓ
  have hd' : (gardenNodeEquiv top P low (.inr ⟨B, a⟩)).IsDesc
      (gardenNodeEquiv top P low (.inr ⟨C, ℓ.toNode⟩)) :=
    (congrArg (fun x : GNode (graftForest top (blockGraftTrees top P low)) =>
      (lowerNodeEmbedding top P low B a).IsDesc x) he) ▸ hd
  exact hBC (garden_lower_block_eq_of_isDesc top P low B C a ℓ.toNode hd')

theorem lower_leavesBelow_eq_map {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GNode (low B).tree) :
    (lowerNodeEmbedding top P low B a).leavesBelow = a.leavesBelow.map (lowerLeafEmbedding top P low B) := by
  classical
  ext ℓ
  obtain ⟨⟨C, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
  by_cases hCB : C = B
  · subst C
    constructor
    · intro h
      exact Finset.mem_map.mpr ⟨l, (mem_lower_leavesBelow_iff top P low B a l).mp h, rfl⟩
    · intro h
      obtain ⟨l', hl', he⟩ := Finset.mem_map.mp h
      have hll : l' = l := (lowerLeafEmbedding top P low B).injective he
      exact (mem_lower_leavesBelow_iff top P low B a l).mpr (hll ▸ hl')
  · constructor
    · intro h
      exact False.elim (not_mem_lower_leavesBelow_of_blocks_ne top P low B C (Ne.symm hCB) a l h)
    · intro h
      obtain ⟨l', _, he⟩ := Finset.mem_map.mp h
      have he' : (⟨B, l'⟩ : Σ B : P.parts, GLeaf (low B).tree) = ⟨C, l⟩ :=
        (gardenLeafEquiv top P low).symm.injective he
      exact False.elim (hCB (congrArg Sigma.fst he').symm)

end WaveTurbulence.Induct
