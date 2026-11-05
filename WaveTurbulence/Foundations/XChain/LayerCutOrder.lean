/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutBranches
public import WaveTurbulence.Foundations.XChain.LayerCutRetention
/-! The order of each cut top tree is exactly the source's top-layer branching count. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem layerCut_branch_mem_iff {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (b : GBranch LG.garden.tree) :
    b.1.2 ∈ (layerCutForest LG p b.1.1).branching ↔ LG.layer b.toNode = p := by
  constructor
  · intro hb
    exact layerCut_branch_layer LG p hbound ⟨b.1, hb⟩
  · intro hb
    exact mem_cutTree_branching_of_no_stop _ _ _ b.2
      ((layerCutStop_false_iff LG p b.toNode).mpr hb.ge)
      (no_strict_layerCutStop_of_layer_ge LG p b.toNode hb.ge)

noncomputable def layerCutBranchEquiv {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (j : Fin w) :
    ↥(layerCutForest LG p j).branching ≃
      ↥(univ.filter (fun b : GBranch LG.garden.tree => b.1.1 = j ∧ LG.layer b.toNode = p)) :=
  Equiv.ofBijective (fun a =>
    let b : GBranch LG.garden.tree := ⟨(j, a.1), cutTree_branching_subset _ _ a.2⟩
    ⟨b, mem_filter.mpr ⟨mem_univ _, rfl, (layerCut_branch_mem_iff LG p hbound b).mp a.2⟩⟩) (by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun z => z.1.1.2) he)
    · rintro ⟨b, hb⟩
      have hj := (mem_filter.mp hb).2.1
      have hl := (mem_filter.mp hb).2.2
      have hm := (layerCut_branch_mem_iff LG p hbound b).mpr hl
      refine ⟨⟨b.1.2, ?_⟩, ?_⟩
      · exact (congrArg (fun k => b.1.2 ∈ (layerCutForest LG p k).branching) hj).mp hm
      · apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hj.symm rfl)

theorem layerCutForest_order {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (j : Fin w) :
    (layerCutForest LG p j).order = LG.topOrder p j := by
  have hc := Fintype.card_congr (layerCutBranchEquiv LG p hbound j)
  simpa only [Fintype.card_coe, TTree.card_branching_eq, LayeredGarden.topOrder] using hc

end WaveTurbulence.Induct
