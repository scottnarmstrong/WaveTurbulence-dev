/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeSubtreeMembership
public import WaveTurbulence.Foundations.XChain.LayerCutBlockGarden
/-! Exact order of extracted lower gardens as the sum of the original subtree orders. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def subtreeBranchEquiv {w : ℕ} (tree : Fin w → TTree) (a : GNode tree) :
    ↥(subtreeAt (tree a.1.1) a.1.2).branching ≃
      ↥(univ.filter (fun b : GBranch tree => a.IsDesc b.toNode)) :=
  Equiv.ofBijective (fun b => ⟨⟨(a.1.1, a.1.2 ++ b.1),
    (subtreeAt_branching_iff _ _ a.2 _).mp b.2⟩,
    mem_filter.mpr ⟨mem_univ _, rfl, List.prefix_append _ _⟩⟩) (by
    constructor
    · intro b c he
      exact Subtype.ext (List.append_cancel_left (congrArg (fun z => z.1.1.2) he))
    · rintro ⟨b, hb⟩
      obtain ⟨hj, r, hr⟩ := (mem_filter.mp hb).2
      have hm : a.1.2 ++ r ∈ (tree a.1.1).branching := by
        have h0 : b.1.2 ∈ (tree a.1.1).branching :=
          (congrArg (fun k => b.1.2 ∈ (tree k).branching) hj.symm).mp b.2
        exact (congrArg (fun q => q ∈ (tree a.1.1).branching) hr.symm).mp h0
      refine ⟨⟨r, (subtreeAt_branching_iff _ _ a.2 _).mpr hm⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hj hr)

theorem subtreeAt_order {w : ℕ} (tree : Fin w → TTree) (a : GNode tree) :
    (subtreeAt (tree a.1.1) a.1.2).order = a.orderBelow := by
  have hc := Fintype.card_congr (subtreeBranchEquiv tree a)
  simpa only [Fintype.card_coe, TTree.card_branching_eq, GNode.orderBelow] using hc

theorem cutBlockGarden_order {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B))) :
    (cutBlockGarden LG p B hcp).garden.order = ∑ u ∈ cutBlockRoots LG p B, u.orderBelow := by
  change (∑ k, ((cutBlockGarden LG p B hcp).garden.tree k).order) = _
  simp_rw [cutBlockGarden_tree]
  have he : (∑ k : Fin B.card,
      (subtreeAt (LG.garden.tree (B.equivFin.symm k).1.1.1) (B.equivFin.symm k).1.1.2).order) =
      ∑ k : Fin B.card, (cutLeafNodeEmbedding LG p (B.equivFin.symm k).1).orderBelow := by
    apply sum_congr rfl
    intro k _
    exact subtreeAt_order LG.garden.tree (cutLeafNodeEmbedding LG p (B.equivFin.symm k).1)
  rw [he]
  have hs := Fintype.sum_equiv B.equivFin.symm
    (fun k => (cutLeafNodeEmbedding LG p (B.equivFin.symm k).1).orderBelow)
    (fun b : ↥B => (cutLeafNodeEmbedding LG p b.1).orderBelow) (fun _ => rfl)
  rw [hs]
  exact (sum_coe_sort B (fun b => (cutLeafNodeEmbedding LG p b).orderBelow)).trans
    (sum_map B (cutLeafNodeEmbedding LG p) (fun u => u.orderBelow)).symm

end WaveTurbulence.Induct
