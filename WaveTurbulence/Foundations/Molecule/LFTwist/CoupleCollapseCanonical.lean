/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CoupleCollapseAgreement
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Count

/-! # Coherent couple collapse preserves source canonical classes

The collapsed object and its layers are constructed explicitly. C4 then
transfers canonicity from a coherent actual embedded couple to the new leaf pair.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} (LG : LayeredGarden w) {a b : GNode LG.garden.tree}
    (h : Comb.IsSubCouple LG.garden a b)

@[expose] noncomputable def collapsedLeftLeaf : GLeaf (collapseCoupleGarden h).tree :=
  collapseLeafEquiv LG.garden.tree a b (Comb.subCouple_incomparable h) (.inr 0)

@[expose] noncomputable def collapsedRightLeaf : GLeaf (collapseCoupleGarden h).tree :=
  collapseLeafEquiv LG.garden.tree a b (Comb.subCouple_incomparable h) (.inr 1)

theorem collapseCouple_embeds_triv (hi : Indep a.1 b.1) :
    Embeds (collapseCoupleGarden h) .triv a.1 b.1 where
  indep := hi
  nodeA := (collapsedLeftLeaf LG h).toNode.2
  nodeB := (collapsedRightLeaf LG h).toNode.2
  treeA := subtreeAt_of_mem_leaves _ _ (collapsedLeftLeaf LG h).2
  treeB := subtreeAt_of_mem_leaves _ _ (collapsedRightLeaf LG h).2
  pairs := by
    intro p hp l hl
    have he : p = (a.1,b.1) := by simpa only [RegCpl.pairsAt, List.mem_singleton] using hp
    subst p
    have he : l = collapsedLeftLeaf LG h := Subtype.ext hl
    rw [he]
    exact congrArg (fun m : GLeaf (collapseCoupleGarden h).tree => m.1)
      (collapseCoupleGarden_pair_left h)

/-- Both newly created leaves are in the minimum of their actual parent layers. -/
theorem collapseCouple_min_layers (p : ℕ) :
    (collapseCoupleLayered LG h p).layer (collapsedLeftLeaf LG h).toNode =
      min ((collapseCoupleLayered LG h p).parentLayer p (collapsedLeftLeaf LG h).toNode)
        ((collapseCoupleLayered LG h p).parentLayer p (collapsedRightLeaf LG h).toNode) := by
  have hp : (collapseCoupleGarden h).pair (collapsedLeftLeaf LG h) = collapsedRightLeaf LG h :=
    collapseCoupleGarden_pair_left h
  exact (extendBranchLayers_leaf _ _ p (collapsedLeftLeaf LG h)).trans (congrArg₂ min
    (branchParentValue_eq_extension_parentLayer _ _ p (collapseCouple_branchPrelayering LG h)
      (collapsedLeftLeaf LG h).toNode)
    ((congrArg (branchParentValue (collapseCoupleGarden h)
      (fun c => LG.layer (collapseCoupleBranchEmbedding h c).toNode) p)
        (congrArg GLeaf.toNode hp)).trans
      (branchParentValue_eq_extension_parentLayer _ _ p (collapseCouple_branchPrelayering LG h)
        (collapsedRightLeaf LG h).toNode)))

/-- The literal new pair satisfies C4's full trivial-couple layer pattern. -/
theorem collapseCouple_triv_pattern (p : ℕ) :
    LayerPattern (collapseCoupleLayered LG h p) p .triv a.1 b.1 := by
  constructor
  · intro l hl
    simp only [RegCpl.linksAt, List.not_mem_nil] at hl
  · intro z hz
    simp only [cplNodes, RegCpl.linksAt, RegCpl.pairsAt, pairEndpoints_nil,
      pairEndpoints_singleton, Finset.empty_union, Finset.mem_insert,
      Finset.mem_singleton] at hz
    have hleft := collapseCouple_min_layers LG h p
    have heq : (collapseCoupleLayered LG h p).layer (collapsedLeftLeaf LG h).toNode =
        (collapseCoupleLayered LG h p).layer (collapsedRightLeaf LG h).toNode :=
      (collapseCoupleLayered LG h p).isLayering.2 (collapsedLeftLeaf LG h) |>
        (fun he => he.trans (congrArg (collapseCoupleLayered LG h p).layer
          (congrArg GLeaf.toNode (collapseCoupleGarden_pair_left h))))
    have hpa := parAt_of_mem (collapseCoupleLayered LG h p) p (collapsedLeftLeaf LG h).toNode.2
    have hpb := parAt_of_mem (collapseCoupleLayered LG h p) p (collapsedRightLeaf LG h).toNode.2
    rcases hz with rfl | rfl
    · exact (layerAt_node (collapseCoupleLayered LG h p) (collapsedLeftLeaf LG h).toNode).trans
        (hleft.trans (congrArg₂ min hpa hpb).symm)
    · exact (layerAt_node (collapseCoupleLayered LG h p) (collapsedRightLeaf LG h).toNode).trans
        (heq.symm.trans (hleft.trans (congrArg₂ min hpa hpb).symm))

/-- Collapsing a coherent embedded regular couple preserves canonical gardens. -/
theorem collapseCouple_isCanonG {p : ℕ} (hc : IsCanonG (p+1) LG)
    (Q : RegCpl) (hwf : Q.wf = true) (hE : Embeds LG.garden Q a.1 b.1)
    (hcoh : CohOn LG (Q.linksAt a.1 b.1)) :
    IsCanonG (p+1) (collapseCoupleLayered LG h p) := by
  exact layerreg1_replace_canonG hc hwf hE hcoh
    (collapseCouple_outAgree LG h p hc.2.2.2 hc.2.1)
    (collapseCouple_embeds_triv LG h hE.indep) (collapseCouple_triv_pattern LG h p)

/-- The same literal collapse preserves canonical couples. -/
theorem collapseCouple_isCanonC {LG : LayeredGarden 2} {a b : GNode LG.garden.tree}
    (h : Comb.IsSubCouple LG.garden a b) {p : ℕ} (hc : IsCanonC (p+1) LG)
    (Q : RegCpl) (hwf : Q.wf = true) (hE : Embeds LG.garden Q a.1 b.1)
    (hcoh : CohOn LG (Q.linksAt a.1 b.1)) :
    IsCanonC (p+1) (collapseCoupleLayered LG h p) := by
  exact layerreg1_replace_canonC hc hwf hE hcoh
    (collapseCouple_outAgree LG h p hc.2 hc.1.1) rfl
    (collapseCouple_embeds_triv LG h hE.indep) (collapseCouple_triv_pattern LG h p)

end WaveTurbulence.LFTwist
