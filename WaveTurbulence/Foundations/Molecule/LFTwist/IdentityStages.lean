/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.IdentityData
public import WaveTurbulence.Foundations.Molecule.LFTwist.LFConstruction
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReverseCoherentCollapse

/-! # The exact intermediate layered object for the identity LF choice -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed
namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

@[expose] noncomputable def identityMid : LayeredGarden w :=
  collapsePairedTreeLayered LG (s.data.decoded_chain_isSubPairedTree s.plain s.decodes s.placement.lower)

theorem identityMid_decodes :
    (s.midData false (s.data.couple s.exceptional) (s.data.couple_wf s.exceptional)).Decodes
      (s.chosen_plain false) s.identityMid.garden :=
  s.midData_identity.symm ▸ eraseTree_collapse_decodes s.data s.plain s.decodes s.placement.lower

theorem identityMid_canonical : CanonicalObject p kind s.identityMid :=
  s.canonical.eraseTree_coherent LG s.data s.plain s.decodes s.placement.lower s.treeCoherent

/-- The identity choice restores the exact old coherent couple after its actual collapse. -/
theorem identity_couple_insertion : CoherentCoupleInsertion p (s.base false) s.identityMid
    (coupleRoot (s.baseData false) (s.chosen_plain false) (s.pairs false s.exceptional) 0)
    (coupleRoot (s.baseData false) (s.chosen_plain false) (s.pairs false s.exceptional) 1)
    (s.data.couple s.exceptional) := by
  let F := s.data.eraseTree s.placement.lower
  have hf : F.Decodes s.plain s.identityMid.garden := eraseTree_collapse_decodes s.data s.plain s.decodes s.placement.lower
  have hE := reconstruction_coupleEmb F s.plain hf s.exceptional
  change Embeds s.identityMid.garden (s.data.couple s.exceptional) _ _ at hE
  have hcoh := eraseTree_couple_coherent LG s.data s.plain s.decodes s.placement.lower s.exceptional s.coupleCoherent
  have ha : nodeSign s.identityMid.garden.sig (inflatedPosition s.skeleton F.tree (s.exceptional.firstLeaf s.plain).toNode) = 1 :=
    (F.decodedNode_sign s.plain hf _).trans (sourcePair_first_sign s.skeleton s.plain s.exceptional)
  have hb : nodeSign s.identityMid.garden.sig (inflatedPosition s.skeleton F.tree (s.exceptional.secondLeaf s.plain).toNode) = -1 :=
    (F.decodedNode_sign s.plain hf _).trans (sourcePair_second_sign s.skeleton s.plain s.exceptional)
  rw [s.pairs_false,s.baseData_false]
  change CoherentCoupleInsertion p
    (normalizedLayered LG s.data s.plain s.decodes s.placement.lower s.exceptional p) s.identityMid
    (inflatedPosition s.skeleton F.tree (s.exceptional.firstLeaf s.plain).toNode)
    (inflatedPosition s.skeleton F.tree (s.exceptional.secondLeaf s.plain).toNode)
    (s.data.couple s.exceptional)
  by_cases hq : s.data.couple s.exceptional = .triv
  · simp only [normalizedLayered,hq,ite_true]
    rw [hq] at hE
    exact reinsert_triv_identity s.identityMid s.identityMid_canonical _ _ ha hb hE
  · simp only [normalizedLayered,hq,ite_false]
    exact reinsert_collapsed_couple s.identityMid (F.decoded_couple_isSubCouple s.plain hf s.exceptional)
      s.identityMid_canonical _ (s.data.couple_wf s.exceptional) ha hb hE hcoh

/-- The identity choice restores the exact old coherent regular tree. -/
theorem identity_tree_insertion :
    ∃ t : TTree, CoherentTreeInsertion p s.identityMid LG
      (inflatedPosition (s.chosen false)
        (s.midData false (s.data.couple s.exceptional) (s.data.couple_wf s.exceptional)).tree
        (s.branches false s.placement.lower).toNode)
      (nodeSign (s.chosen false).sig (s.branches false s.placement.lower).1) t
      (s.data.tree s.placement.lower) := by
  let b := s.placement.lower
  let a := s.data.decodedNode s.plain s.decodes b.toNode
  let n := s.data.decodedCoreNode s.plain s.decodes b
  let h := s.data.decoded_chain_isSubPairedTree s.plain s.decodes b
  have hs : Comb.nodeSubtree n = node3 (fun i => s.data.inflateNode s.plain (b.child i)) :=
    Option.some.inj ((Comb.nodeSubtree_spec n).symm.trans (s.data.decoded_subtree_core s.plain s.decodes b))
  have hE : ChainEmb LG.garden (s.data.tree b) (nodeSign s.skeleton.sig b.1) a.1 (Comb.nodeSubtree n) := by
    rw [hs]
    exact reconstruction_chainEmb s.data s.plain s.decodes b
  have hi := reinsert_collapsed_tree LG h s.canonical (s.data.tree b) (nodeSign s.skeleton.sig b.1)
    (s.data.tree_wf b) (s.data.decodedNode_sign s.plain s.decodes b.toNode) hE s.treeCoherent rfl
  refine ⟨Comb.nodeSubtree n,?_⟩
  rw [s.midData_identity]
  exact (s.data.eraseTree_position_at b) ▸ hi

end LFSource
end WaveTurbulence.LFTwist
