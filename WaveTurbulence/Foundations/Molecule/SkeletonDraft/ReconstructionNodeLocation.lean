/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LocalInsertionHoles

/-! # Actual forest nodes occupy a context block or its filled terminal subtree -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem node_mem_subtree_addresses {w : ℕ} (forest : Fin w → TTree)
    (a target : Address w) (t : TTree)
    (hs : Comb.subtree (forest a.1) a.2 = some t)
    (hn : target.2 ∈ (forest target.1).nodes) (hb : Below a target) :
    target ∈ nodeAddresses t a := by
  obtain ⟨r,rfl⟩ := below_exists_frame a target hb
  apply Finset.mem_image.mpr
  refine ⟨r,(Comb.subtree_nodes_iff hs r).mpr ?_,rfl⟩
  exact hn

/-- Every actual decoded node is either represented by this chain, outside its root,
or inside the original core subtree filling its hole. -/
theorem ReconstructionData.node_chain_location {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (b : GBranch S.tree) :
    target.1 ∈ chainNodes (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) ∨
      ¬ Below (inflatedPosition S D.tree b.toNode) target.1 ∨ Below (D.corePosition b) target.1 := by
  by_cases hb : Below (inflatedPosition S D.tree b.toNode) target.1
  · have hn := node_mem_subtree_addresses (D.forest hS) _ target.1 _
      (D.forest_subtree_position hS b.toNode) target.2 hb
    rw [D.inflateNode_branch hS b,chain_nodeAddresses] at hn
    rcases Finset.mem_union.mp hn with hc | hh
    · exact Or.inl hc
    · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hh
      refine Or.inr (Or.inr ?_)
      rw [← he]
      exact below_extend _ r
  · exact Or.inr (Or.inl hb)

end WaveTurbulence.Reg.Skeleton
