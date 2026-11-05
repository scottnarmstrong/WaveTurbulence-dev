/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePlacementGeometry

/-! # The actual paired-child relations in the switched source scenarios -/

public section
namespace WaveTurbulence.Twist
open TTree Reg.Skeleton
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- A leaf bond between distinct parents has an unmarked paired leaf. -/
theorem leafBond_unmarked {b c : GBranch G.tree} {i j : Fin 3} (hne : b ≠ c)
    {l q : GLeaf G.tree} (hl : l.toNode = b.child i) (hq : q.toNode = c.child j) (hp : G.pair l = q) :
    G.mark l = none := by
  by_contra hm
  have he := (G.pair_eq_iff l).mpr hm
  have hql : q = l := hp.symm.trans he
  have hn : l.1.2 ≠ [] := by
    change l.toNode.1.2 ≠ []
    rw [hl]
    exact Mole.child_nonroot G b i
  have hpb := parent_eq_of_child hn hl
  have hpc := parent_eq_of_child (n := l.toNode) (p := c) (i := j) hn (by rw [← hql]; exact hq)
  exact hne (hpb.symm.trans hpc)

/-- Actual LP pair relations between ordinary distinct atoms survive with the same child slots. -/
theorem leafPairAt_unitTwist {b c : GBranch G.tree} (hb : b ≠ P.lower) (hc : c ≠ P.lower)
    (hne : b ≠ c) (h : Molecpl.LeafPairAt G b c) :
    Molecpl.LeafPairAt (unitTwistGarden G P) (coreBranchEquiv G P b) (coreBranchEquiv G P c) := by
  obtain ⟨l,i,j,_hm,hl,hr⟩ := h
  have ht := leafBond_unitTwist G P (b := b) (c := c) ⟨l,G.pair l,hl,hr,rfl⟩ hb hc
  obtain ⟨l',q',hl',hq',hp'⟩ := ht
  have hne' : coreBranchEquiv G P b ≠ coreBranchEquiv G P c := (coreBranchEquiv G P).injective.ne hne
  exact ⟨l',i,j,leafBond_unmarked (unitTwistGarden G P) hne' hl' hq' hp',hl',by rw [hp']; exact hq'⟩

/-- The doubled LP pairs between ordinary atoms keep both pairs and their distinct ordered slots. -/
theorem doubleLeafPairAt_unitTwist {b c : GBranch G.tree} (hb : b ≠ P.lower) (hc : c ≠ P.lower)
    (hne : b ≠ c) (h : Molecpl.DoubleLeafPairAt G b c) :
    Molecpl.DoubleLeafPairAt (unitTwistGarden G P) (coreBranchEquiv G P b) (coreBranchEquiv G P c) := by
  obtain ⟨l₀,l₁,i₀,i₁,j₀,j₁,_hm₀,_hm₁,hl₀,hr₀,hl₁,hr₁,hi,hj⟩ := h
  obtain ⟨r₀,q₀,ha₀,hb₀,hp₀⟩ := leafBond_unitTwist G P (b := b) (c := c)
    ⟨l₀,G.pair l₀,hl₀,hr₀,rfl⟩ hb hc
  obtain ⟨r₁,q₁,ha₁,hb₁,hp₁⟩ := leafBond_unitTwist G P (b := b) (c := c)
    ⟨l₁,G.pair l₁,hl₁,hr₁,rfl⟩ hb hc
  have hne' : coreBranchEquiv G P b ≠ coreBranchEquiv G P c := (coreBranchEquiv G P).injective.ne hne
  exact ⟨r₀,r₁,i₀,i₁,j₀,j₁,leafBond_unmarked (unitTwistGarden G P) hne' ha₀ hb₀ hp₀,
    leafBond_unmarked (unitTwistGarden G P) hne' ha₁ hb₁ hp₁,ha₀,by rw [hp₀]; exact hb₀,
    ha₁,by rw [hp₁]; exact hb₁,hi,hj⟩

/-- The new retained LP pair ends at the old lower parent. -/
theorem new_outer_leaf_pair :
    Molecpl.OuterLeafPairAt (unitTwistGarden G P) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot)) := by
  refine ⟨coreLeafEquiv G P P.retained,P.keep,P.lower.1.2.getLast P.nonroot,?_,?_,?_,P.outer⟩
  · exact (unitTwistGarden_mark G P P.retained).trans P.unmarked
  · exact (reversePlacement G P).child
  · rw [unitTwistGarden_pair]
    apply Subtype.ext
    change (coreLeafEquiv G P (G.pair P.retained)).1 =
      ((coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot)).1.1,
        (coreBranchEquiv G P (GNode.parent P.lower.toNode P.nonroot)).1.2 ++ [_])
    rw [coreLeafEquiv_paired_val,coreBranchEquiv_fixed_val G P _ (lower_parent_outside G P)]
    have hh := congrArg (fun n : GNode G.tree => n.1) (Mole.parent_child_eq_node P.lower.toNode P.nonroot).symm
    simpa only [GBranch.toNode,GBranch.child] using hh

/-- Every ordinary PC parent relation is preserved. -/
theorem isParent_unitTwist {p c : GBranch G.tree} (hc : c ≠ P.lower) (h : Molecpl.IsParent G p c) :
    Molecpl.IsParent (unitTwistGarden G P) (coreBranchEquiv G P p) (coreBranchEquiv G P c) := by
  obtain ⟨hn,hp⟩ := h
  exact ⟨(coreBranchEquiv_nonroot G P c).mpr hn,
    (branchParent_transport G P c hn hc).trans (congrArg (coreBranchEquiv G P) hp)⟩

end WaveTurbulence.Twist
