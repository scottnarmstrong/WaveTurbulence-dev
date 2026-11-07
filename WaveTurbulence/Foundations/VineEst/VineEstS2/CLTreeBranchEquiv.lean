/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLRealizationTree

/-! # Actual CL branching-node equivalence and exact realization order -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clTreeBranch_surjective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GBranch G.tree) (hv : v ∈ U) : ∃ p, clTreeBranch R p = v := by
  have hr := (cl_realization_iff hU R v.toNode).mp ((Mole.branch_incidence_realization_iff G U v).mpr hv)
  change a.toNode.IsDesc v.toNode ∧ ¬ (a.child R.excluded).IsDesc v.toNode ∧
    ¬ (b.child R.positive).IsDesc v.toNode ∧ ¬ (b.child R.negative).IsDesc v.toNode at hr
  obtain ⟨ht,p,hp⟩ := hr.1
  change a.1.1 = v.1.1 at ht
  change a.1.2++p = v.1.2 at hp
  have hb : p ∈ (Comb.nodeSubtree a.toNode).branching := by
    apply (Comb.subtree_branching_iff (Comb.nodeSubtree_spec a.toNode) p).mpr
    change a.1.2++p ∈ (G.tree a.1.1).branching
    rw [ht,hp]
    exact v.2
  have hbl : b.1.1 = v.1.1 := ((Mole.cl_parent_strict_descendant G
    hU R.parentPattern).1.1).symm.trans ht
  have hc : p ∈ (clRealizationTree R).branching := by
    apply (cropTree_avoidCuts_branching_iff _ _ _ _).mpr
    refine ⟨hb,?_⟩
    intro c hc hcp
    simp only [clCutPaths,Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hr.2.1 ⟨ht,by change _ <+: v.1.2; rw [← hp]; exact hcp⟩
    · exact hr.2.2.1 ⟨hbl,by change _ <+: v.1.2; rw [← hp]; exact hcp⟩
    · exact hr.2.2.2 ⟨hbl,by change _ <+: v.1.2; rw [← hp]; exact hcp⟩
  refine ⟨⟨p,hc⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext ht hp

noncomputable def clTreeBranchEquiv (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    ↥(clRealizationTree R).branching ≃ ↥U :=
  Equiv.ofBijective (fun p => ⟨clTreeBranch R p,clTreeBranch_mem hU R p⟩)
    ⟨fun p q he => clTreeBranch_injective R (congrArg Subtype.val he),by
      intro v
      obtain ⟨p,hp⟩ := clTreeBranch_surjective hU R v.1 v.2
      exact ⟨p,Subtype.ext hp⟩⟩

/-- Exact source count: the cropped realization includes the upper joint,
so its order is n_(1)+1, with n_(1) counting U without that joint. -/
theorem clRealizationTree_order (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    (clRealizationTree R).order = U.card := by
  rw [← Comb.card_branching,← Fintype.card_coe,← Fintype.card_coe]
  exact Fintype.card_congr (clTreeBranchEquiv hU R)

end WaveTurbulence.VineEstS2
