/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPairMembership
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryLeaves

/-! # The exact regional leaf enumeration: paired leaves plus three boundary leaves -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clTreeLeaf_ne_branch (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (l : GLeaf (CLTreeForest R)) (v : GBranch G.tree) (hv : v ∈ U) :
    clTreeNode R l.toNode ≠ v.toNode := by
  intro he
  obtain ⟨p,hp⟩ := clTreeBranch_surjective hU R v hv
  let q : GBranch (CLTreeForest R) := ⟨(0,p.1),p.2⟩
  have hm := (clTreeNode_branch R q).trans ((congrArg (fun v : GBranch G.tree => v.toNode) hp).trans he.symm)
  exact Mole.branch_toNode_ne_leaf q l (clTreeNode_injective R hm)

theorem clPairSideLeaf_ne_boundary (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) (c : Fin 2) (j : Fin 3) :
    clPairSideLeaf hU R hG p c ≠ clBoundaryLeaf hU R j := by
  intro he
  have hm := congrArg (fun l : GLeaf (CLTreeForest R) => clTreeNode R l.toNode) he
  have hn := (clPairSideLeaf_node hU R hG p c).symm.trans (hm.trans (clBoundaryLeaf_node hU R j))
  have hr := (Mole.leaf_incidence_realization_iff G U _).mpr (clPairOriginal_internal hG p c)
  exact clOutBoundary_not_realization hU R j (hn ▸ hr)

noncomputable def clLeafSumMap (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : (↥(clRegionalPairs hG U) × Fin 2) ⊕ Fin 3 → GLeaf (CLTreeForest R)
  | .inl p => clPairSideLeaf hU R hG p.1 p.2
  | .inr j => clBoundaryLeaf hU R j

theorem clLeafSumMap_injective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : Function.Injective (clLeafSumMap hU R hG) := by
  rintro (⟨p,i⟩ | j) (⟨q,k⟩ | l) he
  · apply congrArg Sum.inl
    exact clPairSideLeaf_injective hU R hG he
  · exact (clPairSideLeaf_ne_boundary hU R hG p i l he).elim
  · exact (clPairSideLeaf_ne_boundary hU R hG q k j he.symm).elim
  · apply congrArg Sum.inr
    exact clBoundaryLeaf_injective hU R he

theorem clLeafSumMap_surjective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : Function.Surjective (clLeafSumMap hU R hG) := by
  intro l
  rcases clTreeLeaf_source_or_boundary hU R l with ⟨ℓ,he,hℓ⟩ | ⟨j,he⟩
  · obtain ⟨p,c,hp⟩ := clTreeLeaf_internal_side_exists hU R hG l ℓ he hℓ
    exact ⟨.inl (p,c),hp⟩
  · have hj : j ≠ 0 := by
      intro hj
      subst j
      exact clTreeLeaf_ne_branch hU R l a hU.2.1 he
    let k : Fin 3 := ⟨j.1-1,by omega⟩
    have hk : j = k.succ := Fin.ext (by change j.1 = (j.1-1)+1; omega)
    refine ⟨.inr k,?_⟩
    apply Mole.leaf_toNode_injective
    apply clTreeNode_injective R
    exact (clBoundaryLeaf_node hU R k).trans ((congrArg (clBoundaryNodes R) hk.symm).trans he.symm)

noncomputable def clLeafEquiv (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : (↥(clRegionalPairs hG U) × Fin 2) ⊕ Fin 3 ≃ GLeaf (CLTreeForest R) :=
  Equiv.ofBijective (clLeafSumMap hU R hG) ⟨clLeafSumMap_injective hU R hG,clLeafSumMap_surjective hU R hG⟩

end WaveTurbulence.VineEstS2
