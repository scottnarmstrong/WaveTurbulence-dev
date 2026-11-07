/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLeafIncidences

/-! # Original paired leaves exhaust both sides of the regional pair slots -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clPairOriginal_internal (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) (c : Fin 2) :
    Mole.IsInternalLeaf G U (clPairOriginal hG p c) := by
  have hs := clRegionalPair_realization hG p.1 p.2
  by_cases hc : c = 0
  · simpa only [clPairOriginal,hc,ite_true] using (leaf_mem_clRealizationNodes _).mp hs.1
  · simpa only [clPairOriginal,hc,ite_false] using (leaf_mem_clRealizationNodes _).mp hs.2

theorem clInternalLeaf_side_exists (hG : G.IsPlain) (ℓ : GLeaf G.tree)
    (hℓ : Mole.IsInternalLeaf G U ℓ) :
    ∃ p : ↥(clRegionalPairs hG U), ∃ c : Fin 2, clPairOriginal hG p c = ℓ := by
  classical
  let p := pairOfLeaf G hG ℓ
  by_cases hs : nodeSign G.sig ℓ.1 = 1
  · have he := (pairOfLeaf_sides_pos G hG ℓ hs).1
    have hp : p ∈ clRegionalPairs hG U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm ▸ hℓ⟩
    refine ⟨⟨p,hp⟩,0,?_⟩
    exact he
  · have he := pairOfLeaf_sides_neg G hG ℓ hs
    have hi := (Mole.internal_leaf_pair_iff G U ℓ).mpr hℓ
    have hp : p ∈ clRegionalPairs hG U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.1.symm ▸ hi⟩
    refine ⟨⟨p,hp⟩,1,?_⟩
    exact he.2

theorem clTreeLeaf_internal_side_exists (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (l : GLeaf (CLTreeForest R)) (ℓ : GLeaf G.tree)
    (he : clTreeNode R l.toNode = ℓ.toNode) (hℓ : Mole.IsInternalLeaf G U ℓ) :
    ∃ p : ↥(clRegionalPairs hG U), ∃ c : Fin 2, clPairSideLeaf hU R hG p c = l := by
  obtain ⟨p,c,hp⟩ := clInternalLeaf_side_exists hG ℓ hℓ
  refine ⟨p,c,?_⟩
  have hn := (clPairSideLeaf_node hU R hG p c).trans (congrArg (fun ℓ : GLeaf G.tree => ℓ.toNode) hp)
  exact Mole.leaf_toNode_injective (clTreeNode_injective R (hn.trans he.symm))

end WaveTurbulence.VineEstS2
