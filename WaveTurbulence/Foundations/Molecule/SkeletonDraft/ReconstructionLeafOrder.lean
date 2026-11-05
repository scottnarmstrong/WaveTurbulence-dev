/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides
public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # The total order at source leaves counts each replacement couple exactly once -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.sum_leafTree_order {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (∑ ℓ : GLeaf S.tree, (D.leafTree hS ℓ).order) = ∑ p : SourcePair S, (D.couple p).size := by
  classical
  let E : SourcePair S × Fin 2 ≃ GLeaf S.tree := Equiv.ofBijective
    (fun z => sourcePairLeaf S hS z.1 z.2)
    ⟨sourcePairLeaf_injective S hS,sourcePairLeaf_surjective S hS⟩
  rw [← E.sum_comp (fun ℓ => (D.leafTree hS ℓ).order),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fin.sum_univ_two]
  change (D.leafTree hS (p.firstLeaf hS)).order +
    (D.leafTree hS (p.secondLeaf hS)).order = (D.couple p).size
  rw [D.leafTree_first,D.leafTree_second]
  exact code_trees_order _

end WaveTurbulence.Reg.Skeleton
