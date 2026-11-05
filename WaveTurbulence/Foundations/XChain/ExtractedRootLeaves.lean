/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedPairingClosure
/-! Root-subset leaf sets are preserved exactly by antichain extraction. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem subforestRoot_injective {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) : Function.Injective (subforestRoot U) := by
  intro i j he
  exact (U.equivFin.symm).injective (Subtype.ext he)

theorem subforest_root_leaves_map {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (A : Finset (Fin U.card)) :
    LG.leavesBelowSet (A.image (subforestRoot U)) =
      (univ.filter (fun ℓ : GLeaf (subforestTrees U) => ℓ.1.1 ∈ A)).map
        (subforestLeafEmbedding LG U hU) := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    obtain ⟨u, hu, hd⟩ := Canon.Rel.mem_leavesBelowSet.mp hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
    have hm : ℓ ∈ LG.leavesBelowSet U := Canon.Rel.mem_leavesBelowSet.mpr
      ⟨subforestRoot U k, subforestRoot_mem U k, hd⟩
    obtain ⟨l, he⟩ := (subforestLeafEquiv LG U hU).surjective ⟨ℓ, hm⟩
    have hel : subforestLeafMap U l = ℓ := congrArg Subtype.val he
    have heP := congrArg (fun x : GLeaf LG.garden.tree => (subforestRoot U k).IsDesc x.toNode) hel
    have hd' : (subforestRoot U k).IsDesc (subforestNodeMap U l.toNode) := heP.mpr hd
    have heR := congrArg (fun x : GNode LG.garden.tree => x.IsDesc (subforestNodeMap U l.toNode))
      (subforestNodeMap_root U k)
    have hlow := (subforestNodeMap_isDesc_iff LG U hU (GNode.root (subforestTrees U) k) l.toNode).mp
      (heR.mpr hd')
    have hl : l ∈ univ.filter (fun ℓ : GLeaf (subforestTrees U) => ℓ.1.1 ∈ A) :=
      Finset.mem_filter.mpr ⟨mem_univ _, hlow.1 ▸ hk⟩
    exact Finset.mem_map.mpr ⟨l, hl, hel⟩
  · intro hℓ
    obtain ⟨l, hl, he⟩ := Finset.mem_map.mp hℓ
    have hm : subforestLeafMap U l ∈ LG.leavesBelowSet (A.image (subforestRoot U)) :=
      Canon.Rel.mem_leavesBelowSet.mpr ⟨subforestRoot U l.1.1,
        Finset.mem_image_of_mem _ (Finset.mem_filter.mp hl).2, subforestLeafMap_below U l⟩
    exact he ▸ hm

theorem extracted_irreducible_of_irreducibleAt {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (hirr : LG.IrreducibleAt U) :
    (extractedLayeredGarden LG U hU hcp).garden.Irreducible := by
  classical
  intro A hAn hAu hpair
  have hsub : A.image (subforestRoot U) ⊆ U := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    exact subforestRoot_mem U k
  have hneq : A.image (subforestRoot U) ≠ U := by
    intro he
    apply hAu
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    have hm : subforestRoot U k ∈ A.image (subforestRoot U) := he.symm ▸ subforestRoot_mem U k
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hm
    exact subforestRoot_injective U hji ▸ hj
  have hp := (extractedGarden_completelyPaired_map_iff LG U hU hcp _).mpr hpair
  have he := subforest_root_leaves_map LG U hU A
  exact hirr _ (Finset.mem_powerset.mpr hsub) (hAn.image _) hneq (he.symm ▸ hp)

end WaveTurbulence.Induct
