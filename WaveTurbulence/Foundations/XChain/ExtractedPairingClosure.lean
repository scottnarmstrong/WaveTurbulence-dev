/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedLayeredGarden
public import WaveTurbulence.Foundations.XChain.PairedEmbedding
/-! Pairing closure and complete subtree leaf sets transfer through antichain extraction. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem extractedGarden_pair_map {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (ℓ : GLeaf (subforestTrees U)) :
    subforestLeafMap U ((extractedGarden LG U hU hcp).pair ℓ) = LG.garden.pair (subforestLeafMap U ℓ) :=
  extractedPair_image LG U hU hcp ℓ

theorem extractedGarden_completelyPaired_map_iff {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (S : Finset (GLeaf (subforestTrees U))) :
    LG.garden.CompletelyPaired (S.map (subforestLeafEmbedding LG U hU)) ↔
      (extractedGarden LG U hU hcp).CompletelyPaired S :=
  completelyPaired_map_iff (extractedGarden LG U hU hcp) LG.garden (subforestLeafEmbedding LG U hU)
    (fun ℓ => (extractedGarden_pair_map LG U hU hcp ℓ).symm) S

theorem subforestNodeMap_leavesBelow {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (a : GNode (subforestTrees U)) :
    (subforestNodeMap U a).leavesBelow = a.leavesBelow.map (subforestLeafEmbedding LG U hU) := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    have hd := (Finset.mem_filter.mp hℓ).2
    have hm : ℓ ∈ LG.leavesBelowSet U := Canon.Rel.mem_leavesBelowSet.mpr
      ⟨subforestRoot U a.1.1, subforestRoot_mem U a.1.1, (subforestNodeMap_below U a).trans hd⟩
    obtain ⟨l, he⟩ := (subforestLeafEquiv LG U hU).surjective ⟨ℓ, hm⟩
    have hel : subforestLeafMap U l = ℓ := congrArg Subtype.val he
    have heP := congrArg (fun x : GLeaf LG.garden.tree => (subforestNodeMap U a).IsDesc x.toNode) hel
    have hd' : (subforestNodeMap U a).IsDesc (subforestNodeMap U l.toNode) := heP.mpr hd
    have hl : l ∈ a.leavesBelow := Finset.mem_filter.mpr
      ⟨mem_univ _, (subforestNodeMap_isDesc_iff LG U hU a l.toNode).mp hd'⟩
    exact Finset.mem_map.mpr ⟨l, hl, hel⟩
  · intro hℓ
    obtain ⟨l, hl, he⟩ := Finset.mem_map.mp hℓ
    have hd := (subforestNodeMap_isDesc_iff LG U hU a l.toNode).mpr (Finset.mem_filter.mp hl).2
    have hm : subforestLeafMap U l ∈ (subforestNodeMap U a).leavesBelow :=
      Finset.mem_filter.mpr ⟨mem_univ _, hd⟩
    exact he ▸ hm

end WaveTurbulence.Induct
