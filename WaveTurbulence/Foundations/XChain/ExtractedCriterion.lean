/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedParents
public import WaveTurbulence.Foundations.XChain.ExtractedPairingClosure
/-! CANON's relative criterion becomes the literal criterion on the extracted garden. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem extracted_criterion_of_relCrit {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (q : ℕ)
    (hcrit : Canon.Rel.RelCrit LG U q) :
    (extractedLayeredGarden LG U hU hcp).CanonCriterion q := by
  have hb (a : GNode (subforestTrees U)) : LG.BelowSet U (subforestNodeMap U a) :=
    ⟨subforestRoot U a.1.1, subforestRoot_mem U a.1.1, subforestNodeMap_below U a⟩
  refine ⟨fun a => hcrit.1 _ (hb a), ?_⟩
  intro a b hinc hpair
  have hic : (subforestNodeMap U a).Incomparable (subforestNodeMap U b) :=
    ⟨fun h => hinc.1 ((subforestNodeMap_isDesc_iff LG U hU a b).mp h),
      fun h => hinc.2 ((subforestNodeMap_isDesc_iff LG U hU b a).mp h)⟩
  have hleaves : (subforestNodeMap U a).leavesBelow ∪ (subforestNodeMap U b).leavesBelow =
      (a.leavesBelow ∪ b.leavesBelow).map (subforestLeafEmbedding LG U hU) := by
    have he := congrArg₂ (fun (s t : Finset (GLeaf LG.garden.tree)) => s ∪ t)
      (subforestNodeMap_leavesBelow LG U hU a) (subforestNodeMap_leavesBelow LG U hU b)
    exact he.trans (Finset.map_union a.leavesBelow b.leavesBelow).symm
  have hp := (extractedGarden_completelyPaired_map_iff LG U hU hcp _).mpr hpair
  have hpair' : LG.garden.CompletelyPaired
      ((subforestNodeMap U a).leavesBelow ∪ (subforestNodeMap U b).leavesBelow) := hleaves.symm ▸ hp
  have hc := hcrit.2 _ _ (hb a) (hb b) hic hpair'
  have he := congrArg₂ min (extracted_parentLayer LG U hU hcp q a) (extracted_parentLayer LG U hU hcp q b)
  exact he.le.trans hc

end WaveTurbulence.Induct
