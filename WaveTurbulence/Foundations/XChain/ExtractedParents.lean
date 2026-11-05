/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedLayeredGarden
public import WaveTurbulence.Foundations.XChain.GraftParents
/-! Extracted parent layers agree exactly with the source's relative parent-layer convention. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem subforestNodeMap_path_ne_nil {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (a : GNode (subforestTrees U)) (ha : a.1.2 ≠ []) :
    (subforestNodeMap U a).1.2 ≠ [] := by
  intro he
  exact ha (List.append_eq_nil_iff.mp he).2

theorem subforestNodeMap_not_mem_of_internal {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (a : GNode (subforestTrees U)) (ha : a.1.2 ≠ []) : subforestNodeMap U a ∉ U := by
  intro hm
  have he := Canon.Rel.eq_of_isDesc_of_antichain hU (subforestRoot_mem U a.1.1) hm
    (subforestNodeMap_below U a)
  have hl := congrArg (fun u : GNode LG.garden.tree => u.1.2.length) he
  change (subforestRoot U a.1.1).1.2.length =
    ((subforestRoot U a.1.1).1.2 ++ a.1.2).length at hl
  rw [List.length_append] at hl
  exact ha (List.length_eq_zero_iff.mp (by omega))

theorem subforestNodeMap_par {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (a : GNode (subforestTrees U)) (ha : a.1.2 ≠ []) :
    subforestNodeMap U (Canon.par a) = Canon.par (subforestNodeMap U a) := by
  apply Subtype.ext
  change ((subforestRoot U a.1.1).1.1, (subforestRoot U a.1.1).1.2 ++ a.1.2.dropLast) =
    ((subforestRoot U a.1.1).1.1, ((subforestRoot U a.1.1).1.2 ++ a.1.2).dropLast)
  exact Prod.ext rfl (List.dropLast_append_of_ne_nil ha).symm

theorem extracted_parentLayer {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (q : ℕ)
    (a : GNode (subforestTrees U)) :
    (extractedLayeredGarden LG U hU hcp).parentLayer q a =
      Canon.Rel.rpl LG U q (subforestNodeMap U a) := by
  by_cases ha : a.1.2 = []
  · have hl : (extractedLayeredGarden LG U hU hcp).parentLayer q a = q := by
      simp only [LayeredGarden.parentLayer, ha, ite_true]
    have he : subforestNodeMap U a = subforestRoot U a.1.1 := by
      apply Subtype.ext
      exact Prod.ext rfl (by simp only [subforestNodeMap, ha, List.append_nil])
    have hm : subforestNodeMap U a ∈ U := he.symm ▸ subforestRoot_mem U a.1.1
    have hr : Canon.Rel.rpl LG U q (subforestNodeMap U a) = q := by
      simp only [Canon.Rel.rpl, hm, ite_true]
    exact hl.trans hr.symm
  · have hl := parentLayer_eq_layer_par (extractedLayeredGarden LG U hU hcp) q a ha
    have hp := congrArg LG.layer (subforestNodeMap_par U a ha)
    have hr := parentLayer_eq_layer_par LG q (subforestNodeMap U a)
      (subforestNodeMap_path_ne_nil U a ha)
    have hm := subforestNodeMap_not_mem_of_internal LG U hU a ha
    have hrel : Canon.Rel.rpl LG U q (subforestNodeMap U a) = LG.parentLayer q (subforestNodeMap U a) := by
      simp only [Canon.Rel.rpl, hm, ite_false]
    exact hl.trans (hp.trans (hr.symm.trans hrel.symm))

end WaveTurbulence.Induct
