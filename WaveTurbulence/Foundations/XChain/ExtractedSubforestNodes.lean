/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedSubforest
/-! Exact node and edge transport for the ordered antichain subforest. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def subforestNodeMap {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (a : GNode (subforestTrees U)) : GNode tree :=
  ⟨((subforestRoot U a.1.1).1.1, (subforestRoot U a.1.1).1.2 ++ a.1.2),
    (subtreeAt_nodes_iff _ _ (subforestRoot U a.1.1).2 _).mp a.2⟩

noncomputable def subforestBranchMap {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (a : GBranch (subforestTrees U)) : GBranch tree :=
  ⟨((subforestRoot U a.1.1).1.1, (subforestRoot U a.1.1).1.2 ++ a.1.2),
    (subtreeAt_branching_iff _ _ (subforestRoot U a.1.1).2 _).mp a.2⟩

theorem subforestBranchMap_child {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (b : GBranch (subforestTrees U)) (i : Fin 3) :
    (subforestBranchMap U b).child i = subforestNodeMap U (b.child i) := by
  apply Subtype.ext
  exact Prod.ext rfl (List.append_assoc _ _ _)

theorem subforestNodeMap_below {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (a : GNode (subforestTrees U)) :
    (subforestRoot U a.1.1).IsDesc (subforestNodeMap U a) := ⟨rfl, List.prefix_append _ _⟩

theorem subforestNodeMap_isDesc_iff {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (a b : GNode (subforestTrees U)) :
    (subforestNodeMap U a).IsDesc (subforestNodeMap U b) ↔ a.IsDesc b := by
  constructor
  · intro h
    have ha := (subforestNodeMap_below U a).trans h
    have hb := subforestNodeMap_below U b
    have he : subforestRoot U a.1.1 = subforestRoot U b.1.1 := by
      by_contra hne
      have hinc := hU _ (subforestRoot_mem U a.1.1) _ (subforestRoot_mem U b.1.1) hne
      rcases Canon.isDesc_total ha hb with hd | hd
      · exact hinc.1 hd
      · exact hinc.2 hd
    have hi : a.1.1 = b.1.1 := (U.equivFin.symm).injective (Subtype.ext he)
    refine ⟨hi, ?_⟩
    obtain ⟨r, hr⟩ := h.2
    have hp := congrArg (fun u : GNode LG.garden.tree => u.1.2) he
    have hc : (subforestRoot U a.1.1).1.2 ++ (a.1.2 ++ r) =
        (subforestRoot U a.1.1).1.2 ++ b.1.2 := by
      exact (List.append_assoc _ _ _).symm.trans
        (hr.trans (congrArg (fun s => s ++ b.1.2) hp.symm))
    exact ⟨r, List.append_cancel_left hc⟩
  · rintro ⟨hi, r, hr⟩
    have he := congrArg (subforestRoot U) hi
    have hp := congrArg (fun u : GNode LG.garden.tree => u.1.2) he
    have hroot := congrArg (fun u : GNode LG.garden.tree => u.1.1) he
    refine ⟨hroot, r, ?_⟩
    change ((subforestRoot U a.1.1).1.2 ++ a.1.2) ++ r =
      (subforestRoot U b.1.1).1.2 ++ b.1.2
    rw [List.append_assoc, hr, hp]

end WaveTurbulence.Induct
