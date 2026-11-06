/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniAGraphCollapse

/-! # The actual collapse of an unordered A mini is independent of its root orientation -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem MiniAOccurrence.collapse_flip_eq {w : ℕ} {G : Garden w} {b c : GBranch G.tree}
    {k : MiniCplCode} (h : MiniAOccurrence G b c k) (hG : G.IsPlain) :
    collapseCoupleGarden (h.flip.isSubCouple hG) = collapseCoupleGarden (h.isSubCouple hG) := by
  classical
  let LG : LabelledGarden w (GBranch G.tree) := ⟨G,Function.Embedding.refl _⟩
  let L := LG.collapseCouple (h.isSubCouple hG)
  let R := LG.collapseCouple (h.flip.isSubCouple hG)
  let D := LG.graphDipole_of_branch hG (h.branchDipole hG)
  let E := LG.graphDipole_of_branch hG (h.flip.branchDipole hG)
  have hd : D.contract = E.contract := D.contract_eq_of_unordered E LG.graph.involutive (Or.inr ⟨rfl,rfl⟩)
  have hg : L.graph = R.graph := PortMatching.ext
    ((LG.miniA_graph_contract h hG).trans (hd.trans (LG.miniA_graph_contract h.flip hG).symm))
  exact (L.garden_eq_of_graph_eq R (collapseCoupleGarden_plain _ hG)
    (collapseCoupleGarden_plain _ hG) rfl hg).symm

end WaveTurbulence.Reg.Skeleton
