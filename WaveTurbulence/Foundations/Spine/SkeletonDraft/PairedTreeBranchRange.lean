/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseBranchLabels

/-! # Exact range of actual branch labels after an embedded paired-tree collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem collapsePairedTreeBranchEmbedding_range {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (d : GBranch G.tree) :
    d ∈ Set.range (collapsePairedTreeBranchEmbedding h) ↔ ¬ Below a.1 d.1 ∨ Below b.1 d.1 := by
  rw [replacement_branch_image G.tree a b (Comb.collapseDataOfDesc h.1).path (collapseData_frame h.1) d]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,congrArg (fun z : GBranch G.tree => z.1) hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,Subtype.ext hx⟩

end WaveTurbulence.Reg.Skeleton
