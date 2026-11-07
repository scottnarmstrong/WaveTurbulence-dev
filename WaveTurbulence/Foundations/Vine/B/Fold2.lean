/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold1
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStep
public import WaveTurbulence.Foundations.FinalCount.RedSpliceMap
import Mathlib.Tactic

/-!
# VINE-B Part I (2): the node map of one CL splice agrees with the branch and leaf name maps
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem stepB_node (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) :
    (stepB hB hCL D c).toNode = spNode (clSpliceBoundary hB hCL D) c.toNode := by
  classical
  by_cases hc : c = spliceCrownBranch (clSpliceBoundary hB hCL D)
  · subst hc
    have h1 : (stepB hB hCL D (spliceCrownBranch (clSpliceBoundary hB hCL D))) = a :=
      clSplicedBranchName_crown hB hCL D
    rw [h1]
    exact Subtype.ext (spNode_crown _ _ rfl).symm
  · obtain ⟨p, rfl⟩ := spliceBranchPieceNew_surjective_except_crown (clSpliceBoundary hB hCL D) c hc
    have h1 : stepB hB hCL D (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p) =
        spliceBranchPieceOld (clSpliceBoundary hB hCL D) p := clSplicedBranchName_piece hB hCL D p
    rw [h1]
    cases p with
    | inl l =>
      apply Subtype.ext
      symm
      apply spNode_out
      rintro ⟨h2, h3⟩
      exact l.2 ⟨h2.symm, h3⟩
    | inr p =>
      obtain ⟨k, q⟩ := p
      apply Subtype.ext
      symm
      exact spNode_inside _ k q.1 _ rfl

theorem leafName_node (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedLeafNameEquiv hB hCL D l).1.toNode = spNode (clSpliceBoundary hB hCL D) l.toNode := by
  obtain ⟨p, rfl⟩ := splicePieceNew_surjective (clSpliceBoundary hB hCL D) l
  change (spliceLeafEquiv (clSpliceBoundary hB hCL D) (splicePieceNew (clSpliceBoundary hB hCL D) p)).1.toNode = _
  rw [spliceLeafEquiv_piece]
  cases p with
  | inl l =>
    apply Subtype.ext
    symm
    apply spNode_out
    rintro ⟨h2, h3⟩
    exact l.2 ⟨h2.symm, h3⟩
  | inr p =>
    obtain ⟨k, q⟩ := p
    apply Subtype.ext
    symm
    exact spNode_inside _ k q.1 _ rfl

end WaveTurbulence.VineB
