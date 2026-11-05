/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchContraction
public import WaveTurbulence.Foundations.Molecule.SpliceBranchEquations
public import WaveTurbulence.Foundations.Molecule.ContractionPointEquiv
import Mathlib.Tactic

/-! # The literal old names of surviving PC children after CL splicing -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem clSplicedBranchEquiv_crown :
    clSplicedBranchEquiv hB hCL D (spliceCrownBranch (clSpliceBoundary hB hCL D)) = none := by
  change Equiv.optionCongr (Equiv.subtypeEquivRight (clSpliceRetainedBranch_iff hB hCL D))
    (spliceBranchOptionEquiv (clSpliceBoundary hB hCL D) (spliceCrownBranch (clSpliceBoundary hB hCL D))) = none
  rw [spliceBranchOptionEquiv_crown]
  rfl

theorem clSplicedBranchEquiv_piece (p : SpliceBranchPiece (clSpliceBoundary hB hCL D)) :
    clSplicedBranchEquiv hB hCL D (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p) =
      some ⟨spliceBranchPieceOld (clSpliceBoundary hB hCL D) p,
        (clSpliceRetainedBranch_iff hB hCL D _).mp (spliceBranchPieceOld_retained _ p)⟩ := by
  change Equiv.optionCongr (Equiv.subtypeEquivRight (clSpliceRetainedBranch_iff hB hCL D))
    (spliceBranchOptionEquiv (clSpliceBoundary hB hCL D) (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p)) = _
  rw [spliceBranchOptionEquiv_piece]
  rfl

/-- The crown keeps the old upper-joint name for its external parent edge. -/
@[expose] noncomputable def clSplicedBranchNameEquiv :
    GBranch (clSplicedGardenOfSlots hB hCL D).tree ≃ {v : GBranch G.tree // v ∉ S ∨ v = a} :=
  (clSplicedBranchEquiv hB hCL D).trans (contractionPointEquiv S a hB.2.1)

theorem clSplicedBranchName_crown :
    (clSplicedBranchNameEquiv hB hCL D (spliceCrownBranch (clSpliceBoundary hB hCL D))).1 = a := by
  change ((contractionPointEquiv S a hB.2.1)
    (clSplicedBranchEquiv hB hCL D (spliceCrownBranch (clSpliceBoundary hB hCL D)))).1 = a
  rw [clSplicedBranchEquiv_crown]
  rfl

theorem clSplicedBranchName_piece (p : SpliceBranchPiece (clSpliceBoundary hB hCL D)) :
    (clSplicedBranchNameEquiv hB hCL D (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p)).1 =
      spliceBranchPieceOld (clSpliceBoundary hB hCL D) p := by
  change ((contractionPointEquiv S a hB.2.1)
    (clSplicedBranchEquiv hB hCL D (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p))).1 = _
  rw [clSplicedBranchEquiv_piece]
  rfl

theorem clSpliceBoundary_nonroot (i : Fin 3) :
    ((clSpliceBoundary hB hCL D).node i).1.2 ≠ [] := by
  change (clBaseBoundary a b D.excluded D.kept
    (clBoundarySelector D.excluded (clSameSign a b) i)).1.2 ≠ []
  generalize clBoundarySelector D.excluded (clSameSign a b) i = j
  fin_cases j
  · exact child_nonroot G a D.excluded
  · exact child_nonroot G b 1
  · exact child_nonroot G b (otherOuterChild D.kept)

/-- Splicing preserves whether each external PC child is an original root. -/
theorem clSplicedBranchName_root_iff (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedBranchNameEquiv hB hCL D c).1.1.2 = [] ↔ c.1.2 = [] := by
  classical
  by_cases hc : c = spliceCrownBranch (clSpliceBoundary hB hCL D)
  · subst c
    rw [clSplicedBranchName_crown]
    rfl
  · obtain ⟨p,rfl⟩ := spliceBranchPieceNew_surjective_except_crown (clSpliceBoundary hB hCL D) c hc
    rw [clSplicedBranchName_piece]
    cases p with
    | inl l => rfl
    | inr p =>
      have hold := List.append_ne_nil_of_left_ne_nil (clSpliceBoundary_nonroot hB hCL D p.1) p.2.1
      have hnew := List.append_ne_nil_of_right_ne_nil a.1.2 (List.cons_ne_nil p.1 p.2.1)
      exact ⟨fun h => (hold h).elim,fun h => (hnew h).elim⟩

end WaveTurbulence.Mole
