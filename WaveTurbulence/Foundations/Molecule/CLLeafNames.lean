/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchNames
import Mathlib.Tactic

/-! # Literal old leaf names, marks, roots and pairing after CL splicing -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

@[expose] noncomputable def clSplicedLeafNameEquiv :
    GLeaf (clSplicedGardenOfSlots hB hCL D).tree ≃
      {l : GLeaf G.tree // IsSpliceRetainedLeaf (clSpliceBoundary hB hCL D) l} :=
  spliceLeafEquiv (clSpliceBoundary hB hCL D)

theorem clSplicedLeafName_mark (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedGardenOfSlots hB hCL D).mark l = G.mark (clSplicedLeafNameEquiv hB hCL D l).1 := rfl

theorem clSplicedLeafName_pair (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedLeafNameEquiv hB hCL D ((clSplicedGardenOfSlots hB hCL D).pair l)).1 =
      G.pair (clSplicedLeafNameEquiv hB hCL D l).1 := by
  exact congrArg Subtype.val (transportedLeafPair_comm G
    (IsSpliceRetainedLeaf (clSpliceBoundary hB hCL D))
    (clSignedBoundary_pair_closed hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle
      D.kept_ne_middle D.upper D.lower)
    (spliceLeafEquiv (clSpliceBoundary hB hCL D)) l)

theorem clSplicedLeafName_root_iff (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedLeafNameEquiv hB hCL D l).1.1.2 = [] ↔ l.1.2 = [] := by
  obtain ⟨p,rfl⟩ := splicePieceNew_surjective (clSpliceBoundary hB hCL D) l
  change (spliceLeafEquiv (clSpliceBoundary hB hCL D)
    (splicePieceNew (clSpliceBoundary hB hCL D) p)).1.1.2 = [] ↔ _
  rw [spliceLeafEquiv_piece]
  cases p with
  | inl l => rfl
  | inr p =>
    have hold := List.append_ne_nil_of_left_ne_nil (clSpliceBoundary_nonroot hB hCL D p.1) p.2.1
    have hnew := List.append_ne_nil_of_right_ne_nil a.1.2 (List.cons_ne_nil p.1 p.2.1)
    exact ⟨fun h => (hold h).elim,fun h => (hnew h).elim⟩

theorem clSplicedLeafName_sign (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree) :
    (clSplicedGardenOfSlots hB hCL D).sign l.toNode =
      G.sign (clSplicedLeafNameEquiv hB hCL D l).1.toNode :=
  spliceLeafEquiv_sign (clSpliceBoundary hB hCL D)
    (clSignedBoundary_sign hB hCL D.excluded D.kept D.excluded_missing D.excluded_ne_middle D.kept_ne_middle) l

end WaveTurbulence.Mole
