/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLSpliceGarden
public import WaveTurbulence.Foundations.Molecule.SpliceBranchEquiv
public import WaveTurbulence.Foundations.Molecule.BlockContraction
import Mathlib.Tactic

/-! # The actual atom equivalence for CL contraction
TARGET `block_clcn` (2): one merged crown plus precisely the old atoms
outside the removed realization. Dart and orientation commutation follow
in the subsequent incidence proof.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset

private theorem retained_branch_logic {A B C D E : Prop}
    (h : E ↔ A ∧ ¬ B ∧ ¬ C ∧ ¬ D) : (¬ A ∨ B ∨ C ∨ D) ↔ ¬ E := by tauto

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem clSpliceRetainedBranch_iff (c : GBranch G.tree) :
    IsSpliceRetainedBranch (clSpliceBoundary hB hCL D) c ↔ c ∉ S := by
  have hL := (cl_branch_realization_iff G hB hCL c).trans
    (cl_pruned_region_explicit G D.upper D.lower c.toNode)
  rw [forall_excluded_children_iff D.kept D.kept_ne_middle] at hL
  have hdesc := clSignedBoundary_descendant_union hB hCL D.excluded D.kept
    D.excluded_missing D.excluded_ne_middle c.toNode
  change (¬ a.toNode.IsDesc c.toNode ∨
    ∃ i, ((clSpliceBoundary hB hCL D).node i).IsDesc c.toNode) ↔ c ∉ S
  exact (or_congr Iff.rfl hdesc).trans (retained_branch_logic hL)

/-- Actual branches of the constructed garden are exactly the contracted
vertex names: the crown is merged, and all other atoms are old survivors. -/
@[expose] noncomputable def clSplicedBranchEquiv :
    GBranch (clSplicedGardenOfSlots hB hCL D).tree ≃ ContractVertex S :=
  (spliceBranchOptionEquiv (clSpliceBoundary hB hCL D)).trans
    (Equiv.optionCongr (Equiv.subtypeEquivRight (clSpliceRetainedBranch_iff hB hCL D)))

include hB in
theorem garden_contractGroup_atoms_univ : (contractGroup G.molecule S).atoms = univ := by
  classical
  ext v
  simp only [mem_univ,iff_true]
  cases v with
  | none =>
    apply mem_image.mpr
    exact ⟨a,mem_univ _,(contractVertex_eq_none S a).mpr hB.2.1⟩
  | some v =>
    apply mem_image.mpr
    refine ⟨v.1,mem_univ _,?_⟩
    simp only [contractVertex,dite_eq_right v.2]

/-- All contracted vertex names are actual atoms because the garden's
old atom set is the full branching-node carrier and the block is nonempty. -/
@[expose] noncomputable def gardenContractAtomEquiv :
    ContractVertex S ≃ (contractGroup G.molecule S).atoms where
  toFun v := ⟨v,by rw [garden_contractGroup_atoms_univ hB]; exact mem_univ _⟩
  invFun v := v.1
  left_inv _ := rfl
  right_inv v := Subtype.ext rfl

@[expose] noncomputable def clSplicedBranchAtomEquiv :
    GBranch (clSplicedGardenOfSlots hB hCL D).tree ≃ (contractGroup G.molecule S).atoms :=
  (clSplicedBranchEquiv hB hCL D).trans (gardenContractAtomEquiv hB)

end WaveTurbulence.Mole
