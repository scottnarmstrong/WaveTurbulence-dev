/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistScenarioRelations

/-! # The actual (II-a,b) and (II-c,d) scenario switches

TARGET Remark explaintwist L1441: the local source configurations are
exchanged by the concrete designated unit twist. Selected ordinary
branches retain their actual addresses and their LP/PC relations.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The old lower parent identifies the endpoint of the new outer LP pair. -/
theorem new_outer_of_parent {p : GBranch G.tree} (hp : Molecpl.IsParent G p P.lower) :
    Molecpl.OuterLeafPairAt (unitTwistGarden G P) (coreBranchEquiv G P P.lower) (coreBranchEquiv G P p) := by
  obtain ⟨_hn,hp⟩ := hp
  have he : GNode.parent P.lower.toNode P.nonroot = p := hp
  exact he ▸ new_outer_leaf_pair G P

/-- The designated old outer LP endpoint becomes the new lower parent. -/
theorem new_parent_of_outer {S : Finset (GBranch G.tree)} {a p : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) (hp : p ∈ S)
    (h : Molecpl.OuterLeafPairAt G P.lower p) :
    Molecpl.IsParent (unitTwistGarden G P) (coreBranchEquiv G P p) (coreBranchEquiv G P P.lower) :=
  ⟨(coreBranchEquiv_nonroot G P P.lower).mpr P.nonroot,
    (lower_new_parent G P).trans (congrArg (coreBranchEquiv G P) (placement_paired_parent G P hB hCL hP hp h))⟩

variable {S : Finset (GBranch G.tree)} {a p q : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) (hp : p ∈ S) (hq : q ∈ S)
    (hpl : p ≠ P.lower) (hql : q ≠ P.lower) (hpq : p ≠ q)
include hB hCL hP hp hq hpl hql hpq

/-- The designated actual twist sends source (II-a) to (II-b). -/
theorem typeII_A_to_B (h : Molecpl.IsTypeIIA G a P.lower p q) :
    Molecpl.IsTypeIIB (unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P p) (coreBranchEquiv G P q) := by
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have fp := selected_branch_fixed G P hB hCL hP hp hpl
  have fq := selected_branch_fixed G P hB hCL hP hq hql
  exact ⟨new_parent_of_outer G P hB hCL hP hp h.2.1,new_outer_of_parent G P h.1,
    doubleLeafPairAt_unitTwist G P hpl hql hpq h.2.2.1,
    (fixed_branch_desc_iff G P fp fq).not.mpr h.2.2.2.1,
    (fixed_branch_desc_iff G P fq fp).not.mpr h.2.2.2.2.1,
    (fixed_branch_desc_iff G P fa fp).mpr h.2.2.2.2.2.1,
    (fixed_branch_desc_iff G P fa fq).mpr h.2.2.2.2.2.2⟩

/-- The designated actual twist sends source (II-b) to (II-a). -/
theorem typeII_B_to_A (h : Molecpl.IsTypeIIB G a P.lower p q) :
    Molecpl.IsTypeIIA (unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P p) (coreBranchEquiv G P q) := by
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have fp := selected_branch_fixed G P hB hCL hP hp hpl
  have fq := selected_branch_fixed G P hB hCL hP hq hql
  exact ⟨new_parent_of_outer G P hB hCL hP hq h.2.1,new_outer_of_parent G P h.1,
    doubleLeafPairAt_unitTwist G P hpl hql hpq h.2.2.1,
    (fixed_branch_desc_iff G P fp fq).not.mpr h.2.2.2.1,
    (fixed_branch_desc_iff G P fq fp).not.mpr h.2.2.2.2.1,
    (fixed_branch_desc_iff G P fa fp).mpr h.2.2.2.2.2.1,
    (fixed_branch_desc_iff G P fa fq).mpr h.2.2.2.2.2.2⟩

omit hq in
/-- The designated actual twist sends source (II-c) to (II-d). -/
theorem typeII_C_to_D (h : Molecpl.IsTypeIIC G a P.lower p q) :
    Molecpl.IsTypeIID (unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P p) (coreBranchEquiv G P q) := by
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have fp := selected_branch_fixed G P hB hCL hP hp hpl
  exact ⟨new_parent_of_outer G P hB hCL hP hp h.2.2.2.1,isParent_unitTwist G P hql h.1,
    leafPairAt_unitTwist G P hpl hql hpq h.2.2.1,new_outer_of_parent G P h.2.1,
    (fixed_branch_desc_iff G P fa fp).mpr h.2.2.2.2⟩

/-- The designated actual twist sends source (II-d) to (II-c). -/
theorem typeII_D_to_C (h : Molecpl.IsTypeIID G a P.lower p q) :
    Molecpl.IsTypeIIC (unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P p) (coreBranchEquiv G P q) := by
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  have fp := selected_branch_fixed G P hB hCL hP hp hpl
  exact ⟨isParent_unitTwist G P hql h.2.1,new_parent_of_outer G P hB hCL hP hq h.2.2.2.1,
    leafPairAt_unitTwist G P hpl hql hpq h.2.2.1,new_outer_of_parent G P h.1,
    (fixed_branch_desc_iff G P fa fp).mpr h.2.2.2.2⟩

end WaveTurbulence.Twist
