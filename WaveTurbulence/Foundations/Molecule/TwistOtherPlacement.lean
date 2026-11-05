/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSeparatedVines

/-! # Transporting another designated core site through a source unit twist

TARGET Definition twist: separation is a source premise, while all new
placement and CL conditions below are proved from it.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P Q : CorePlacement G)
variable {S T : Finset (GBranch G.tree)} {a c : GBranch G.tree}

/-- Parent addresses agree when actual nonroot leaves agree. -/
theorem leaf_parent_congr {l m : GLeaf G.tree} (hl : l.1.2 ≠ []) (hm : m.1.2 ≠ []) (he : l = m) :
    GNode.parent l.toNode hl = GNode.parent m.toNode hm := by
  apply Subtype.ext
  exact congrArg (fun l : GLeaf G.tree => (l.1.1,l.1.2.dropLast)) he

/-- Different lower joints have different retained child leaves. -/
theorem retained_ne_of_lower_ne (hne : P.lower ≠ Q.lower) : P.retained ≠ Q.retained := by
  intro he
  have hp := parent_eq_of_child (retained_nonroot G P) P.child
  have hq := parent_eq_of_child (retained_nonroot G Q) Q.child
  exact hne (hp.symm.trans ((leaf_parent_congr G _ _ he).trans hq))

/-- A retained pair cannot connect the lower sites of two separated CL groups. -/
theorem separated_retained_ne_pair
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P)
    (hC : G.molecule.IsBlock T c Q.lower) (hDL : Mole.CLParentPattern G T c Q.lower)
    (hQ : IsPlacementAt G T Q.lower Q) (hsep : SeparatedGroups S T) :
    Q.retained ≠ G.pair P.retained := by
  intro he
  have hn := separated_lower_ne G P Q hB hCL hC hDL hsep
  have hqs : Q.lower ∈ S := by
    have hp := placement_paired_parent_mem G P hP
    have hh := parent_eq_of_child (retained_nonroot G Q) Q.child
    have hv : GNode.parent (G.pair P.retained).toNode P.paired_nonroot = Q.lower := by
      exact (leaf_parent_congr G _ _ he.symm).trans hh
    exact hv ▸ hp
  have hpt : P.lower ∈ T := by
    have hp := placement_paired_parent_mem G Q hQ
    have hv : G.pair Q.retained = P.retained := by rw [he,G.pair_pair]
    have hh : GNode.parent (G.pair Q.retained).toNode Q.paired_nonroot = P.lower := by
      exact (leaf_parent_congr G _ _ hv).trans (parent_eq_of_child (retained_nonroot G P) P.child)
    exact hh ▸ hp
  exact hn (hsep P.lower hB.2.2.1 hpt Q.lower hqs hC.2.2.1)

/-- The other retained child has its unchanged ordered slot after transport. -/
theorem other_retained_child (hne : P.lower ≠ Q.lower)
    (hl : Q.retained ≠ G.pair P.retained) :
    (coreLeafEquiv G P Q.retained).toNode = (coreBranchEquiv G P Q.lower).child Q.keep := by
  have h := leaf_child_transport G P Q.child hl
  have hv : Q.lower.1 ≠ P.lower.1 := fun he => hne (Subtype.ext he.symm)
  simpa only [exchangeChildSlot,hv,ite_false] using h

/-- The other pair remains outside its lower subtree, derived from the new CL geometry. -/
theorem other_paired_outside
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P)
    (hC : G.molecule.IsBlock T c Q.lower) (hDL : Mole.CLParentPattern G T c Q.lower)
    (hQ : IsPlacementAt G T Q.lower Q) (hsep : SeparatedGroups S T) :
    ¬ (coreBranchEquiv G P Q.lower).toNode.IsDesc (coreLeafEquiv G P (G.pair Q.retained)).toNode := by
  have hne := separated_lower_ne G P Q hB hCL hC hDL hsep
  have hl := separated_retained_ne_pair G P Q hB hCL hP hC hDL hQ hsep
  have hr := retained_ne_of_lower_ne G P Q hne
  have hpair : G.pair Q.retained ≠ G.pair P.retained := by
    intro he
    have hh := congrArg G.pair he
    simp only [G.pair_pair] at hh
    exact hr hh.symm
  have hBt := isBlock_twistedAtoms G P hC
  have hCLt := clParentPattern_twist_separated G P Q hB hCL hP hC hDL hsep
  have ht : ∀ z ∈ twistedAtoms G P T, (coreBranchEquiv G P Q.lower).toNode.IsDesc z.toNode →
      z = coreBranchEquiv G P Q.lower := by
    apply Molecpl.cl_terminal_branch (unitTwistGarden G P) hBt hCLt hBt.2.2.1
    intro i hi
    have hiold := (internalPositions_twist_other G P T Q.lower hne.symm i.succ).mp hi
    have hik := (hQ.2 i).mp hiold
    exact ⟨coreLeafEquiv G P Q.retained,hik.symm ▸ other_retained_child G P Q hne hl⟩
  have hp := leafParent_transport G P (G.pair Q.retained) Q.paired_nonroot hpair
  have hpmem := (mem_twistedAtoms G P T _).mpr (placement_paired_parent_mem G Q hQ)
  have hpne : coreBranchEquiv G P (GNode.parent (G.pair Q.retained).toNode Q.paired_nonroot) ≠
      coreBranchEquiv G P Q.lower := fun he =>
    placement_paired_parent_ne G Q ((coreBranchEquiv G P).injective he)
  have hchild := (Mole.parent_child_eq_node (coreLeafEquiv G P (G.pair Q.retained)).toNode
    ((coreLeafEquiv_nonroot G P (G.pair Q.retained)).mpr Q.paired_nonroot)).symm
  have hchild' := hchild.trans (congrArg (fun v : GBranch (unitTwistGarden G P).tree =>
    v.child ((coreLeafEquiv G P (G.pair Q.retained)).1.2.getLast
      ((coreLeafEquiv_nonroot G P (G.pair Q.retained)).mpr Q.paired_nonroot))) hp)
  exact child_leaf_outside_of_terminal (unitTwistGarden G P) hpmem hpne ht hchild'

/-- The actual transported core placement at the other source family member. -/
@[expose] noncomputable def otherPlacement
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P)
    (hC : G.molecule.IsBlock T c Q.lower) (hDL : Mole.CLParentPattern G T c Q.lower)
    (hQ : IsPlacementAt G T Q.lower Q) (hsep : SeparatedGroups S T) : CorePlacement (unitTwistGarden G P) where
  lower := coreBranchEquiv G P Q.lower
  retained := coreLeafEquiv G P Q.retained
  nonroot := (coreBranchEquiv_nonroot G P Q.lower).mpr Q.nonroot
  paired_nonroot := by
    have he := unitTwistGarden_pair G P Q.retained
    exact he.symm ▸ (coreLeafEquiv_nonroot G P (G.pair Q.retained)).mpr Q.paired_nonroot
  keep := Q.keep
  unmarked := (unitTwistGarden_mark G P Q.retained).trans Q.unmarked
  child := other_retained_child G P Q
    (separated_lower_ne G P Q hB hCL hC hDL hsep)
    (separated_retained_ne_pair G P Q hB hCL hP hC hDL hQ hsep)
  outer := Q.outer
  paired_outside := by
    have he := congrArg GLeaf.toNode (unitTwistGarden_pair G P Q.retained)
    exact he.symm ▸ other_paired_outside G P Q hB hCL hP hC hDL hQ hsep

/-- The other transported site keeps exactly its designated internal lower slot. -/
theorem otherPlacement_at
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P)
    (hC : G.molecule.IsBlock T c Q.lower) (hDL : Mole.CLParentPattern G T c Q.lower)
    (hQ : IsPlacementAt G T Q.lower Q) (hsep : SeparatedGroups S T) :
    IsPlacementAt (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P Q.lower)
      (otherPlacement G P Q hB hCL hP hC hDL hQ hsep) := by
  refine ⟨rfl,fun i => ?_⟩
  exact (internalPositions_twist_other G P T Q.lower
    (separated_lower_ne G P Q hB hCL hC hDL hsep).symm i.succ).trans (hQ.2 i)

end WaveTurbulence.Twist
