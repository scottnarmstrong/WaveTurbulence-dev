/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistCorePreservation

/-! # Separation of the lower sites in a source family of CL vines

TARGET Definition twist: two distinct vines have at most one common
atom. The common-joint restriction is stronger than the separation used
here. In particular, two core vines cannot have the same lower joint.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- At most one common atom, as required for distinct source family members. -/
@[expose] def SeparatedGroups {A : Type*} (S T : Finset A) : Prop :=
  ∀ x ∈ S, x ∈ T → ∀ y ∈ S, y ∈ T → x = y

variable {w : ℕ} (G : Garden w) (P Q : CorePlacement G)
variable {S T : Finset (GBranch G.tree)} {a c : GBranch G.tree}

/-- A branch is different from its own immediate parent. -/
theorem branch_ne_parent (b : GBranch G.tree) (hn : b.1.2 ≠ []) :
    b ≠ GNode.parent b.toNode hn := by
  intro he
  have hh := Molecpl.parent_height G hn he.symm
  omega

/-- Two CL groups meeting in at most one atom have different lower joints. -/
theorem separated_lower_ne (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower)
    (hC : G.molecule.IsBlock T c Q.lower)
    (hDL : Mole.CLParentPattern G T c Q.lower) (hsep : SeparatedGroups S T) : P.lower ≠ Q.lower := by
  intro he
  have hp : GNode.parent P.lower.toNode P.nonroot ∈ S := hCL.2.2
  have hq : GNode.parent P.lower.toNode P.nonroot ∈ T := by
    simpa only [he] using hDL.2.2
  exact branch_ne_parent G P.lower P.nonroot
    (hsep P.lower hB.2.2.1 (he.symm ▸ hC.2.2.1) _ hp hq)

/-- The paired incidence at the retained lower leaf is not a self-loop. -/
theorem placement_paired_parent_ne :
    GNode.parent (G.pair P.retained).toNode P.paired_nonroot ≠ P.lower := by
  intro he
  have hdesc : P.lower.toNode.IsDesc (G.pair P.retained).toNode := by
    rw [← he]
    exact ⟨rfl,List.dropLast_prefix _⟩
  exact P.paired_outside hdesc

/-- Another CL group keeps its upper/lower parent pattern under the unit twist. -/
theorem clParentPattern_twist_separated
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P)
    (hC : G.molecule.IsBlock T c Q.lower) (hDL : Mole.CLParentPattern G T c Q.lower)
    (hsep : SeparatedGroups S T) :
    Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P T)
      (coreBranchEquiv G P c) (coreBranchEquiv G P Q.lower) := by
  have hne := separated_lower_ne G P Q hB hCL hC hDL hsep
  constructor
  · intro hc
    by_cases he : c = P.lower
    · obtain ⟨_hn,hc⟩ := hc
      have hh : GNode.parent (G.pair P.retained).toNode P.paired_nonroot ∈ T := by
        have hn : GNode.parent (coreBranchEquiv G P P.lower).toNode
            ((coreBranchEquiv_nonroot G P P.lower).mpr P.nonroot) ∈ twistedAtoms G P T := by
          subst c
          exact hc
        exact (mem_twistedAtoms G P T _).mp ((lower_new_parent G P) ▸ hn)
      have hp := placement_paired_parent_mem G P hP
      have heq := hsep P.lower hB.2.2.1 (he ▸ hC.2.1) _ hp hh
      exact placement_paired_parent_ne G P heq.symm
    · have hz := (Mole.zero_mem_internalPositions (unitTwistGarden G P)
          ((mem_twistedAtoms G P T c).mpr hC.2.1)).mpr hc
      have ho := (internalPositions_twist_other G P T c he 0).mp hz
      exact hDL.1 ((Mole.zero_mem_internalPositions G hC.2.1).mp ho)
  · refine ⟨(coreBranchEquiv_nonroot G P Q.lower).mpr Q.nonroot,?_⟩
    have hp := (mem_twistedAtoms G P T _).mpr hDL.2.2
    exact (branchParent_transport G P Q.lower Q.nonroot hne.symm).symm ▸ hp

end WaveTurbulence.Twist
