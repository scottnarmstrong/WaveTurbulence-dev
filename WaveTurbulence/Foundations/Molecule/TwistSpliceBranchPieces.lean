/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSplicedGarden

/-! # The actual retained-branch diagram for the two source CL splicings -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- Branches outside the upper splice site keep their exact address. -/
theorem coreBranchEquiv_outside_upper_val (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (b : GBranch G.tree)
    (hout : ¬ a.toNode.IsDesc b.toNode) : (coreBranchEquiv G P b).1 = b.1 := by
  apply coreBranchEquiv_fixed_val
  intro hd
  have hb := (Mole.cl_parent_strict_descendant G hB hCL).1
  exact hout ⟨hb.1.trans hd.1,hb.2.trans hd.2⟩

/-- The new actual branch piece corresponding to an old retained branch piece. -/
@[expose] noncomputable def twistedSpliceBranchPiece (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    Mole.SpliceBranchPiece (originalSpliceBoundary G P hB hCL D) →
      Mole.SpliceBranchPiece (twistedSpliceBoundary G P hB hCL hP D)
  | .inl b => .inl ⟨coreBranchEquiv G P b.1,by
      intro hd
      have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
      have fb := coreBranchEquiv_outside_upper_val G P hB hCL b.1 b.2
      change (coreBranchEquiv G P a).1.1 = (coreBranchEquiv G P b.1).1.1 ∧
        (coreBranchEquiv G P a).1.2 <+: (coreBranchEquiv G P b.1).1.2 at hd
      rw [fa,fb] at hd
      exact b.2 hd⟩
  | .inr ⟨i,q⟩ => .inr ⟨i,⟨q.1,by
      rw [unitTwist_boundarySubtree G P hB hCL hP D i]
      exact q.2⟩⟩

/-- Corresponding branch pieces have identical actual spliced addresses. -/
theorem twistedSpliceBranchPiece_new_val (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (p : Mole.SpliceBranchPiece (originalSpliceBoundary G P hB hCL D)) :
    (Mole.spliceBranchPieceNew (twistedSpliceBoundary G P hB hCL hP D) (twistedSpliceBranchPiece G P hB hCL hP D p)).1 =
      (Mole.spliceBranchPieceNew (originalSpliceBoundary G P hB hCL D) p).1 := by
  cases p with
  | inl b => exact coreBranchEquiv_outside_upper_val G P hB hCL b.1 b.2
  | inr p =>
    obtain ⟨i,q⟩ := p
    change ((coreBranchEquiv G P a).1.1,(coreBranchEquiv G P a).1.2 ++ i::q.1) = (a.1.1,a.1.2 ++ i::q.1)
    rw [selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1]

/-- The old names of corresponding retained branch pieces commute with actual branch transport. -/
theorem twistedSpliceBranchPiece_old (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (p : Mole.SpliceBranchPiece (originalSpliceBoundary G P hB hCL D)) :
    coreBranchEquiv G P (Mole.spliceBranchPieceOld (originalSpliceBoundary G P hB hCL D) p) =
      Mole.spliceBranchPieceOld (twistedSpliceBoundary G P hB hCL hP D) (twistedSpliceBranchPiece G P hB hCL hP D p) := by
  cases p with
  | inl b => rfl
  | inr p =>
    obtain ⟨i,q⟩ := p
    apply Subtype.ext
    have he := coreBranchEquiv_address G P (Mole.spliceBranchPieceOld (originalSpliceBoundary G P hB hCL D) (.inr ⟨i,q⟩))
    exact he.trans (unitTwist_boundary_address_append G P hB hCL hP D i q.1)

/-- The upper crown representative is the same actual branch after casting the equal forests. -/
theorem twisted_spliceCrown_cast (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    forestBranchCast (unitTwist_splicedForest G P hB hCL hP D).symm
      (Mole.spliceCrownBranch (originalSpliceBoundary G P hB hCL D)) =
      Mole.spliceCrownBranch (twistedSpliceBoundary G P hB hCL hP D) := by
  apply Subtype.ext
  change a.1 = (coreBranchEquiv G P a).1
  exact (selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1).symm

/-- The literal inherited old branching-node names commute with the actual unit twist. -/
theorem unitTwist_spliceBranch_diagram (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) (b : GBranch (originalSplicedGarden G P hB hCL D).tree) :
    coreBranchEquiv G P (Mole.clSplicedBranchNameEquiv hB hCL D b).1 =
      (Mole.clSplicedBranchNameEquiv (isBlock_twistedAtoms G P hB)
        (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
        (forestBranchCast (unitTwist_splicedForest G P hB hCL hP D).symm b)).1 := by
  by_cases hb : b = Mole.spliceCrownBranch (originalSpliceBoundary G P hB hCL D)
  · subst b
    have h₀ := Mole.clSplicedBranchName_crown hB hCL D
    have h₁ := Mole.clSplicedBranchName_crown
      (isBlock_twistedAtoms G P hB)
      (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
    have hc := congrArg (fun z => (Mole.clSplicedBranchNameEquiv
      (isBlock_twistedAtoms G P hB)
      (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D) z).1)
      (twisted_spliceCrown_cast G P hB hCL hP D)
    exact (congrArg (coreBranchEquiv G P) h₀).trans (h₁.symm.trans hc.symm)
  · obtain ⟨p,rfl⟩ := Mole.spliceBranchPieceNew_surjective_except_crown (originalSpliceBoundary G P hB hCL D) b hb
    have he : forestBranchCast (unitTwist_splicedForest G P hB hCL hP D).symm
        (Mole.spliceBranchPieceNew (originalSpliceBoundary G P hB hCL D) p) =
      Mole.spliceBranchPieceNew (twistedSpliceBoundary G P hB hCL hP D) (twistedSpliceBranchPiece G P hB hCL hP D p) :=
      Subtype.ext (twistedSpliceBranchPiece_new_val G P hB hCL hP D p).symm
    have h₀ := Mole.clSplicedBranchName_piece hB hCL D p
    have h₁ := Mole.clSplicedBranchName_piece (isBlock_twistedAtoms G P hB)
      (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
      (twistedSpliceBranchPiece G P hB hCL hP D p)
    have hc := congrArg (fun z => (Mole.clSplicedBranchNameEquiv
      (isBlock_twistedAtoms G P hB)
      (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D) z).1) he
    exact (congrArg (coreBranchEquiv G P) h₀).trans
      ((twistedSpliceBranchPiece_old G P hB hCL hP D p).trans (h₁.symm.trans hc.symm))

end WaveTurbulence.Twist
