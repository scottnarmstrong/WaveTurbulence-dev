/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpliceBranchPieces

/-! # Equality of inherited decorations on the common actual spliced garden

TARGET twistexplain (e). The crown keeps the upper old name, surviving
branches keep their actual old names, and leaves use the accepted splice
leaf pullback. All surviving labels are unchanged by the unit twist.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Change only the node-membership proof across equality of two ordered forests. -/
@[expose] def forestNodeCast {w : ℕ} {F H : Fin w → TTree} (he : F = H) : GNode F ≃ GNode H where
  toFun n := ⟨n.1,by simpa only [← he] using n.2⟩
  invFun n := ⟨n.1,by simpa only [he] using n.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Inherit each actual surviving old node label under the accepted CL splice. -/
@[expose] noncomputable def inheritCLLabels {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (D : Mole.CLSpliceSlots G S a b) {E : Type*} (κ : GNode G.tree → E) :
    GNode (Mole.clSplicedGardenOfSlots hB hCL D).tree → E :=
  fun n => Sum.elim
    (fun v => κ (Mole.clSplicedBranchNameEquiv hB hCL D v).1.toNode)
    (fun l => κ (Mole.spliceLeafEquiv (Mole.clSpliceBoundary hB hCL D) l).1.toNode)
    ((nodePieceEquiv (Mole.clSplicedGardenOfSlots hB hCL D).tree).symm n)

/-- Actual branch labels are pulled back by the accepted surviving-name equivalence. -/
theorem inheritCLLabels_branch {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (D : Mole.CLSpliceSlots G S a b)
    {E : Type*} (κ : GNode G.tree → E) (v : GBranch (Mole.clSplicedGardenOfSlots hB hCL D).tree) :
    inheritCLLabels hB hCL D κ v.toNode = κ (Mole.clSplicedBranchNameEquiv hB hCL D v).1.toNode := by
  let e := nodePieceEquiv (Mole.clSplicedGardenOfSlots hB hCL D).tree
  exact congrArg (Sum.elim (fun v => κ (Mole.clSplicedBranchNameEquiv hB hCL D v).1.toNode)
    (fun l => κ (Mole.spliceLeafEquiv (Mole.clSpliceBoundary hB hCL D) l).1.toNode)) (e.symm_apply_apply (.inl v))

/-- Actual leaf labels are pulled back by the accepted retained-leaf equivalence. -/
theorem inheritCLLabels_leaf {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (D : Mole.CLSpliceSlots G S a b)
    {E : Type*} (κ : GNode G.tree → E) (l : GLeaf (Mole.clSplicedGardenOfSlots hB hCL D).tree) :
    inheritCLLabels hB hCL D κ l.toNode = κ (Mole.spliceLeafEquiv (Mole.clSpliceBoundary hB hCL D) l).1.toNode := by
  let e := nodePieceEquiv (Mole.clSplicedGardenOfSlots hB hCL D).tree
  exact congrArg (Sum.elim (fun v => κ (Mole.clSplicedBranchNameEquiv hB hCL D v).1.toNode)
    (fun l => κ (Mole.spliceLeafEquiv (Mole.clSpliceBoundary hB hCL D) l).1.toNode)) (e.symm_apply_apply (.inr l))

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- Every inherited node label on the common source-spliced garden is exactly unchanged. -/
theorem unitTwist_inherited_labels (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) {E : Type*} (κ : GNode G.tree → E)
    (n : GNode (originalSplicedGarden G P hB hCL D).tree) :
    inheritCLLabels (isBlock_twistedAtoms G P hB)
        (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
        (twistNodeLabels G P κ) (forestNodeCast (unitTwist_splicedForest G P hB hCL hP D).symm n) =
      inheritCLLabels hB hCL D κ n := by
  obtain ⟨p,rfl⟩ := (nodePieceEquiv (originalSplicedGarden G P hB hCL D).tree).surjective n
  cases p with
  | inl v =>
    let old := (Mole.clSplicedBranchNameEquiv hB hCL D v)
    have hne : old.1 ≠ P.lower := by
      intro he
      rcases old.2 with hn | ha
      · exact hn (he.symm ▸ hB.2.2.1)
      · exact hB.2.2.2.1 (ha.symm.trans he)
    have hcast : forestNodeCast (unitTwist_splicedForest G P hB hCL hP D).symm v.toNode =
        (forestBranchCast (unitTwist_splicedForest G P hB hCL hP D).symm v).toNode := Subtype.ext rfl
    have hn := unitTwist_spliceBranch_diagram G P hB hCL hP D v
    calc
      _ = twistNodeLabels G P κ
          (Mole.clSplicedBranchNameEquiv (isBlock_twistedAtoms G P hB)
            (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
            (forestBranchCast (unitTwist_splicedForest G P hB hCL hP D).symm v)).1.toNode := by
        exact (congrArg (inheritCLLabels
          (isBlock_twistedAtoms G P hB)
          (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
          (twistNodeLabels G P κ)) hcast).trans (inheritCLLabels_branch _ _ _ _ _)
      _ = twistNodeLabels G P κ (coreBranchEquiv G P old.1).toNode := congrArg
        (fun b => twistNodeLabels G P κ b.toNode) hn.symm
      _ = κ old.1.toNode := twistNodeLabels_branch G P κ old.1 hne
      _ = _ := (inheritCLLabels_branch _ _ _ _ v).symm
  | inr l =>
    let old := Mole.spliceLeafEquiv (originalSpliceBoundary G P hB hCL D) l
    have hnot : ¬ Mole.IsInternalLeaf G S old.1 :=
      (Mole.clSignedBoundary_retained_iff hB hCL D.excluded D.kept
        D.excluded_missing D.excluded_ne_middle D.kept_ne_middle D.upper D.lower old.1).mp old.2
    have hpairInternal : Mole.IsInternalLeaf G S (G.pair P.retained) :=
      (Mole.leaf_incidence_realization_iff G S _).mp (placement_pair_in_realization G P hB hP)
    have hretInternal := (Mole.internal_leaf_pair_iff G S P.retained).mp hpairInternal
    have hr : old.1 ≠ P.retained := fun he => hnot (he.symm ▸ hretInternal)
    have hp : old.1 ≠ G.pair P.retained := fun he => hnot (he.symm ▸ hpairInternal)
    have hcast : forestNodeCast (unitTwist_splicedForest G P hB hCL hP D).symm l.toNode =
        (forestLeafCast (unitTwist_splicedForest G P hB hCL hP D).symm l).toNode := Subtype.ext rfl
    have hn := unitTwist_spliceLeaf_diagram G P hB hCL hP D l
    calc
      _ = twistNodeLabels G P κ (Mole.spliceLeafEquiv (twistedSpliceBoundary G P hB hCL hP D)
          (forestLeafCast (unitTwist_splicedForest G P hB hCL hP D).symm l)).1.toNode := by
        exact (congrArg (inheritCLLabels
          (isBlock_twistedAtoms G P hB)
          (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
          (twistNodeLabels G P κ)) hcast).trans (inheritCLLabels_leaf _ _ _ _ _)
      _ = twistNodeLabels G P κ (coreLeafEquiv G P old.1).toNode := congrArg
        (fun z => twistNodeLabels G P κ z.toNode) hn.symm
      _ = κ old.1.toNode := (twistNodeLabels_leaf G P κ old.1).trans (ite_eq_right (not_or.mpr ⟨hr,hp⟩))
      _ = _ := (inheritCLLabels_leaf _ _ _ _ l).symm

end WaveTurbulence.Twist
