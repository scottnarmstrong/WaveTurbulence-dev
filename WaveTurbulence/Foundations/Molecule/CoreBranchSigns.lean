/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.UnitTwistGarden

/-! # Exact branching-sign flip under the actual unit twist

TARGET twistexplain (b): every branching sign is preserved except at u2.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Actual old branch decomposition through the common forest. -/
@[expose] noncomputable def coreBranchPiece : GBranch G.tree ≃
    InsertionBranchPiece (commonForest G P.lower) (lowerCrown G P.lower) :=
  (forestBranchCast (restore_commonForest G P.lower).symm).trans
    (insertionBranchEquiv (commonForest G P.lower) (collapsedRoot G P.lower) (lowerCrown G P.lower)).symm

/-- The local lower crown root is an actual branching node. -/
@[expose] def lowerLocalBranch : ↥(lowerCrown G P.lower).branching := ⟨[],by
  apply (Comb.subtree_branching_iff (Mole.spliceNodeSubtree_spec G P.lower.toNode) []).mpr
  simpa only [List.append_nil,GBranch.toNode] using P.lower.2⟩

/-- The actual lower branch is the root of the inserted branch piece. -/
theorem coreBranchPiece_lower : coreBranchPiece G P P.lower = .inr (lowerLocalBranch G P) := by
  apply (coreBranchPiece G P).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  change P.lower.1 = (P.lower.1.1,P.lower.1.2 ++ [])
  simp

/-- Evaluate actual branch exchange on a branch piece. -/
theorem coreBranchEquiv_piece (p : InsertionBranchPiece (commonForest G P.lower) (lowerCrown G P.lower)) :
    coreBranchEquiv G P ((coreBranchPiece G P).symm p) =
      insertionBranchMap (commonForest G P.lower) (pairedHole G P) (switchFree P.keep (lowerCrown G P.lower))
        ((Equiv.sumCongr (Equiv.refl _) (switchBranchEquiv P.keep (lowerCrown G P.lower))) p) := by
  change (insertionBranchEquiv _ _ _) ((Equiv.sumCongr _ _)
    ((insertionBranchEquiv _ _ _).symm ((forestBranchCast (restore_commonForest G P.lower).symm)
      ((forestBranchCast (restore_commonForest G P.lower).symm).symm ((insertionBranchEquiv _ _ _) p))))) = _
  simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  rfl

/-- The actual unit twist flips only the sign of the lower branching node. -/
theorem coreBranchEquiv_sign (b : GBranch G.tree) :
    (unitTwistGarden G P).sign (coreBranchEquiv G P b).toNode =
      if b = P.lower then -G.sign b.toNode else G.sign b.toNode := by
  classical
  obtain ⟨p,rfl⟩ := (coreBranchPiece G P).symm.surjective b
  change nodeSign G.sig (coreBranchEquiv G P ((coreBranchPiece G P).symm p)).1 = _
  rw [coreBranchEquiv_piece]
  cases p with
  | inl b =>
    have hne : (coreBranchPiece G P).symm (.inl b) ≠ P.lower := by
      intro he
      have hh := congrArg (coreBranchPiece G P) he
      rw [Equiv.apply_symm_apply,coreBranchPiece_lower] at hh
      cases hh
    rw [ite_eq_right hne]
    rfl
  | inr q =>
    have he : (coreBranchPiece G P).symm (.inr q) = P.lower ↔ q.1 = [] := by
      rw [Equiv.symm_apply_eq,coreBranchPiece_lower,Sum.inr.injEq]
      exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩
    simp only [he]
    change pathSign (G.sig (pairedHole G P).1.1)
        ((pairedHole G P).1.2 ++ switchPath P.keep q.1) =
      if q.1 = [] then -pathSign (G.sig P.lower.1.1) (P.lower.1.2 ++ q.1)
      else pathSign (G.sig P.lower.1.1) (P.lower.1.2 ++ q.1)
    simp only [pathSign_append]
    have hs : nodeSign G.sig (pairedHole G P).1 = -nodeSign G.sig P.lower.1 :=
      CorePlacement.hole_signs G P
    change pathSign (nodeSign G.sig (pairedHole G P).1) (switchPath P.keep q.1) = _
    rw [hs]
    exact switched_branch_sign P.outer (lowerCrown_retained_leaf G P) _ q.2

end WaveTurbulence.Twist
