/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CutNodeEquiv
public import WaveTurbulence.Foundations.Molecule.LFTwist.PairClosure

/-! # Signed decoration values on the actual threshold-cut correspondence

The swapped lower/partner roles preserve signed node values under the
actual TWIST decoration bijection. The retained leaf is the only exception,
and its flat layer excludes it from every threshold cut.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The signed scalar value used by the exact complete-pairing criterion. -/
@[expose] def signedValue (κ : GNode G.tree → ℤ) (n : GNode G.tree) : ℤ := (G.sign n : ℤ) * κ n

/-- Every ordinary actual node keeps its sign under naive subtree transport. -/
theorem naiveNodeEquiv_sign_other (n : GNode G.tree) (hb : n ≠ P.lower.toNode)
    (hr : n ≠ P.retained.toNode) (hp : n ≠ (G.pair P.retained).toNode) :
    (unitTwistGarden G P).sign (naiveNodeEquiv G P n) = G.sign n := by
  obtain ⟨x,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases x with
  | inl b =>
    have hne : b ≠ P.lower := fun he => hb (congrArg GBranch.toNode he)
    exact (congrArg (unitTwistGarden G P).sign (naiveNodeEquiv_branch G P b)).trans
      ((coreBranchEquiv_sign G P b).trans (ite_eq_right hne))
  | inr l =>
    have hlr : l ≠ P.retained := fun he => hr (congrArg GLeaf.toNode he)
    have hlp : l ≠ G.pair P.retained := fun he => hp (congrArg GLeaf.toNode he)
    have hm : coreLeafMultiplier G P l = 1 := ite_eq_right (not_or.mpr ⟨hlr,hlp⟩)
    exact (congrArg (unitTwistGarden G P).sign (naiveNodeEquiv_leaf G P l)).trans
      ((leaf_sign_transport G P l).trans (by rw [hm,one_mul]; rfl))

/-- Every ordinary actual node keeps its scalar label under the actual twist decoration map. -/
theorem naiveNodeEquiv_label_other (κ : GNode G.tree → ℤ) (n : GNode G.tree)
    (hb : n ≠ P.lower.toNode) (hr : n ≠ P.retained.toNode) (hp : n ≠ (G.pair P.retained).toNode) :
    twistNodeLabels G P κ (naiveNodeEquiv G P n) = κ n := by
  exact (twistNodeLabels_naive G P κ n).trans (by
    simp only [switchedOldLabels,hb,hr,hp,or_self,ite_false])

/-- The cut-node correspondence preserves every signed scalar value except
at the retained leaf; the source paired-leaf equation handles the partner role. -/
theorem cutNodeEquiv_signedValue (κ : GNode G.tree → ℤ) (hκ : IsDecoration G κ)
    (n : GNode G.tree) (hr : n ≠ P.retained.toNode) :
    signedValue (unitTwistGarden G P) (twistNodeLabels G P κ) (cutNodeEquiv G P n) = signedValue G κ n := by
  by_cases hb : n = P.lower.toNode
  · subst n
    unfold signedValue
    rw [cutNodeEquiv_lower,twistNodeLabels_paired,leaf_sign_transport]
    simp only [coreLeafMultiplier,eq_self,or_true,ite_true,neg_one_mul,paired_sign,neg_neg]
  · by_cases hp : n = (G.pair P.retained).toNode
    · subst n
      unfold signedValue
      rw [cutNodeEquiv_paired,twistNodeLabels_lower,coreBranchEquiv_sign,ite_eq_left rfl,paired_sign,← hκ.2 P.retained]
    · unfold signedValue
      rw [cutNodeEquiv_other G P n hb hp,naiveNodeEquiv_sign_other G P n hb hr hp,
        naiveNodeEquiv_label_other G P κ n hb hr hp]

/-- The retained child is flat in the collapsed source layering and hence
never belongs to an integer threshold cut. -/
theorem retained_not_cutRoot (LG : LayeredGarden w) (R : CorePlacement LG.garden)
    (he : SameLowerLayer LG R) (p r : ℕ) : ¬ IsCutRoot LG p r R.retained.toNode := by
  intro hc
  have hp := parent_eq_of_child (retained_nonroot LG.garden R) R.child
  have hpar := parentLayer_nonroot LG p R.retained.toNode (retained_nonroot LG.garden R)
  rw [hp] at hpar
  have hret : LG.layer R.lower.toNode = LG.layer R.retained.toNode := he
  have hlow := hc.1
  have hhigh := hc.2
  omega

end WaveTurbulence.LFTwist
