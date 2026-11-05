/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistLabelAlgebra

/-! # The actual bijection of decorations under a unit twist

TARGET twistexplain (d). Both directions satisfy the literal source
IsDecoration predicate; the inverse is proved on paired labels.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The lower conservation equation is reflected by the switched labels. -/
theorem twistNodeLabels_lower_reflect {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E)
    (hnew : twistNodeLabels G P κ (coreBranchEquiv G P P.lower).toNode =
      twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child 0) -
      twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child 1) +
      twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child 2)) :
    κ P.lower.toNode = κ (P.lower.child 0) - κ (P.lower.child 1) + κ (P.lower.child 2) := by
  have h := (twistNodeLabels_lower G P κ).symm.trans (hnew.trans
    (congrArg₂ (fun x y : E => x + y)
      (congrArg₂ (fun x y : E => x - y) (twistNodeLabels_lower_child G P κ 0)
        (twistNodeLabels_lower_child G P κ 1)) (twistNodeLabels_lower_child G P κ 2)))
  have hk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
  have hc := congrArg κ P.child
  rcases hk with hk | hk
  · simp only [hk,freeSwap,Equiv.swap_apply_def] at hc h
    norm_num at hc h
    rw [hc] at h
    rw [h]
    abel
  · simp only [hk,freeSwap,Equiv.swap_apply_def] at hc h
    norm_num at hc h
    rw [hc] at h
    rw [h]
    abel

/-- On paired labels, the literal decoration equations hold iff they hold after the twist. -/
theorem isDecoration_iff_twistNodeLabels {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E)
    (hpair : ∀ l : GLeaf G.tree, κ l.toNode = κ (G.pair l).toNode) :
    IsDecoration G κ ↔ IsDecoration (unitTwistGarden G P) (twistNodeLabels G P κ) := by
  constructor
  · exact twistNodeLabels_isDecoration G P κ
  · intro hnew
    refine ⟨?_,hpair⟩
    intro b
    by_cases hb : b = P.lower
    · subst b
      exact twistNodeLabels_lower_reflect G P κ (hnew.1 (coreBranchEquiv G P P.lower))
    · have h0 := twistNodeLabels_other_child G P κ (hpair P.retained) b hb 0
      have h1 := twistNodeLabels_other_child G P κ (hpair P.retained) b hb 1
      have h2 := twistNodeLabels_other_child G P κ (hpair P.retained) b hb 2
      exact (twistNodeLabels_branch G P κ b hb).symm.trans
        ((hnew.1 (coreBranchEquiv G P b)).trans
          (congrArg₂ (fun x y : E => x + y) (congrArg₂ (fun x y : E => x - y) h0 h1) h2))

/-- The inverse concrete label recipe produces an actual old-garden decoration. -/
theorem untwistNodeLabels_isDecoration {E : Type*} [AddCommGroup E]
    (η : GNode (unitTwistGarden G P).tree → E) (hη : IsDecoration (unitTwistGarden G P) η) :
    IsDecoration G (untwistNodeLabels G P η) := by
  apply (isDecoration_iff_twistNodeLabels G P _ (untwistNodeLabels_paired G P η hη.2)).mpr
  rw [twist_untwistNodeLabels G P η hη.2]
  exact hη

/-- The unit twist bijects actual decorations, with the exact source lower/retained exchange. -/
@[expose] noncomputable def unitTwistDecorationEquiv (E : Type*) [AddCommGroup E] :
    {κ : GNode G.tree → E // IsDecoration G κ} ≃
      {η : GNode (unitTwistGarden G P).tree → E // IsDecoration (unitTwistGarden G P) η} where
  toFun κ := ⟨twistNodeLabels G P κ.1,twistNodeLabels_isDecoration G P κ.1 κ.2⟩
  invFun η := ⟨untwistNodeLabels G P η.1,untwistNodeLabels_isDecoration G P η.1 η.2⟩
  left_inv κ := Subtype.ext (untwist_twistNodeLabels G P κ.1 (κ.2.2 P.retained))
  right_inv η := Subtype.ext (twist_untwistNodeLabels G P η.1 η.2.2)

end WaveTurbulence.Twist
