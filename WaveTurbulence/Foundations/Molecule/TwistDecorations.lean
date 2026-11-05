/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistLowerLabels

/-! # Actual decoration preservation for the unit twist

TARGET twistexplain (d): the lower/retained exchange is a valid momentum
decoration. All source conservation and paired-leaf equations are proved.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The transported labels satisfy the lower branch's actual conservation equation. -/
theorem twistNodeLabels_lower_conservation {E : Type*} [AddCommGroup E]
    (κ : GNode G.tree → E) (hκ : IsDecoration G κ) :
    twistNodeLabels G P κ (coreBranchEquiv G P P.lower).toNode =
      twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child 0) -
      twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child 1) +
      twistNodeLabels G P κ ((coreBranchEquiv G P P.lower).child 2) := by
  rw [twistNodeLabels_lower,twistNodeLabels_lower_child,twistNodeLabels_lower_child,twistNodeLabels_lower_child]
  have hk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
  have h := hκ.1 P.lower
  have hc := congrArg κ P.child
  rcases hk with hk | hk
  · simp only [hk,freeSwap,Equiv.swap_apply_def] at hc ⊢
    norm_num at hc ⊢
    rw [h,← hc]
    abel
  · simp only [hk,freeSwap,Equiv.swap_apply_def] at hc ⊢
    norm_num at hc ⊢
    rw [h,← hc]
    abel

/-- Every actual source decoration is transported to an actual decoration of the twisted garden. -/
theorem twistNodeLabels_isDecoration {E : Type*} [AddCommGroup E]
    (κ : GNode G.tree → E) (hκ : IsDecoration G κ) :
    IsDecoration (unitTwistGarden G P) (twistNodeLabels G P κ) := by
  constructor
  · intro b
    obtain ⟨p,rfl⟩ := (coreBranchEquiv G P).surjective b
    by_cases hp : p = P.lower
    · subst p
      exact twistNodeLabels_lower_conservation G P κ hκ
    · have h0 := twistNodeLabels_other_child G P κ (hκ.2 P.retained) p hp 0
      have h1 := twistNodeLabels_other_child G P κ (hκ.2 P.retained) p hp 1
      have h2 := twistNodeLabels_other_child G P κ (hκ.2 P.retained) p hp 2
      exact (twistNodeLabels_branch G P κ p hp).trans ((hκ.1 p).trans
        (congrArg₂ (fun x y : E => x + y)
          (congrArg₂ (fun x y : E => x - y) h0.symm h1.symm) h2.symm))
  · exact twistNodeLabels_leaf_pairs G P κ hκ.2

end WaveTurbulence.Twist
