/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorations

/-! # Exact phase preservation under a unit twist

TARGET twistexplain and the m=1 mechanical check: every corresponding
branch has the same phase zeta*Omega. The lower Omega and zeta both flip.
The proof is symbolic for all dimensions and all vine lengths.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w d : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The lower resonance factor is negated by the actual label exchange. -/
theorem omegaNode_unitTwist_lower (κ : GNode G.tree → Mom d) :
    omegaNode (unitTwistGarden G P) (twistNodeLabels G P κ) (coreBranchEquiv G P P.lower) =
      -omegaNode G κ P.lower := by
  calc
    _ = resFactor
        (if (0 : Fin 3) = P.keep then κ P.lower.toNode else κ (P.lower.child (freeSwap P.keep 0)))
        (if (1 : Fin 3) = P.keep then κ P.lower.toNode else κ (P.lower.child (freeSwap P.keep 1)))
        (if (2 : Fin 3) = P.keep then κ P.lower.toNode else κ (P.lower.child (freeSwap P.keep 2)))
        (κ P.retained.toNode) := by
      unfold omegaNode
      congr 1
      · exact twistNodeLabels_lower_child G P κ 0
      · exact twistNodeLabels_lower_child G P κ 1
      · exact twistNodeLabels_lower_child G P κ 2
      · exact twistNodeLabels_lower G P κ
    _ = _ := by
      unfold omegaNode resFactor
      have hk : P.keep = 0 ∨ P.keep = 2 := by have hh := P.outer; omega
      have hc := congrArg κ P.child
      rcases hk with hk | hk
      · simp [hk,freeSwap,Equiv.swap_apply_def] at hc ⊢
        rw [hc]
        ring
      · simp [hk,freeSwap,Equiv.swap_apply_def] at hc ⊢
        rw [hc]
        ring

/-- Every other resonance factor is unchanged for actual paired node values. -/
theorem omegaNode_unitTwist_other (κ : GNode G.tree → Mom d)
    (hpair : κ P.retained.toNode = κ (G.pair P.retained).toNode)
    (b : GBranch G.tree) (hb : b ≠ P.lower) :
    omegaNode (unitTwistGarden G P) (twistNodeLabels G P κ) (coreBranchEquiv G P b) = omegaNode G κ b := by
  unfold omegaNode
  congr 1
  · exact twistNodeLabels_other_child G P κ hpair b hb 0
  · exact twistNodeLabels_other_child G P κ hpair b hb 1
  · exact twistNodeLabels_other_child G P κ hpair b hb 2
  · exact twistNodeLabels_branch G P κ b hb

/-- Every signed resonance phase is exactly preserved, including the one-rung vine. -/
theorem unitTwist_phase (κ : GNode G.tree → Mom d) (hκ : IsDecoration G κ) (b : GBranch G.tree) :
    (((unitTwistGarden G P).sign (coreBranchEquiv G P b).toNode : ℤ) : ℝ) *
      omegaNode (unitTwistGarden G P) (twistNodeLabels G P κ) (coreBranchEquiv G P b) =
    ((G.sign b.toNode : ℤ) : ℝ) * omegaNode G κ b := by
  by_cases hb : b = P.lower
  · subst b
    rw [coreBranchEquiv_sign,ite_eq_left rfl,omegaNode_unitTwist_lower]
    simp
  · rw [coreBranchEquiv_sign,ite_eq_right hb,omegaNode_unitTwist_other G P κ (hκ.2 P.retained) b hb]

end WaveTurbulence.Twist
