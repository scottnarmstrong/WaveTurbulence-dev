/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorationEquiv

/-! # Prescribed roots in the actual decoration bijection

TARGET twistexplain (d): the correspondence preserves every prescribed
root vector, hence restricts to the literal integer n-decorations.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The common actual address formula applies to the full node bijection. -/
theorem naiveNodeEquiv_address (n : GNode G.tree) :
    (naiveNodeEquiv G P n).1 = exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep n.1 := by
  obtain ⟨q,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    change (naiveNodeEquiv G P b.toNode).1 = _
    rw [naiveNodeEquiv_branch]
    exact coreBranchEquiv_address G P b
  | inr l =>
    change (naiveNodeEquiv G P l.toNode).1 = _
    rw [naiveNodeEquiv_leaf]
    exact coreLeafEquiv_address G P l

end WaveTurbulence.Twist
