/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPrime

/-! # The designated placement and selected branches of its source vine

TARGET twist: all selected branching nodes except the lower joint lie
outside its removed subtree; any internal leaf-pair witness identifies
the same designated u23. These facts tie scenario and splice consumers
to the exact input vine.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Fixed selected branch addresses retain their ancestor relation. -/
theorem fixed_branch_desc_iff {p q : GBranch G.tree}
    (hp : (coreBranchEquiv G P p).1 = p.1) (hq : (coreBranchEquiv G P q).1 = q.1) :
    (coreBranchEquiv G P p).toNode.IsDesc (coreBranchEquiv G P q).toNode ↔ p.toNode.IsDesc q.toNode := by
  change (coreBranchEquiv G P p).1.1 = (coreBranchEquiv G P q).1.1 ∧
    (coreBranchEquiv G P p).1.2 <+: (coreBranchEquiv G P q).1.2 ↔ p.1.1 = q.1.1 ∧ p.1.2 <+: q.1.2
  rw [hp,hq]

end WaveTurbulence.Twist
