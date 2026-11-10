/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistGroupTransport
public import WaveTurbulence.Foundations.Molecule.IsoBlockTransport

/-! # Current connected blocks are preserved by the actual unit twist -/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The exact current connected B2 block predicate is preserved. -/
theorem isBlock_twistedAtoms {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) :
    (unitTwistGarden G P).molecule.IsBlock (twistedAtoms G P S) (coreBranchEquiv G P a) (coreBranchEquiv G P b) :=
  iso_isBlock G (unitTwistGarden G P) (unitTwistDirectedIso G P) hB

end WaveTurbulence.Twist
