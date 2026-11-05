/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.Molecule.TwistEpsilon
public import WaveTurbulence.Foundations.Molecule.TwistInheritedLabels
public import WaveTurbulence.Foundations.Molecule.TwistBondLabels
public import WaveTurbulence.Foundations.Molecule.TwistPhases
public import WaveTurbulence.Foundations.Molecule.TwistDecorationRoots
public import WaveTurbulence.Foundations.Molecule.TwistTypeISwitches
public import WaveTurbulence.Foundations.Molecule.TwistTypeIISwitches

/-! # M6 TWIST: the actual source involution and its cancellation

TARGET Definition twist and Remarks explaintwist/twistexplain
(L1423–L1458), including every vine-II length m ≥ 1 (F72).

`corePlacement_at_vine` derives the designated internal u23 from the
current connected source vine. `unitTwistGarden` performs the literal
ordered subtree exchange, and `unitTwistGarden_involutive` includes the
pairing and marks. The six source scenario switches, prime equivalence,
and actual directed molecular isomorphism are proved in the imported
modules. `unitTwist_canonicalSplice` and `unitTwist_inherited_labels`
compare the accepted source splicings, with no substitute splice API.

`unitTwistIntDecorationEquiv` is the literal integer-decoration bijection
with prescribed roots; bond vectors and each zeta*Omega are preserved.
The full epsilon coefficient is preserved and the branch-sign product
is negated, giving `unitTwist_epsilon_amplitude_cancel` for a common
amplitude. Original time domains and leaf weights need not coincide;
the later LFTWIST packet supplies their analytic comparison.

For source collections, `CoreFamily.twist` proves all second-site
conditions and transports the source family. `familyStep_involutive`
and `familyStep_commute` are consequences of the actual surgeries.
`SourceVineFamily.twists_count` counts literal Garden values: exactly
2^r for r core members, hence a power of two and at most 2^q. Its
separation premise is weaker than the source common-joint restriction.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- The two source unit-twist options are distinct literal gardens. -/
theorem unitTwistGarden_ne {w : ℕ} (G : Garden w) (P : CorePlacement G) :
    unitTwistGarden G P ≠ G :=
  gardens_ne_of_leaf_branch (unitTwist_leaf_at_lower P) P.lower.2

/-- The actual branching-node count is preserved, hence so is the common
order-dependent scalar factor in the source contribution. -/
theorem unitTwist_branch_count {w : ℕ} (G : Garden w) (P : CorePlacement G) :
    Fintype.card (GBranch (unitTwistGarden G P).tree) = Fintype.card (GBranch G.tree) :=
  (Fintype.card_congr (coreBranchEquiv G P)).symm

end WaveTurbulence.Twist
