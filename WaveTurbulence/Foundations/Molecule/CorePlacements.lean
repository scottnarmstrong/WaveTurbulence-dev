/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LeafAncestorParent
public import WaveTurbulence.Foundations.Molecule.LowerTerminal

/-! # Producing actual unit-twist placements from core vines

TARGET twist: u23 is an outer child leaf, and its paired leaf u0 is
outside the lower subtree. Both facts are proved from the vine premises.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w)

/-- Concrete placement data for the subtree exchange, including actual paired leaves. -/
structure CorePlacement where
  lower : GBranch G.tree
  retained : GLeaf G.tree
  nonroot : lower.1.2 ≠ []
  paired_nonroot : (G.pair retained).1.2 ≠ []
  keep : Fin 3
  unmarked : G.mark retained = none
  child : retained.toNode = lower.child keep
  outer : keep ≠ 1
  paired_outside : ¬ lower.toNode.IsDesc (G.pair retained).toNode

/-- The two insertion slots have opposite root signs, derived from the paired outer leaf. -/
theorem CorePlacement.hole_signs (P : CorePlacement G) :
    nodeSign G.sig (commonOutsideLeaf G P.lower (G.pair P.retained) P.paired_outside).1 =
      -nodeSign G.sig (collapsedRoot G P.lower).1 := by
  have hp := G.pair_sign P.retained (Garden.pair_ne_of_unmarked P.unmarked)
  have hc : G.sign P.retained.toNode = G.sign P.lower.toNode := by
    rw [P.child]
    exact Mole.outer_child_sign G P.lower P.keep P.outer
  change nodeSign G.sig (G.pair P.retained).1 = -nodeSign G.sig P.lower.1
  change nodeSign G.sig (G.pair P.retained).1 = -nodeSign G.sig P.retained.1 at hp
  change nodeSign G.sig P.retained.1 = nodeSign G.sig P.lower.1 at hc
  rw [hp,hc]

end WaveTurbulence.Twist
