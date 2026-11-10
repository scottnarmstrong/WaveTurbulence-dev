/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDartDirections

/-! # Directed isomorphisms between actual garden molecules

The abstract target carrier avoids unfolding a concrete surgery during
finite-set/typeclass elaboration. The unit-twist instance is proved.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Actual half-edge isomorphism of two garden molecules. -/
structure GardenDirectedIso {w : ℕ} (G H : Garden w) where
  branches : GBranch G.tree ≃ GBranch H.tree
  darts : GardenDart G ≃ GardenDart H
  atom_comm : ∀ x, H.molecule.atom (darts x) = branches (G.molecule.atom x)
  mate_comm : ∀ x, H.molecule.mate (darts x) = darts (G.molecule.mate x)
  out_comm : ∀ x, H.molecule.out (darts x) = G.molecule.out x

/-- The concrete twist supplies every field of the abstract actual-garden isomorphism. -/
@[expose] noncomputable def unitTwistDirectedIso {w : ℕ} (G : Garden w) (P : CorePlacement G) :
    GardenDirectedIso G (unitTwistGarden G P) where
  branches := coreBranchEquiv G P
  darts := twistDartEquiv G P
  atom_comm := twistDartEquiv_atom G P
  mate_comm := twistDartEquiv_mate G P
  out_comm := twistDartEquiv_out G P

end WaveTurbulence.Twist
