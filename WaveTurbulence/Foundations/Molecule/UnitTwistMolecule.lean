/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDartDirections

/-! # Directed molecule isomorphism of the actual unit twist

TARGET twistexplain (a): exact half-edge multiplicities, mates, atom
endpoints, and orientations are preserved. The only label exchange is
between the actual lower PC bond and its retained LP bond.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The concrete unit twist is an isomorphism to the same directed molecule. -/
@[expose] noncomputable def unitTwistMoleculeIso :
    Mole.GardenMoleculeIso G (unitTwistGarden G P).molecule where
  branches :=
    { toFun b := ⟨coreBranchEquiv G P b,Finset.mem_univ _⟩
      invFun b := (coreBranchEquiv G P).symm b.1
      left_inv b := (coreBranchEquiv G P).symm_apply_apply b
      right_inv b := Subtype.ext ((coreBranchEquiv G P).apply_symm_apply b.1) }
  darts := twistDartEquiv G P
  atom_comm := twistDartEquiv_atom G P
  mate_comm := twistDartEquiv_mate G P
  out_comm := twistDartEquiv_out G P

end WaveTurbulence.Twist
