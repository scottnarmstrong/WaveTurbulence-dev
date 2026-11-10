/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.IsoGroupTransport
public import WaveTurbulence.Foundations.Molecule.VinePlacementGeometry

/-! # Transporting actual atomic groups and internal incidences under a twist -/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The same atomic group in the concrete twisted garden. -/
@[expose] noncomputable def twistedAtoms (S : Finset (GBranch G.tree)) :
    Finset (GBranch (unitTwistGarden G P).tree) := isoAtoms G (unitTwistGarden G P) (unitTwistDirectedIso G P) S

/-- Group membership is preserved by the actual branch bijection. -/
theorem mem_twistedAtoms (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    coreBranchEquiv G P v ∈ twistedAtoms G P S ↔ v ∈ S :=
  mem_isoAtoms G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v

/-- The actual dart bijection preserves internal-group membership. -/
theorem inGroup_twistedAtoms (S : Finset (GBranch G.tree)) (x : GardenDart G) :
    (unitTwistGarden G P).molecule.InGroup (twistedAtoms G P S) (twistDartEquiv G P x) ↔
      G.molecule.InGroup S x :=
  inGroup_isoAtoms G (unitTwistGarden G P) (unitTwistDirectedIso G P) S x

end WaveTurbulence.Twist
