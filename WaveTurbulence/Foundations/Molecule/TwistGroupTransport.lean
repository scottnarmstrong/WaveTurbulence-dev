/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.IsoGroupTransport
public import WaveTurbulence.Foundations.Molecule.TwistTypeISwitches

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

/-- Membership in any internally oriented incidence set is preserved. -/
theorem internal_filter_mem (S : Finset (GBranch G.tree)) (v : GBranch G.tree)
    (p : Bool → Prop) [DecidablePred p] (x : GardenDart G) :
    twistDartEquiv G P x ∈ ((unitTwistGarden G P).molecule.dartsAt (coreBranchEquiv G P v)).filter
        (fun y => (unitTwistGarden G P).molecule.InGroup (twistedAtoms G P S) y ∧ p ((unitTwistGarden G P).molecule.out y)) ↔
      x ∈ (G.molecule.dartsAt v).filter (fun y => G.molecule.InGroup S y ∧ p (G.molecule.out y)) :=
  iso_internal_filter_mem G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v p x

/-- All internal oriented incidence counts are unchanged. -/
theorem internal_filter_card (S : Finset (GBranch G.tree)) (v : GBranch G.tree)
    (p : Bool → Prop) [DecidablePred p] :
    (((unitTwistGarden G P).molecule.dartsAt (coreBranchEquiv G P v)).filter
      (fun y => (unitTwistGarden G P).molecule.InGroup (twistedAtoms G P S) y ∧ p ((unitTwistGarden G P).molecule.out y))).card =
    ((G.molecule.dartsAt v).filter (fun y => G.molecule.InGroup S y ∧ p (G.molecule.out y))).card :=
  iso_internal_filter_card G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v p

/-- Internal total degrees are unchanged. -/
theorem degIn_twistedAtoms (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    (unitTwistGarden G P).molecule.degIn (twistedAtoms G P S) (coreBranchEquiv G P v) = G.molecule.degIn S v :=
  iso_degIn G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v

/-- Internal out-degrees are unchanged. -/
theorem outIn_twistedAtoms (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    (unitTwistGarden G P).molecule.outIn (twistedAtoms G P S) (coreBranchEquiv G P v) = G.molecule.outIn S v :=
  iso_outIn G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v

/-- Internal in-degrees are unchanged. -/
theorem inIn_twistedAtoms (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    (unitTwistGarden G P).molecule.inIn (twistedAtoms G P S) (coreBranchEquiv G P v) = G.molecule.inIn S v :=
  iso_inIn G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v

end WaveTurbulence.Twist
