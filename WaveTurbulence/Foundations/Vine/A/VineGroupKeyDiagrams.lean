/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.Vine.A.VineGroupCandidateMap
/-! Equality of the complete normalized candidate sets along an actual LF twist. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}
variable (Z : TwistGroupSite G) (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0)
include hsel

/-- Normalized reversal commutes with the actual LF dart map. -/
theorem coarseDartTwist_mate (x : CoarseDart G) :
    coarseDartMate Z.target (coarseDartTwist Z hsel x) =
      coarseDartTwist Z hsel (coarseDartMate G x) := Subtype.ext (Z.iso.mate_comm x.1)

/-- Every valid HV candidate has exactly the same normalized key after LF. -/
theorem hvGroupKey_twist (hS : SingleHVGroup G S) (t : {t // HVCandidate G S t}) :
    hvGroupKey (hS.map Z.iso) (hvCandidateEquiv Z.iso S t) = hvGroupKey hS t := by
  have hd : hvCandidateDart (hS.map Z.iso) (hvCandidateEquiv Z.iso S t) =
      coarseDartTwist Z hsel (hvCandidateDart hS t) := Subtype.ext rfl
  unfold hvGroupKey
  rw [hd, coarseDartTwist_mate Z hsel, coarseDartWord_twist Z hsel, coarseDartWord_twist Z hsel]
  change [_, _, coarseAtomWord Z.target (Z.iso.e t.1.1),
    coarseAtomWord Z.target (Z.iso.e t.1.2.1), _] = _
  rw [coarseAtomWord_twist Z hsel, coarseAtomWord_twist Z hsel]

/-- Complete normalized support words agree under the actual atom map. -/
theorem coarseSupportWord_twist (A : Finset (GBranch G.tree)) :
    coarseSupportWord Z.target (Z.iso.img A) = coarseSupportWord G A := by
  classical
  apply congrArg (fun s : Finset (List ℕ) => s.sort (· ≤ ·))
  change (A.image Z.iso.e).image (coarseAtomWord Z.target) = A.image (coarseAtomWord G)
  rw [Finset.image_image]
  apply Finset.image_congr
  intro v _
  exact coarseAtomWord_twist Z hsel v

/-- Every DV constituent/joint key agrees after LF, with the whole support retained. -/
theorem dvGroupKey_twist (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) :
    dvGroupKey Z.target (dvTripleEquiv Z.iso t) = dvGroupKey G t := by
  change [coarseSupportWord Z.target (Z.iso.img t.1), [coarseAtomWord Z.target (Z.iso.e t.2.1)],
    [coarseAtomWord Z.target (Z.iso.e t.2.2)]] = _
  rw [coarseSupportWord_twist Z hsel, coarseAtomWord_twist Z hsel, coarseAtomWord_twist Z hsel]
  rfl

end WaveTurbulence.VineA
