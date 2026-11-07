/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceCorrespondence
/-! The actual molecular correspondence agrees with the full branching
and leaf correspondences on PC and LP darts. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- The full leaf correspondence preserves exactly the LP typing predicate. -/
theorem spliceFoldLeafEquiv_lp_profile (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf (spliceFold G l).G.tree) :
    ((spliceFold G l).G.mark q = none ∧ q.1.2 ≠ [] ∧ ((spliceFold G l).G.pair q).1.2 ≠ []) ↔
      ((spliceFold G m).G.mark (spliceFoldLeafEquiv l m hc q) = none ∧
        (spliceFoldLeafEquiv l m hc q).1.2 ≠ [] ∧
        ((spliceFold G m).G.pair (spliceFoldLeafEquiv l m hc q)).1.2 ≠ []) := by
  rw [(spliceFoldLeafTrace l).lp_profile, (spliceFoldLeafTrace m).lp_profile, spliceFoldLeafEquiv_comm]

/-- The induced actual LP-leaf equivalence. -/
noncomputable def spliceFoldLPLeafEquiv (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) :
    GardenLPLeaf (spliceFold G l).G ≃ GardenLPLeaf (spliceFold G m).G :=
  (spliceFoldLeafEquiv l m hc).subtypeEquiv (spliceFoldLeafEquiv_lp_profile l m hc)

/-- The induced actual nonroot-branch equivalence. -/
noncomputable def spliceFoldPCEquiv (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) :
    {c : GBranch (spliceFold G l).G.tree // c.1.2 ≠ []} ≃
      {c : GBranch (spliceFold G m).G.tree // c.1.2 ≠ []} :=
  (spliceFoldMolIso l m hc).e.subtypeEquiv
    (fun c => (not_congr (spliceFoldMolIso_branch_root l m hc c)).symm)

/-- Actual PC darts follow the actual branch equivalence, retaining their side. -/
theorem spliceFoldMolIso_pc (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls)
    (c : {c : GBranch (spliceFold G l).G.tree // c.1.2 ≠ []}) (side : Bool) :
    (spliceFoldMolIso l m hc).d (.inl (c, side)) = .inl (spliceFoldPCEquiv l m hc c, side) := by
  apply (spliceFold G m).M.od_inj
  rw [(spliceFoldMolIso_names l m hc).2, (spliceFoldDartTrace l).pc, (spliceFoldDartTrace m).pc]
  apply congrArg (fun c => Sum.inl (c, side))
  apply Subtype.ext
  exact ((spliceFoldMolIso_names l m hc).1 c.1).symm

/-- Actual LP darts follow the actual full leaf equivalence. -/
theorem spliceFoldMolIso_lp (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GardenLPLeaf (spliceFold G l).G) :
    (spliceFoldMolIso l m hc).d (.inr q) = .inr (spliceFoldLPLeafEquiv l m hc q) := by
  apply (spliceFold G m).M.od_inj
  rw [(spliceFoldMolIso_names l m hc).2, (spliceFoldDartTrace l).lp, (spliceFoldDartTrace m).lp]
  apply congrArg Sum.inr
  apply Subtype.ext
  exact (spliceFoldLeafEquiv_comm l m hc q.1).symm

end WaveTurbulence.VineA
