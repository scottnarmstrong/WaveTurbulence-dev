/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Realize

/-! # ZP-SURJ: states of `Zp(A)` from exceptional data, and classification of the states -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι}
variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

/-- The state of `Zp(A)` reached by the operation with a given construction. -/
@[expose] noncomputable def opState {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    ST w ι pstar J :=
  ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar ε⟩

theorem reach_opState {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    ReachSp p kind pstar J [pstar] A sp0 (opState A sp0 hcan hel htc hcc con).1 (opState A sp0 hcan hel htc hcc con).2 :=
  ReachSp.apply (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)
    (ReachSp.nil _ _)

/-- **Realization**: every exceptional datum with the source count is the native datum of a state of `Zp(A)`. -/
theorem state_of_datum {ε : Bool} {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}
    (hD : ExcDatum (A.source pstar hcan hel htc hcc) ε Q X LQ LX)
    (hc : rawTreeLayerCount A.layered A.data A.plain p (A.family.placement pstar).lower +
        rawCoupleLayerCount A.layered A.data A.plain p
          (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) =
        topBranchCount LX p + topBranchCount LQ p) :
    ∃ con : LFConstruction (A.source pstar hcan hel htc hcc) ε,
      con.newCouple = Q ∧ con.newTree = X ∧ conLQ con = LQ ∧ conLX con = LX :=
  ⟨construction' hD hc, construction'_newCouple hD hc, construction'_newTree hD hc,
    conLQ_construction' hD hc, conLX_construction' hD hc⟩

theorem st_ext [DecidableEq ι] [Fintype ι] {G G' : ST w ι pstar J}
    (h : ReachSp p kind pstar J [pstar] A sp0 G.1 G.2) (h' : ReachSp p kind pstar J [pstar] A sp0 G'.1 G'.2)
    (e : G.1 = G'.1) : G = G' := by
  obtain ⟨X, s1⟩ := G
  obtain ⟨X', s2⟩ := G'
  change X = X' at e
  subst e
  have := ReachSp.unique (List.nodup_singleton pstar) (List.nodup_singleton pstar) h h'
  subst this
  rfl

/-- **Classification**: every state of `Zp(A)` is the output of an operation (the skip is the identity operation). -/
theorem classify [DecidableEq ι] (hA : IsPrimeGarden A.skeleton) {G : FamilyReconstruction w ι}
    (hG : FamilyBatch p kind [pstar] A G) :
    ∃ (ε : Bool) (con : LFConstruction (A.source pstar hcan hel htc hcc) ε),
      G = opOut A pstar hcan hel htc hcc con := by
  cases hG with
  | skip _ h1 =>
    cases h1
    obtain ⟨con, hcon⟩ := (A.source pstar hcan hel htc hcc).identity_construction
    refine ⟨false, con, ?_⟩
    exact eq_of_prime_layered hA (List.nodup_singleton pstar) (List.nodup_singleton pstar)
      (FamilyBatch.skip pstar (FamilyBatch.nil A))
      (FamilyBatch.apply (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)
        (FamilyBatch.nil _)) hcon.symm
  | apply op h1 =>
    cases h1
    obtain ⟨hcan', hel', htc', hcc', ε, con⟩ := op
    exact ⟨ε, con, rfl⟩

end WaveTurbulence.ZpSurj
