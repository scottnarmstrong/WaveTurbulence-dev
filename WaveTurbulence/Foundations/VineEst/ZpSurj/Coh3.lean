/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Coh2

/-! # ZP-SURJ: native coherence of the exceptional objects of a state -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w : ℕ} {ι : Type*} {p : ℕ}

theorem pair_leaves_nonroot (G : FamilyReconstruction w ι) (i : ι) :
    ((pairOfLeaf G.skeleton G.plain (G.family.placement i).retained).firstLeaf G.plain).toNode.1.2 ≠ [] ∧
    ((pairOfLeaf G.skeleton G.plain (G.family.placement i).retained).secondLeaf G.plain).toNode.1.2 ≠ [] := by
  have hr : (G.family.placement i).retained.toNode.1.2 ≠ [] := by
    rw [(G.family.placement i).child]; simp [GBranch.child]
  have hp := (G.family.placement i).paired_nonroot
  by_cases hs : nodeSign G.skeleton.sig (G.family.placement i).retained.1 = 1
  · obtain ⟨h1, h2⟩ := pairOfLeaf_sides_pos G.skeleton G.plain _ hs
    rw [h1, h2]; exact ⟨hr, hp⟩
  · obtain ⟨h1, h2⟩ := pairOfLeaf_sides_neg G.skeleton G.plain _ hs
    rw [h1, h2]; exact ⟨hp, hr⟩

/-- **Native coherence of a state** from canonicity and the two coherence conditions on the exceptional rows. -/
theorem nativeCoh_of_cohOn (G : FamilyReconstruction w ι) (i : ι) (hcan : IsCanonGC (p + 1) G.layered)
    (hC : CohOn G.layered ((G.data.couple (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained)).linksAt
      (coupleRoot G.data G.plain (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained) 0)
      (coupleRoot G.data G.plain (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained) 1)))
    (hT : CohOn G.layered ((G.data.tree (G.family.placement i).lower).linksAt
      (nodeSign G.skeleton.sig (G.family.placement i).lower.1)
      (inflatedPosition G.skeleton G.data.tree (G.family.placement i).lower.toNode))) :
    IsCoherentCoupleAt p (zpPairQ G i).1 (zpPairQ G i).2 (zpData G i).1 (sigStar G i).2.1 ∧
      IsCoherentTreeAt p (zpBranchQ G i).1 (zpBranchQ G i).2 (zpData G i).2.1 (sigStar G i).2.2 := by
  have hspec := stateLayer_spec G
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction G.data G.plain (stateLayer G) (stateLayer_isLayering G)) := by
    rw [hspec]; exact hcan
  obtain ⟨hn1, hn2⟩ := pair_leaves_nonroot G i
  refine ⟨couple_coherent_of_canonical G.data G.plain (stateLayer G) (stateLayer_isLayering G) p hcan' _ hn1 hn2 ?_,
    tree_coherent_of_canonical G.data G.plain (stateLayer G) (stateLayer_isLayering G) p hcan' _
      (G.family.placement i).nonroot ?_⟩
  · refine coupleCnt_zero_of_cohOn G.data G.plain _ _ ?_
    rw [hspec]; exact hC
  · refine treeCnt_zero_of_cohOn G.data _ _ ?_
    rw [hspec]; exact hT

section Op
variable {kind : Bool}
variable (A : FamilyReconstruction w ι) (i : ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
    (A.family.atoms i) (A.family.upper i))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))
  {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε)

/-- The native exceptional objects of an operation output are coherent at their parent layers. -/
theorem nativeCoh_op :
    IsCoherentCoupleAt p (zpPairQ (opOut A i hcan hel htc hcc con) i).1 (zpPairQ (opOut A i hcan hel htc hcc con) i).2
      (zpData (opOut A i hcan hel htc hcc con) i).1 (sigStar (opOut A i hcan hel htc hcc con) i).2.1 ∧
    IsCoherentTreeAt p (zpBranchQ (opOut A i hcan hel htc hcc con) i).1 (zpBranchQ (opOut A i hcan hel htc hcc con) i).2
      (zpData (opOut A i hcan hel htc hcc con) i).2.1 (sigStar (opOut A i hcan hel htc hcc con) i).2.2 := by
  have hD := con_excDatum con
  refine nativeCoh_of_cohOn (opOut A i hcan hel htc hcc con) i
    (canonGC_of_canonicalObject (con.canonical)) ?_ ?_
  · rw [op_pair_eq A i hcan hel htc hcc con]
    have hFD : con.data.couple (chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)) = con.newCouple :=
      Function.update_self _ _ _
    exact cohOn_of_native_pattern con.data ((A.source i hcan hel htc hcc).chosen_plain ε) con.outLayer
      con.out_isLayering _ (pa := parAt ((A.source i hcan hel htc hcc).base ε) p (cA (A.source i hcan hel htc hcc) ε))
      (pb := parAt ((A.source i hcan hel htc hcc).base ε) p (cB (A.source i hcan hel htc hcc) ε))
      (by rw [hFD]; exact hD.patQ)
  · rw [op_lower_eq A i hcan hel htc hcc con]
    have hFD : con.data.tree (chosenBranchEquiv A.skeleton (A.family.placement i) ε
        (A.family.placement i).lower) = con.newTree := Function.update_self _ _ _
    exact cohOn_tree_of_native_pattern con.data ((A.source i hcan hel htc hcc).chosen_plain ε) con.outLayer
      con.out_isLayering _ (pa := parAt ((A.source i hcan hel htc hcc).base ε) p (tA (A.source i hcan hel htc hcc) ε))
      (by rw [hFD]; exact hD.patX)

end Op

end WaveTurbulence.ZpSurj
