/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Pat1

/-! # ZP-SURJ: the parent layers of the base gardens of the two skeleton choices -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {w : ℕ} {ι : Type*} {p : ℕ}

theorem pcl_eq_parAt (G : FamilyReconstruction w ι) (x : GNode G.skeleton.tree) (hn : x.1.2 ≠ []) :
    parentCoreLayer G.data G.plain (stateLayer G) x = parAt G.layered p (inflatedPosition G.skeleton G.data.tree x) := by
  have h := parAt_attached G.data G.plain (stateLayer G) (stateLayer_isLayering G) p x hn
  rw [stateLayer_spec G] at h
  unfold parentCoreLayer
  rw [dif_neg hn]
  exact h.symm

section Chosen
variable (A : FamilyReconstruction w ι) (i : ι) {ε : Bool}
  {D : ReconstructionData (chosenSkeleton A.skeleton (A.family.placement i) ε)} {L : LayeredGarden w}
  {hd : D.Decodes (chosenSkeleton_plain _ _ A.plain ε) L.garden}

theorem chosenState_lower_eq : ((chosenState A i ε D L hd).family.placement i).lower =
    chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower := by
  cases ε
  · rfl
  · exact A.family.nextPlacement_lower i i

theorem chosenState_pair_eq : pairOfLeaf (chosenState A i ε D L hd).skeleton (chosenState A i ε D L hd).plain
    ((chosenState A i ε D L hd).family.placement i).retained =
    chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
      (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) := by
  cases ε
  · exact (pairOfLeaf_firstLeaf A.skeleton A.plain _).symm
  · have hr : (A.family.nextPlacement i i).retained =
        coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained :=
      A.family.nextPlacement_retained i i
    have hq : chosenPairEquiv A.skeleton (A.family.placement i) A.plain true
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
        pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) (unitTwistGarden_plain _ _ A.plain)
          (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained) :=
      sourcePairEquiv_pairOfLeaf A.plain (unitTwistGarden_plain _ _ A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i)) (fun l => (unitTwistGarden_pair _ _ l).symm) _
    rw [hq]
    show pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) _ (A.family.nextPlacement i i).retained = _
    rw [hr]

theorem zpPairQ_chosen :
    zpPairQ (chosenState A i ε D L hd) i =
      (parAt L p (inflatedPosition (chosenSkeleton A.skeleton (A.family.placement i) ε) D.tree
        ((chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
          (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).firstLeaf
          (chosenSkeleton_plain _ _ A.plain ε)).toNode),
       parAt L p (inflatedPosition (chosenSkeleton A.skeleton (A.family.placement i) ε) D.tree
        ((chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
          (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).secondLeaf
          (chosenSkeleton_plain _ _ A.plain ε)).toNode)) := by
  obtain ⟨hn1, hn2⟩ := pair_leaves_nonroot (chosenState A i ε D L hd) i
  unfold zpPairQ pairQ
  rw [chosenState_pair_eq A i] at hn1 hn2 ⊢
  exact Prod.ext (pcl_eq_parAt (chosenState A i ε D L hd) _ hn1)
    (pcl_eq_parAt (chosenState A i ε D L hd) _ hn2)

theorem zpBranchQ_fst_chosen :
    (zpBranchQ (chosenState A i ε D L hd) i).1 =
      parAt L p (inflatedPosition (chosenSkeleton A.skeleton (A.family.placement i) ε) D.tree
        (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower).toNode) := by
  have hn := ((chosenState A i ε D L hd).family.placement i).nonroot
  have := pcl_eq_parAt (p := p) (chosenState A i ε D L hd) ((chosenState A i ε D L hd).family.placement i).lower.toNode hn
  show parentCoreLayer _ _ _ ((chosenState A i ε D L hd).family.placement i).lower.toNode = _
  rw [chosenState_lower_eq A i] at this ⊢
  exact this

theorem zpBranchQ_snd_chosen :
    (zpBranchQ (chosenState A i ε D L hd) i).2 =
      layerAt L (D.corePosition (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower)) := by
  rw [branchQ_snd, chosenState_lower_eq A i]
  exact rfl

end Chosen

section Base
variable {pstar : ι}
variable (A : FamilyReconstruction w ι)
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

/-- The state whose layered garden is the base garden of the choice `ε`. -/
@[expose] noncomputable def baseState (ε : Bool) : FamilyReconstruction w ι :=
  chosenState A pstar ε ((A.source pstar hcan hel htc hcc).baseData ε) ((A.source pstar hcan hel htc hcc).base ε)
    ((A.source pstar hcan hel htc hcc).base_decodes ε)

theorem base_pin (ε : Bool) (c : GBranch A.skeleton.tree) :
    layerAt A.layered (A.data.corePosition c) =
      layerAt ((A.source pstar hcan hel htc hcc).base ε)
        (((A.source pstar hcan hel htc hcc).baseData ε).corePosition (chosenBranchEquiv A.skeleton (A.family.placement pstar) ε c)) :=
  (k2_pins (A.source pstar hcan hel htc hcc) ε).1 c

theorem base_pair_parents (ε : Bool) :
    (parAt ((A.source pstar hcan hel htc hcc).base ε) p (cA (A.source pstar hcan hel htc hcc) ε),
      parAt ((A.source pstar hcan hel htc hcc).base ε) p (cB (A.source pstar hcan hel htc hcc) ε)) =
    zpPairQ (baseState A hcan hel htc hcc ε) pstar :=
  (zpPairQ_chosen (p := p) A pstar).symm

theorem base_branch_parents (ε : Bool) :
    (parAt ((A.source pstar hcan hel htc hcc).base ε) p (tA (A.source pstar hcan hel htc hcc) ε),
      layerAt ((A.source pstar hcan hel htc hcc).base ε) (tA (A.source pstar hcan hel htc hcc) ε)) =
    zpBranchQ (baseState A hcan hel htc hcc ε) pstar := by
  refine Prod.ext (zpBranchQ_fst_chosen (p := p) A pstar).symm ?_
  have hcore : ((A.source pstar hcan hel htc hcc).baseData ε).corePosition
      (chosenBranchEquiv A.skeleton (A.family.placement pstar) ε (A.family.placement pstar).lower) =
      tA (A.source pstar hcan hel htc hcc) ε := by
    unfold ReconstructionData.corePosition
    change addrExt (inflatedPosition _ _ ((A.source pstar hcan hel htc hcc).branches ε
      (A.source pstar hcan hel htc hcc).placement.lower).toNode) (((A.source pstar hcan hel htc hcc).baseData ε).tree
      ((A.source pstar hcan hel htc hcc).branches ε (A.source pstar hcan hel htc hcc).placement.lower)).lonePath = _
    rw [baseData_tree_lower (A.source pstar hcan hel htc hcc) ε]
    exact addrExt_nil _
  exact ((congrArg (layerAt _) hcore).symm.trans (zpBranchQ_snd_chosen A pstar).symm)

end Base

end WaveTurbulence.ZpSurj
