/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Geo3

/-! # ZP-SURJ: the parent-layer numbers of a TRUE operation output are those of the start, swapped -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Mole

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}
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

theorem numbers_true (con : LFConstruction (A.source i hcan hel htc hcc) true) :
    (zpBranchQ (opOut A i hcan hel htc hcc con) i).1 = numR A i ∧
      (zpBranchQ (opOut A i hcan hel htc hcc con) i).2 = (zpBranchQ A i).2 ∧
      numR (opOut A i hcan hel htc hcc con) i = (zpBranchQ A i).1 := by
  have hl : (A.family.nextPlacement i i).lower =
      coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower :=
    A.family.nextPlacement_lower i i
  have hr : (A.family.nextPlacement i i).retained =
      coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained :=
    A.family.nextPlacement_retained i i
  have hn : (A.family.placement i).lower.toNode.1.2 ≠ [] := (A.family.placement i).nonroot
  have hn2 : (A.skeleton.pair (A.family.placement i).retained).toNode.1.2 ≠ [] :=
    (A.family.placement i).paired_nonroot
  have hnl : (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).toNode.1.2 ≠ [] :=
    (coreBranchEquiv_nonroot A.skeleton (A.family.placement i) _).mpr hn
  have hnp : ((unitTwistGarden A.skeleton (A.family.placement i)).pair
      (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained)).toNode.1.2 ≠ [] := by
    rw [unitTwistGarden_pair]
    have h1 := coreLeafEquiv_paired_val A.skeleton (A.family.placement i)
    intro h
    apply hn
    have := congrArg Prod.snd h1
    change _ = (A.family.placement i).lower.1.2 at this
    exact this.symm.trans h
  refine ⟨?_, ?_, ?_⟩
  · show parentCoreLayer _ _ _ (A.family.nextPlacement i i).lower.toNode = _
    rw [hl]
    exact pcl_pin A i hcan hel htc hcc con (x := (A.skeleton.pair (A.family.placement i).retained).toNode)
      hn2 hnl (twist_parent_lower A.skeleton (A.family.placement i) hnl)
  · show stateLayer (opOut A i hcan hel htc hcc con) ((opOut A i hcan hel htc hcc con).data.coreBranch
      (opOut A i hcan hel htc hcc con).plain (A.family.nextPlacement i i).lower).toNode = _
    rw [hl]
    exact (pin_cl A i hcan hel htc hcc con (A.family.placement i).lower).symm
  · show parentCoreLayer _ _ _ ((unitTwistGarden A.skeleton (A.family.placement i)).pair
      (A.family.nextPlacement i i).retained).toNode = _
    rw [hr]
    exact pcl_pin A i hcan hel htc hcc con (x := (A.family.placement i).lower.toNode) hn hnp
      (twist_parent_paired A.skeleton (A.family.placement i) hnp)

end WaveTurbulence.ZpSurj
