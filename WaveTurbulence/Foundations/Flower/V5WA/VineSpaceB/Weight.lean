/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.BondSplit
public import WaveTurbulence.Foundations.VineEst.VineSpaceB.BondStatements
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls6Zp
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw9Native

/-! # V5-SPACE-EXT: the bond weight of a state, and its transport along family operations

`layX X`: the core layering of the skeleton of a state; `bW ψ κ X U`: the bond weight of the block `U` of `X`.
A TRUE operation transports the core layers along the branch bijection, a FALSE one keeps them
(`LFConstruction.coreLayers`, through `coreLayer_eq`). Combined with the molecule isomorphism (`VineSpaceB.Bond`)
this gives the four transports used by the weighted recursion: rigid (operation below the block), same chart,
twist at the lower joint of the block (S side), twist above the block (T side). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B VineSpaceK Links

variable {w d : ℕ} {ι : Type*}

/-- The core (skeleton) layering of a state. -/
def layX (X : FamilyReconstruction w ι) (v : GBranch X.skeleton.tree) : ℕ :=
  stateLayer X (X.data.coreBranch X.plain v).toNode

theorem memberCoreLayer_eq (z : ClassMember w ι) (v : GBranch z.1.skeleton.tree) :
    memberCoreLayer z v = layX z.1 v := by
  unfold memberCoreLayer layX
  rw [← stateLayer_spec z.1]
  exact layerAt_node (layeredReconstruction z.1.data z.1.plain (stateLayer z.1) (stateLayer_isLayering z.1))
    (z.1.data.coreBranch z.1.plain v).toNode

section Op
variable {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
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

/-- A TRUE operation transports the core layers. -/
theorem layX_true (con : LFConstruction (A.source i hcan hel htc hcc) true) (v : GBranch A.skeleton.tree) :
    layX (opOut A i hcan hel htc hcc con) (coreBranchEquiv A.skeleton (A.family.placement i) v) = layX A v :=
  coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) v

/-- A FALSE operation keeps the core layers. -/
theorem layX_false (con : LFConstruction (A.source i hcan hel htc hcc) false) (v : GBranch A.skeleton.tree) :
    layX (opOut A i hcan hel htc hcc con) v = layX A v :=
  coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) v

end Op

end WaveTurbulence.VineSpaceB
