/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Geo1
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls7Inj

/-! # ZP-SURJ: core-layer pins of an operation output -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Mole

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

theorem cl_eq_layerAt (G : FamilyReconstruction w ι) (c : GBranch G.skeleton.tree) :
    stateLayer G (G.data.coreBranch G.plain c).toNode = layerAt G.layered (G.data.corePosition c) := by
  conv_rhs => rw [← stateLayer_spec G]
  exact (layerAt_node (layeredReconstruction G.data G.plain (stateLayer G) (stateLayer_isLayering G))
    (G.data.coreBranch G.plain c).toNode).symm

section Op
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

theorem pin_cl (c : GBranch A.skeleton.tree) :
    stateLayer A (A.data.coreBranch A.plain c).toNode =
      stateLayer (opOut A i hcan hel htc hcc con)
        ((opOut A i hcan hel htc hcc con).data.coreBranch (opOut A i hcan hel htc hcc con).plain
          (chosenBranchEquiv A.skeleton (A.family.placement i) ε c)).toNode := by
  refine (cl_eq_layerAt A c).trans ((con.coreLayers c).trans ?_)
  exact (cl_eq_layerAt (opOut A i hcan hel htc hcc con) (chosenBranchEquiv A.skeleton (A.family.placement i) ε c)).symm

theorem pcl_pin {x : GNode A.skeleton.tree}
    {x' : GNode (opOut A i hcan hel htc hcc con).skeleton.tree}
    (hn : x.1.2 ≠ []) (hn' : x'.1.2 ≠ [])
    (hpar : x'.parent hn' = chosenBranchEquiv A.skeleton (A.family.placement i) ε (x.parent hn)) :
    parentCoreLayer (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) x' =
      parentCoreLayer A.data A.plain (stateLayer A) x := by
  unfold parentCoreLayer
  rw [dif_neg hn, dif_neg hn', hpar]
  exact (pin_cl A i hcan hel htc hcc con _).symm

theorem numbers_false (con : LFConstruction (A.source i hcan hel htc hcc) false) :
    zpBranchQ (opOut A i hcan hel htc hcc con) i = zpBranchQ A i ∧
      numR (opOut A i hcan hel htc hcc con) i = numR A i := by
  have hn : (A.family.placement i).lower.toNode.1.2 ≠ [] := (A.family.placement i).nonroot
  have hn2 : (A.skeleton.pair (A.family.placement i).retained).toNode.1.2 ≠ [] :=
    (A.family.placement i).paired_nonroot
  constructor
  · refine Prod.ext ?_ ?_
    · exact pcl_pin A i hcan hel htc hcc con (x := (A.family.placement i).lower.toNode) hn hn rfl
    · exact (pin_cl A i hcan hel htc hcc con (A.family.placement i).lower).symm
  · exact pcl_pin A i hcan hel htc hcc con (x := (A.skeleton.pair (A.family.placement i).retained).toNode)
      hn2 hn2 rfl

end Op

end WaveTurbulence.ZpSurj
