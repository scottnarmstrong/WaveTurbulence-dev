/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Realize2

/-! # ZP-SURJ: the numerical inequalities between the layers `L₂ ≤ L₃, L₄ ≤ p` of the start state -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.Mole

variable {w : ℕ} {ι : Type*} {p : ℕ}

/-- The layer of the core of a skeleton branch. -/
@[expose] noncomputable def cll (G : FamilyReconstruction w ι) (b : GBranch G.skeleton.tree) : ℕ :=
  layerAt G.layered (G.data.corePosition b)

theorem inducedPrelayer_eq_cll (G : FamilyReconstruction w ι) (b : GBranch G.skeleton.tree) :
    inducedPrelayer G.layered G.data G.plain G.decodes b = cll G b :=
  (layerAt_node G.layered (G.data.decodedCoreBranch G.plain G.decodes b).toNode).symm

theorem pcl_eq_cll (G : FamilyReconstruction w ι) {x : GNode G.skeleton.tree} (hn : x.1.2 ≠ []) :
    parentCoreLayer G.data G.plain (stateLayer G) x = cll G (x.parent hn) := by
  unfold parentCoreLayer
  rw [dif_neg hn]
  exact cl_eq_layerAt G _

theorem branchQ_snd (G : FamilyReconstruction w ι) (i : ι) : (zpBranchQ G i).2 = cll G (G.family.placement i).lower :=
  cl_eq_layerAt G _

theorem branchQ_fst (G : FamilyReconstruction w ι) (i : ι) :
    (zpBranchQ G i).1 = cll G ((G.family.placement i).lower.toNode.parent (G.family.placement i).nonroot) :=
  pcl_eq_cll G (G.family.placement i).nonroot

theorem numR_eq (G : FamilyReconstruction w ι) (i : ι) :
    numR G i = cll G ((G.skeleton.pair (G.family.placement i).retained).toNode.parent
      (G.family.placement i).paired_nonroot) :=
  pcl_eq_cll G (G.family.placement i).paired_nonroot

theorem cll_le_p (G : FamilyReconstruction w ι) {kind : Bool} (hcan : CanonicalObject p kind G.layered)
    (b : GBranch G.skeleton.tree) : cll G b ≤ p := by
  unfold cll
  have hc := hcan.criterion.1
  by_cases h : (G.data.corePosition b).2 ∈ (G.layered.garden.tree (G.data.corePosition b).1).nodes
  · rw [layerAt_of_mem _ h]; exact hc _
  · unfold layerAt; rw [dif_neg h]; exact Nat.zero_le _

section Start
variable (A : FamilyReconstruction w ι) (i : ι) {kind : Bool}
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

include hcan hel htc hcc

theorem L2_le_q2 : (zpBranchQ A i).2 ≤ (zpBranchQ A i).1 := by
  rw [branchQ_snd, branchQ_fst]
  have hn := (A.family.placement i).nonroot
  have h := inducedPrelayer_isBranchPrelayering A.layered A.data A.plain A.decodes
    ((A.family.placement i).lower.toNode.parent hn) (A.family.placement i).lower
    ((A.family.placement i).lower.toNode.1.2.getLast hn)
    (Mole.parent_child_eq_node (A.family.placement i).lower.toNode hn).symm
  rw [inducedPrelayer_eq_cll, inducedPrelayer_eq_cll] at h
  exact h

theorem L2_le_q1 : (zpBranchQ A i).2 ≤ numR A i := by
  rw [branchQ_snd, numR_eq]
  have h := sourceExpanded_parent_guard A.layered A.data A.plain A.decodes (A.family.placement i)
    (A.source i hcan hel htc hcc).core (A.source i hcan hel htc hcc).selected hel
  rw [inducedPrelayer_eq_cll, inducedPrelayer_eq_cll] at h
  exact h

theorem q1_le_p : numR A i ≤ p := by
  rw [numR_eq]; exact cll_le_p A hcan _

theorem q2_le_p : (zpBranchQ A i).1 ≤ p := by
  rw [branchQ_fst]; exact cll_le_p A hcan _

end Start

end WaveTurbulence.ZpSurj
