/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF1
import Mathlib.Tactic

/-!
# Transport across a `false`-choice operation: eligibility and coherence of another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem eligible_transport_false {s : LFSource p kind LG} (h : LFConstruction s false)
    {P : CorePlacement s.skeleton} {X : VineType} {B : Finset (GBranch s.skeleton.tree)}
    {a : GBranch s.skeleton.tree}
    (el : SourceLayerEligible LG s.data s.plain s.decodes P X B a) :
    SourceLayerEligible h.output h.data s.plain h.decodes P X B a := by
  have hP : inducedPrelayer h.output h.data s.plain h.decodes =
      inducedPrelayer LG s.data s.plain s.decodes := funext (inducedPrelayer_output_false h)
  unfold SourceLayerEligible at el ⊢
  rw [hP]
  exact el

variable {ι : Type*}

theorem transF_treeCoherent (A : FamilyReconstruction w ι) (i j : ι) (hij : i ≠ j)
    (c : CanonicalObject p kind A.layered)
    (el : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (tc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (cc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source i c el tc cc) false)
    (tcJ : CohOn A.layered ((A.data.tree (A.family.placement j).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement j).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement j).lower.toNode))) :
    CohOn con.output ((con.data.tree (A.family.placement j).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement j).lower.1)
      (inflatedPosition A.skeleton con.data.tree (A.family.placement j).lower.toNode)) := by
  have hb : (A.family.placement j).lower ≠ (A.source i c el tc cc).placement.lower :=
    fun he => hij ((A.family.lower_injective he).symm)
  have ht : con.data.tree (A.family.placement j).lower = A.data.tree (A.family.placement j).lower :=
    data_tree_other con _ hb
  rw [ht]
  refine cohOn_chain_transport _ _ _ _ (fun r hr => ?_) tcJ
  exact (con.ordinaryTreeLayers _ hb r hr).symm

theorem transF_coupleCoherent (A : FamilyReconstruction w ι) (i j : ι) (hij : i ≠ j)
    (c : CanonicalObject p kind A.layered)
    (el : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (tc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (cc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source i c el tc cc) false)
    (ccJ : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).secondLeaf A.plain).toNode))) :
    CohOn con.output ((con.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained)).linksAt
      (inflatedPosition A.skeleton con.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton con.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).secondLeaf A.plain).toNode)) := by
  set q := pairOfLeaf A.skeleton A.plain (A.family.placement j).retained with hq
  have hne : q ≠ (A.source i c el tc cc).exceptional :=
    fun he => CoreFamily.exceptional_ne A.family A.plain hij.symm he
  have hco : con.data.couple q = A.data.couple q := data_couple_other con q hne
  rw [hco]
  have hemb := reconstruction_coupleEmb A.data A.plain A.decodes q
  refine cohOn_couple_transport _ _ _ _ _ hemb.indep (fun r hr => ?_) (fun r hr => ?_) ccJ
  · have := con.ordinaryCoupleLayers q hne 0 r hr
    rw [LFSource.pairs_false (A.source i c el tc cc) q] at this
    exact this.symm
  · have := con.ordinaryCoupleLayers q hne 1 r hr
    rw [LFSource.pairs_false (A.source i c el tc cc) q] at this
    exact this.symm

end WaveTurbulence.Stage1
