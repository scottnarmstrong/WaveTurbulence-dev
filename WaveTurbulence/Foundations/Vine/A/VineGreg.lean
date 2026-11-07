/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineRegularIndex
import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue1
/-! Both exceptional rows are coherent, so actual LF operations preserve greg. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open TTree Reg Reg.Skeleton LFTwist Links RegRed RedSplice Stage1
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

/-- Every actual tree row keeps its incoherency, including the replaced coherent row. -/
theorem lf_tree_index (C : LFConstruction s ε) (b : GBranch s.skeleton.tree) :
    C.output.incoherency ((C.data.tree (s.branches ε b)).linksAt
      (nodeSign (s.chosen ε).sig (s.branches ε b).1)
      (inflatedPosition (s.chosen ε) C.data.tree (s.branches ε b).toNode)) =
    LG.incoherency ((s.data.tree b).linksAt (nodeSign s.skeleton.sig b.1)
      (inflatedPosition s.skeleton s.data.tree b.toNode)) := by
  by_cases hb : b = s.placement.lower
  · subst b
    exact (incoherency_eq_zero_of_cohOn _ _ (treeCoherent_output_gen C)).trans
      (incoherency_eq_zero_of_cohOn _ _ s.treeCoherent).symm
  · exact lf_tree_index_other C b hb

/-- Every actual couple row keeps its incoherency, including the replaced coherent row. -/
theorem lf_couple_index (C : LFConstruction s ε) (q : SourcePair s.skeleton) :
    C.output.incoherency ((C.data.couple (s.pairs ε q)).linksAt
      (inflatedPosition (s.chosen ε) C.data.tree ((s.pairs ε q).firstLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) C.data.tree ((s.pairs ε q).secondLeaf (s.chosen_plain ε)).toNode)) =
    LG.incoherency ((s.data.couple q).linksAt
      (inflatedPosition s.skeleton s.data.tree (q.firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton s.data.tree (q.secondLeaf s.plain).toNode)) := by
  by_cases hq : q = s.exceptional
  · subst q
    exact (incoherency_eq_zero_of_cohOn _ _ (coupleCoherent_output_gen C)).trans
      (incoherency_eq_zero_of_cohOn _ _ s.coupleCoherent).symm
  · exact lf_couple_index_other C q hq

/-- The actual regular incoherency contribution is unchanged by either LF choice. -/
theorem lf_gregOf (C : LFConstruction s ε) :
    gregOf C.data (s.chosen_plain ε) C.output = gregOf s.data s.plain LG := by
  classical
  unfold gregOf
  congr 1
  · rw [← (s.pairs ε).sum_comp]
    exact Finset.sum_congr rfl (fun q _ => lf_couple_index C q)
  · rw [← (s.branches ε).sum_comp]
    exact Finset.sum_congr rfl (fun b _ => lf_tree_index C b)

/-- Actual family operations preserve the actual regular contribution. -/
theorem operation_gregOf {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    gregOf op.output.data op.output.plain op.output.layered = gregOf A.data A.plain A.layered :=
  lf_gregOf op.construction

/-- Actual composed LF batches preserve the actual regular contribution. -/
theorem BatchIso.gregOf {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F) :
    RedSplice.gregOf B.data B.plain B.layered = RedSplice.gregOf A.data A.plain A.layered := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact ih
  | apply op _ ih => exact ih.trans (operation_gregOf op)

end WaveTurbulence.VineA
