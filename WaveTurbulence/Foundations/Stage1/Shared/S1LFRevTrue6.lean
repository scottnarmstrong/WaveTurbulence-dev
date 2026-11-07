/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue5
import Mathlib.Tactic

/-!
# T1 for choice `true`: the reverse operation at the output returns exactly the original state
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {LG : LayeredGarden w}

theorem lfSource_ext {s1 s2 : LFSource p kind LG} (e1 : s1.skeleton = s2.skeleton)
    (e2 : HEq s1.data s2.data) (e3 : HEq s1.placement s2.placement) (e4 : HEq s1.support s2.support)
    (e5 : HEq s1.upper s2.upper) (e6 : s1.vineType = s2.vineType) : s1 = s2 := by
  obtain ⟨sk1, pl1, d1, dec1, plc1, can1, vt1, sup1, up1, core1, sel1, el1, tc1, cc1⟩ := s1
  obtain ⟨sk2, pl2, d2, dec2, plc2, can2, vt2, sup2, up2, core2, sel2, el2, tc2, cc2⟩ := s2
  simp only at e1 e2 e3 e4 e5 e6
  subst e1
  have := eq_of_heq e2
  subst this
  have := eq_of_heq e3
  subst this
  have := eq_of_heq e4
  subst this
  have := eq_of_heq e5
  subst this
  subst e6
  rfl

theorem lfConstruction_transport {s1 s2 : LFSource p kind LG} (e : s1 = s2) {ε : Bool}
    (c : LFConstruction s1 ε) :
    ∃ c' : LFConstruction s2 ε, c'.output = c.output ∧ HEq c'.data c.data := by
  subst e
  exact ⟨c, rfl, HEq.rfl⟩


theorem familyState_heq_family {st1 st2 : FamilyState w ι} (e : st1 = st2) : HEq st1.2 st2.2 := by
  subst e
  exact HEq.rfl

/-- **Reverse of an LF operation with skeleton choice `true`** (GAP.congEquiv (b)): at the output there is an LF
operation returning exactly the original state. -/
theorem exists_reverse_op_true (A : FamilyReconstruction w ι) (i : ι)
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
    (con : LFConstruction (A.source i c el tc cc) true) :
    ∃ op' : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨c, el, tc, cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) i,
      op'.output = A := by
  let O := FamilyOperation.output (⟨c, el, tc, cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)
  have hPl : O.family.placement i = reversePlacement A.skeleton (A.family.placement i) :=
    A.family.nextPlacement_self i
  have el' : SourceLayerEligible O.layered O.data O.plain O.decodes (O.family.placement i)
      (O.family.kind i) (O.family.atoms i) (O.family.upper i) := by
    rw [hPl]
    exact eligible_output_true con
  have tc' : CohOn O.layered ((O.data.tree (O.family.placement i).lower).linksAt
      (nodeSign O.skeleton.sig (O.family.placement i).lower.1)
      (inflatedPosition O.skeleton O.data.tree (O.family.placement i).lower.toNode)) := by
    rw [hPl]
    exact treeCoherent_output_true con
  have cc' : CohOn O.layered ((O.data.couple (pairOfLeaf O.skeleton O.plain (O.family.placement i).retained)).linksAt
      (inflatedPosition O.skeleton O.data.tree
        ((pairOfLeaf O.skeleton O.plain (O.family.placement i).retained).firstLeaf O.plain).toNode)
      (inflatedPosition O.skeleton O.data.tree
        ((pairOfLeaf O.skeleton O.plain (O.family.placement i).retained).secondLeaf O.plain).toNode)) := by
    rw [hPl]
    exact coupleCoherent_output_true con
  have hsrc : O.source i con.canonical el' tc' cc' = revSourceT (A.source i c el tc cc) con :=
    lfSource_ext rfl HEq.rfl (heq_of_eq hPl) HEq.rfl HEq.rfl rfl
  obtain ⟨h', hh', hd'⟩ := exists_reverse_construction_true (s := A.source i c el tc cc) con
  obtain ⟨c', hc1, hc2⟩ := lfConstruction_transport hsrc.symm h'
  let op' : FamilyOperation (p := p) (kind := kind) O i := ⟨con.canonical, el', tc', cc', true, c'⟩
  refine ⟨op', ?_⟩
  have e1 := op'.familyState_output
  have e2 := (⟨c, el, tc, cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i).familyState_output
  have e3 : op'.output.familyState = A.familyState := by
    have e1' : op'.output.familyState = familyStep i O.familyState := by
      simpa only [op', ite_true] using e1
    have e2' : O.familyState = familyStep i A.familyState := by simpa only [O, ite_true] using e2
    rw [e1', e2']
    exact familyStep_involutive i A.familyState
  apply familyReconstruction_ext
  · exact (congrArg (unitTwistGarden (unitTwistGarden A.skeleton (A.family.placement i))) hPl).trans
      (unitTwistGarden_involutive A.skeleton (A.family.placement i))
  · exact familyState_heq_family e3
  · exact hc2.trans hd'
  · exact hc1.trans hh'

end WaveTurbulence.Stage1
