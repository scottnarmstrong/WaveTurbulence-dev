/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFComposeTrue1
import Mathlib.Tactic

/-!
# T2 for a first operation with choice `true`
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {LG : LayeredGarden w}

section Instances
variable {s : LFSource p kind LG} (h : LFConstruction s true)

theorem revSourceT_baseData_false : (revSourceT s h).baseData false = s.baseData true :=
  (LFSource.baseData_false _).trans (normalizedData_output_true h)

theorem revSourceT_base_false : (revSourceT s h).base false = s.base true := by
  have K := normalized_output h
  rw [pairs_true_exc s] at K
  exact K

/-- Composition `true` then `false`: one operation with choice `true`. -/
theorem exists_compose_true_false (h2 : LFConstruction (revSourceT s h) false) :
    ∃ h3 : LFConstruction s true, h3.output = h2.output ∧ HEq h3.data h2.data :=
  exists_compose_construction_true h h2 rfl (revSourceT_base_false h)
    (heq_of_eq (revSourceT_baseData_false h)) (fun _ => rfl)
    (fun _ => congrArg Subtype.val (LFSource.pairs_false _ _))

/-- Composition `true` then `true`: one operation with choice `false`. -/
theorem exists_compose_true_true (h2 : LFConstruction (revSourceT s h) true) :
    ∃ h3 : LFConstruction s false, h3.output = h2.output ∧ HEq h3.data h2.data :=
  exists_compose_construction_true h h2 (unitTwistGarden_involutive s.skeleton s.placement)
    (revSourceT_base_true h) (revSourceT_baseData_heq h)
    (fun b => coreBranchEquiv_twice_val s.skeleton s.placement b)
    (fun q => (revSourceT_pairs_twice_val h q).trans (congrArg Subtype.val (LFSource.pairs_false s q)).symm)

end Instances


/-- **Composition at one member, first operation with choice `true`.** -/
theorem exists_compose_op_true (A : FamilyReconstruction w ι) (i : ι)
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
    (con : LFConstruction (A.source i c el tc cc) true)
    (op2 : FamilyOperation (p := p) (kind := kind)
      (FamilyOperation.output (⟨c, el, tc, cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) i) :
    ∃ op3 : FamilyOperation (p := p) (kind := kind) A i, op3.output = op2.output := by
  let O := FamilyOperation.output (⟨c, el, tc, cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)
  have hPl : O.family.placement i = reversePlacement A.skeleton (A.family.placement i) :=
    A.family.nextPlacement_self i
  rcases op2 with ⟨c2, el2, tc2, cc2, ε2, con2⟩
  have hsrc : O.source i c2 el2 tc2 cc2 = revSourceT (A.source i c el tc cc) con :=
    lfSource_ext rfl HEq.rfl (heq_of_eq hPl) HEq.rfl HEq.rfl rfl
  obtain ⟨k2, hk1, hk2⟩ := lfConstruction_transport hsrc con2
  have e1 := (⟨c, el, tc, cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i).familyState_output
  cases ε2 with
  | false =>
    obtain ⟨h3, ho, hd⟩ := exists_compose_true_false con k2
    refine ⟨⟨c, el, tc, cc, true, h3⟩, ?_⟩
    apply familyReconstruction_ext
    · rfl
    · exact HEq.rfl
    · exact hd.trans hk2
    · exact ho.trans hk1
  | true =>
    obtain ⟨h3, ho, hd⟩ := exists_compose_true_true con k2
    refine ⟨⟨c, el, tc, cc, false, h3⟩, ?_⟩
    have e3 : (FamilyOperation.output (⟨c, el, tc, cc, false, h3⟩ : FamilyOperation (p := p) (kind := kind) A i)).familyState =
        (FamilyOperation.output (⟨c2, el2, tc2, cc2, true, con2⟩ : FamilyOperation (p := p) (kind := kind) O i)).familyState := by
      have a1 := (⟨c, el, tc, cc, false, h3⟩ : FamilyOperation (p := p) (kind := kind) A i).familyState_output
      have a2 := (⟨c2, el2, tc2, cc2, true, con2⟩ : FamilyOperation (p := p) (kind := kind) O i).familyState_output
      have e1' : O.familyState = familyStep i A.familyState := by simpa only [O, ite_true] using e1
      have a1' : (FamilyOperation.output (⟨c, el, tc, cc, false, h3⟩ : FamilyOperation (p := p) (kind := kind) A i)).familyState
          = A.familyState := by simpa only [Bool.false_eq_true, ite_false] using a1
      have a2' : (FamilyOperation.output (⟨c2, el2, tc2, cc2, true, con2⟩ : FamilyOperation (p := p) (kind := kind) O i)).familyState
          = familyStep i O.familyState := by simpa only [ite_true] using a2
      rw [a1', a2', e1']
      exact (familyStep_involutive i A.familyState).symm
    apply familyReconstruction_ext
    · exact ((congrArg (unitTwistGarden (unitTwistGarden A.skeleton (A.family.placement i))) hPl).trans
        (unitTwistGarden_involutive A.skeleton (A.family.placement i))).symm
    · exact familyState_heq_family e3
    · exact hd.trans hk2
    · exact ho.trans hk1

end WaveTurbulence.Stage1
