/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia11
import Mathlib.Tactic

/-!
# Diamond for two `true` operations: the two orders have the same skeleton and family
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i j : ι}
  (P : PairCtx p kind A i j)

/-- The operation at member `j` of the output of the `true` operation at `i`. -/
@[expose] noncomputable def PairCtx.opJT (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true) :
    FamilyOperation (p := p) (kind := kind)
      (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j :=
  ⟨con.canonical, eligible_transport_true con (CoreFamily.nextPlacement_lower A.family i j) P.elJ,
    transT_treeCoherent A i j P.hij P.c P.el P.tc P.cc con P.tcJ,
    transT_coupleCoherent A i j P.hij P.c P.el P.tc P.cc con P.ccJ, true, P.constT con hj⟩

theorem PairCtx.TT_famstate (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true) :
    (P.opJT con hj).output.familyState = (P.swap.opJT hj con).output.familyState := by
  have h1 := (P.opJT con hj).familyState_output
  have h2 := (P.swap.opJT hj con).familyState_output
  have h3 := (⟨P.c, P.el, P.tc, P.cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i).familyState_output
  have h4 := (⟨P.c, P.elJ, P.tcJ, P.ccJ, true, hj⟩ : FamilyOperation (p := p) (kind := kind) A j).familyState_output
  rw [if_pos (by rfl)] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact (familyStep_commute i j A.familyState).symm

end WaveTurbulence.Stage1
