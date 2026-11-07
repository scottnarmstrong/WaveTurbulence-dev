/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia9
import Mathlib.Tactic

/-!
# `OpsCommute` from the four diamonds and the reversal of operations
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

theorem FamilyOperation.exists_cast {A1 A2 : FamilyReconstruction w ι} (h : A1 = A2) {j : ι}
    (op : FamilyOperation (p := p) (kind := kind) A1 j) :
    ∃ op' : FamilyOperation (p := p) (kind := kind) A2 j, op'.output = op.output := by
  subst h; exact ⟨op, rfl⟩

/-- Every operation can be reversed (both choices). -/
theorem FamilyOperation.exists_rev {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    ∃ r : FamilyOperation (p := p) (kind := kind) op.output i, r.output = A := by
  rcases op with ⟨c, el, tc, cc, ε, con⟩
  cases ε
  · exact exists_reverse_op_false A i c el tc cc con
  · exact exists_reverse_op_true A i c el tc cc con

/-- The Diamond statement for all four combinations of choices. -/
def DiamondProp (p : ℕ) (kind : Bool) (w : ℕ) (ι : Type*) : Prop :=
  ∀ (A : FamilyReconstruction w ι) (i j : ι) (P : PairCtx p kind A i j) (ci cj : Bool)
    (con : LFConstruction P.srcI ci) (hj : LFConstruction P.srcJ cj),
    ∃ (opj : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, ci, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j)
      (opi : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, cj, hj⟩ : FamilyOperation (p := p) (kind := kind) A j)) i),
      opj.output = opi.output

theorem diamondProp_of_TT (hTT : ∀ (A : FamilyReconstruction w ι) (i j : ι) (P : PairCtx p kind A i j)
    (con : LFConstruction P.srcI true) (hj : LFConstruction P.srcJ true),
    ∃ (opj : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) j)
      (opi : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, true, hj⟩ : FamilyOperation (p := p) (kind := kind) A j)) i),
      opj.output = opi.output) : DiamondProp p kind w ι := by
  intro A i j P ci cj con hj
  cases ci <;> cases cj
  · exact P.diamond_FF con hj
  · exact P.diamond_FT con hj
  · exact P.diamond_TF con hj
  · exact hTT A i j P con hj

/-- **`OpsCommute` from the Diamond and reversal.** -/
theorem opsCommute_of_diamond (hD : DiamondProp p kind w ι) : OpsCommute p kind w ι := by
  intro A i j hij op1 op2
  obtain ⟨rev1, hrev1⟩ := FamilyOperation.exists_rev op1
  let P : PairCtx p kind op1.output i j :=
    ⟨hij, rev1.canonical, rev1.eligible, rev1.treeCoherent, rev1.coupleCoherent,
      op2.eligible, op2.treeCoherent, op2.coupleCoherent⟩
  obtain ⟨opj, opi, hdia⟩ := hD op1.output i j P rev1.choice op2.choice rev1.construction op2.construction
  obtain ⟨op2', hop2'⟩ := FamilyOperation.exists_cast hrev1 opj
  obtain ⟨ropi, hropi⟩ := FamilyOperation.exists_rev opi
  have hW : opi.output = op2'.output := by rw [hop2', ← hdia]
  obtain ⟨op1', hop1'⟩ := FamilyOperation.exists_cast hW ropi
  exact ⟨op2', op1', hop1'.trans hropi⟩

end WaveTurbulence.Stage1
