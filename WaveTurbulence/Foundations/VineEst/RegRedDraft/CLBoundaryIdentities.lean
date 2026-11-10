/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLExternalSlots
public import WaveTurbulence.Foundations.Spine.GardenEnergyCorrespondence

/-! # Actual CL boundary momentum and resonance identities (TARGET vineest Step 1) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Finset

theorem slotWeight_parent {w : ℕ} (G : Garden w) (v : GBranch G.tree) :
    Mole.slotWeight G v 0 = ((G.sign v.toNode : ℤ) : ℝ) := by
  rcases Int.units_eq_one_or (G.sign v.toNode) with h | h <;> norm_num [Mole.slotWeight,h]

theorem slotWeight_child {w : ℕ} (G : Garden w) (v : GBranch G.tree) (i : Fin 3) :
    Mole.slotWeight G v i.succ = -((G.sign (v.child i) : ℤ) : ℝ) := by
  rcases Int.units_eq_one_or (G.sign v.toNode) with h | h <;>
    fin_cases i <;> norm_num [Mole.slotWeight,Mole.child_sign_formula,h]

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Exact regional divergence on a current connected CL block, including the
upper parent slot and exactly the three outgoing child slots. -/
theorem cl_slotSum_boundary (hB : G.molecule.IsBlock S a b) (D : CLRegionData G S a b)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (A : GNode G.tree → E)
    (hA : ∀ ℓ, A ℓ.toNode = A (G.pair ℓ).toNode) :
    (∑ v ∈ S, Mole.slotSum G A v) =
      ((G.sign a.toNode : ℤ) : ℝ) • A a.toNode -
        ((G.sign (a.child D.excluded) : ℤ) : ℝ) • A (a.child D.excluded) -
        ((G.sign (b.child D.positive) : ℤ) : ℝ) • A (b.child D.positive) -
        ((G.sign (b.child D.negative) : ℤ) : ℝ) • A (b.child D.negative) := by
  rw [sum_slotSum_eq_externalSlots G S A hA,cl_sum_externalSlotSum hB A,
    cl_externalSlotSum_upper hB D A,cl_externalSlotSum_lower hB D A,
    slotWeight_parent,slotWeight_child,slotWeight_child,slotWeight_child]
  simp only [neg_smul]
  abel

noncomputable def clBoundaryEnergy {d : ℕ} (D : CLRegionData G S a b) (k : GNode G.tree → Mom d) : ℝ :=
  ((G.sign (a.child D.excluded) : ℤ) : ℝ) * ‖k (a.child D.excluded)‖^2 +
    ((G.sign (b.child D.positive) : ℤ) : ℝ) * ‖k (b.child D.positive)‖^2 +
    ((G.sign (b.child D.negative) : ℤ) : ℝ) * ‖k (b.child D.negative)‖^2 -
    ((G.sign a.toNode : ℤ) : ℝ) * ‖k a.toNode‖^2

end WaveTurbulence.RegRed
