/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLTreeBranchEquiv
public import WaveTurbulence.Foundations.VineEst.VineEstS2.PredecessorBudget
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalFactors

/-! # Exponential coefficient budget on the actual CL realization -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clRealizationTree_order_eq_local_add_one (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) : (clRealizationTree R).order = clLocalOrder1 R+1 := by
  rw [clRealizationTree_order hU R]
  change U.card = (U.erase a).card+1
  exact (Finset.card_erase_add_one hU.2.1).symm

theorem clLocalOrder1_pos (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    0 < clLocalOrder1 R := by
  have hd := hU
  change 0 < (U.erase a).card
  exact Finset.card_pos.mpr ⟨b,Finset.mem_erase.mpr ⟨Ne.symm hd.2.2.2.1,hd.2.2.1⟩⟩

/-- A concrete universal C₀=81 for the numerical predecessor cost on the
actual source realization. The source region always has at least two joints. -/
theorem cl_predecessorCostProduct_le (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    predecessorCostProduct (clRealizationTree R) ≤ 81^clLocalOrder1 R := by
  have hn := clLocalOrder1_pos hU R
  calc
    _ ≤ 9^(clRealizationTree R).order := predecessorCostProduct_le _
    _ = 9^(clLocalOrder1 R+1) := congrArg (fun n => 9^n) (clRealizationTree_order_eq_local_add_one hU R)
    _ ≤ 9^(2*clLocalOrder1 R) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 81^clLocalOrder1 R := by rw [pow_mul]; rfl

end WaveTurbulence.VineEstS2
