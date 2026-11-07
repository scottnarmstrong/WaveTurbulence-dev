/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorCrop
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignRouteBudget

/-! # The total predecessor budget on actual interior branches -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem prod_clInteriorPredecessorBudget_le (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) :
    (∏ v : ↥(clInteriorBranches R), clPredecessorBudget R (clInteriorCrop hU R v)) ≤
      6561^clLocalOrder1 R := by
  classical
  calc
    _ = ∏ v ∈ Finset.univ.image (clInteriorCrop hU R), clPredecessorBudget R v :=
      (Finset.prod_image (fun _ _ _ _ he => clInteriorCrop_injective hU R he)).symm
    _ ≤ ∏ v : GBranch (CLTreeForest R), clPredecessorBudget R v :=
      Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun v _ _ => clPredecessorBudget_pos R v)
    _ ≤ _ := cl_signPredecessorRoute_cost_le hU R

end WaveTurbulence.VineEstS2
