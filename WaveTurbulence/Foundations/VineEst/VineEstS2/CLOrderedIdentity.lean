/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOrderedRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorBudget

/-! # Numbered source predecessor identities in sumint's subtraction form -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clOrderedBudget (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R)
    (v : Fin (clLocalOrder1 R)) : ℕ :=
  clPredecessorBudget R (clInteriorCrop hU R (Ei.e.symm v))

noncomputable def clOrderedBranchValue {E : Type*} (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (Ei : CLIntOrder hU R) (κ : GNode G.tree → E) (v : Fin (clLocalOrder1 R)) : E :=
  κ (Ei.e.symm v).1.toNode

noncomputable def clOrderedPairValue {E : Type*} (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (hG : G.IsPlain) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (κ : GNode G.tree → E)
    (p : Fin (clLocalOrder1 R)) : E :=
  clOriginValue hU R hG κ (.inl (Ep.symm p))

open Classical in
theorem clOrdered_coeff_count_le (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (v : Fin (clLocalOrder1 R)) :
    (Finset.univ.filter (fun p => clOrderedCoeff hU R hG Ei Ep v (.inl p) ≠ 0)).card +
    (Finset.univ.filter (fun c => clOrderedCoeff hU R hG Ei Ep v (.inr c) ≠ 0)).card ≤ clOrderedBudget hU R Ei v := by
  classical
  have he := Finset.card_equiv Ep.symm
    (s := Finset.univ.filter (fun p => clOrderedCoeff hU R hG Ei Ep v (.inl p) ≠ 0))
    (t := Finset.univ.filter (fun p => clOriginCoeff hU R hG
      (clPredecessorSupport R (clInteriorCrop hU R (Ei.e.symm v)))
      (clInteriorCrop hU R (Ei.e.symm v)) (.inl p) ≠ 0))
    (fun p => ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩⟩)
  rw [he]
  exact cl_predecessor_coeff_count_le hU R hG _

theorem clOrderedBudget_pos (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R)
    (v : Fin (clLocalOrder1 R)) : 1 ≤ clOrderedBudget hU R Ei v := clPredecessorBudget_pos R _

theorem prod_clOrderedBudget_le (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R) :
    (∏ v : Fin (clLocalOrder1 R), clOrderedBudget hU R Ei v) ≤ 6561^clLocalOrder1 R := by
  calc
    _ = ∏ v : ↥(clInteriorBranches R), clPredecessorBudget R (clInteriorCrop hU R v) :=
      Ei.e.symm.prod_comp _
    _ ≤ _ := prod_clInteriorPredecessorBudget_le hU R

end WaveTurbulence.VineEstS2
