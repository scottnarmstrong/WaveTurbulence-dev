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

/-- The numbered k and ell variables are actual source pair and branch
momenta. The identity holds in every abelian group, hence also coefficientwise. -/
theorem clOrdered_predecessor_identity {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R))
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : Fin (clLocalOrder1 R)) :
    clOrderedBranchValue hU R Ei κ v-(clOrderedPrev hU R Ei v).elim 0 (clOrderedBranchValue hU R Ei κ) =
      (∑ p, clOrderedCoeff hU R hG Ei Ep v (.inl p) • clOrderedPairValue hU R hG Ep κ p) +
      ∑ c, clOrderedCoeff hU R hG Ei Ep v (.inr c) • κ (clBoundaryNodes R c) := by
  let u := Ei.e.symm v
  have hr := cl_physical_predecessor_row hU R hG κ hκ hp (clInteriorCrop hU R u)
  rw [clInteriorCrop_node,clInteriorPredecessor_value] at hr
  have he : (clOrderedPrev hU R Ei v).elim 0 (clOrderedBranchValue hU R Ei κ) =
      (clInteriorPredecessor hU R u).elim 0 (fun z => κ z.1.toNode) := by
    unfold clOrderedPrev
    cases hz : clInteriorPredecessor hU R u with
    | none => simp only [Option.map_none,Option.elim_none]
    | some z => simp only [Option.map_some,Option.elim_some,clOrderedBranchValue,Equiv.symm_apply_apply]
  rw [he]
  calc
    _ = _ := hr
    _ = _ := by
      rw [Fintype.sum_sum_type]
      congr 1
      exact (Ep.symm.sum_comp (fun p =>
        clOriginCoeff hU R hG (clPredecessorSupport R (clInteriorCrop hU R u))
          (clInteriorCrop hU R u) (.inl p) • clOriginValue hU R hG κ (.inl p))).symm

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
