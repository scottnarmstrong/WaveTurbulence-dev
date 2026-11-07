/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOriginCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SearchSupportBudget
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Actual CL predecessor rows and their coefficient budgets -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clPredecessorSupport (R : CLRegionData G U a b) (v : GBranch (CLTreeForest R)) :=
  searchLeafSupport (fun _ : Fin 1 => G.sign a.toNode)
    (nodeSign (fun _ : Fin 1 => G.sign a.toNode) v.1) v

noncomputable def clPredecessorBudget (R : CLRegionData G U a b) (v : GBranch (CLTreeForest R)) : ℕ :=
  ∏ u ∈ signPredecessorRoute (fun _ : Fin 1 => G.sign a.toNode) v, branchPredecessorCost u

theorem clPredecessorBudget_pos (R : CLRegionData G U a b) (v : GBranch (CLTreeForest R)) :
    1 ≤ clPredecessorBudget R v := by
  classical
  exact Finset.one_le_prod (fun u _ => branchPredecessorCost_pos u)

/-- Grouping the actual support by source-pair or boundary origin gives the
physical subtraction row, with no hypothetical reparametrization premise. -/
theorem cl_physical_predecessor_row {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch (CLTreeForest R)) :
    κ (clTreeNode R v.toNode)-physicalPredecessor (fun _ : Fin 1 => G.sign a.toNode)
      (fun x => κ (clTreeNode R x)) v =
      ∑ o, clOriginCoeff hU R hG (clPredecessorSupport R v) v o • clOriginValue hU R hG κ o := by
  calc
    _ = ∑ l ∈ clPredecessorSupport R v,
        predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v l • κ (clTreeNode R l.toNode) :=
      physical_predecessor_leaf_sum (fun _ : Fin 1 => G.sign a.toNode)
        (fun x : GNode (CLTreeForest R) => κ (clTreeNode R x)) (clTreeNode_conservation R κ hκ) v
    _ = ∑ l ∈ clPredecessorSupport R v,
        predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v l •
          clOriginValue hU R hG κ (clLeafOrigin hU R hG l) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [clLeafOrigin_value hU R hG κ hp]
    _ = _ := pushSignedCoeff_smul _ _ _ _

open Classical in
/-- The number of nonzero paired and boundary coefficients obeys the actual
heavy-route cost, including cancellations of pairs wholly inside the support. -/
theorem cl_predecessor_coeff_count_le (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (v : GBranch (CLTreeForest R)) :
    (Finset.univ.filter (fun p : ↥(clRegionalPairs hG U) =>
      clOriginCoeff hU R hG (clPredecessorSupport R v) v (.inl p) ≠ 0)).card +
    (Finset.univ.filter (fun c : Fin 4 =>
      clOriginCoeff hU R hG (clPredecessorSupport R v) v (.inr c) ≠ 0)).card ≤ clPredecessorBudget R v := by
  classical
  have hc := card_pushSignedCoeff_support_le (clPredecessorSupport R v) (clLeafOrigin hU R hG)
    (predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v)
  have he : (Finset.univ.filter (fun o : ↥(clRegionalPairs hG U) ⊕ Fin 4 =>
      clOriginCoeff hU R hG (clPredecessorSupport R v) v o ≠ 0)).card =
      (Finset.univ.filter (fun p : ↥(clRegionalPairs hG U) =>
        clOriginCoeff hU R hG (clPredecessorSupport R v) v (.inl p) ≠ 0)).card +
      (Finset.univ.filter (fun c : Fin 4 =>
        clOriginCoeff hU R hG (clPredecessorSupport R v) v (.inr c) ≠ 0)).card := by
    have hh := Fintype.card_congr (Equiv.subtypeSum (p := fun o : ↥(clRegionalPairs hG U) ⊕ Fin 4 =>
      clOriginCoeff hU R hG (clPredecessorSupport R v) v o ≠ 0))
    simpa only [Fintype.card_sum,Fintype.card_subtype] using hh
  change (Finset.univ.filter (fun o : ↥(clRegionalPairs hG U) ⊕ Fin 4 =>
    clOriginCoeff hU R hG (clPredecessorSupport R v) v o ≠ 0)).card ≤ _ at hc
  rw [he] at hc
  exact hc.trans (searchLeafSupport_card_le_route _ _ _)

end WaveTurbulence.VineEstS2
