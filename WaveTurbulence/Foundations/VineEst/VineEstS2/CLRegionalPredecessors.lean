/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOrderedIdentity
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorBudget

/-! # Regional conservation suffices for actual predecessor rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clTreeNode_conservation_local {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, v ∈ U → κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (v : GBranch (CLTreeForest R)) :
    κ (clTreeNode R v.toNode) = κ (clTreeNode R (v.child 0))-
      κ (clTreeNode R (v.child 1))+κ (clTreeNode R (v.child 2)) := by
  rw [clTreeNode_branch,clTreeNode_child,clTreeNode_child,clTreeNode_child]
  exact hκ _ (clTreeBranch_mem hU R _)

/-- Grouping the actual support by source-pair or boundary origin gives the
physical subtraction row, with no hypothetical reparametrization premise. -/
theorem cl_physical_predecessor_row_local {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, v ∈ U → κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch (CLTreeForest R)) :
    κ (clTreeNode R v.toNode)-physicalPredecessor (fun _ : Fin 1 => G.sign a.toNode)
      (fun x => κ (clTreeNode R x)) v =
      ∑ o, clOriginCoeff hU R hG (clPredecessorSupport R v) v o • clOriginValue hU R hG κ o := by
  calc
    _ = ∑ l ∈ clPredecessorSupport R v,
        predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v l • κ (clTreeNode R l.toNode) :=
      physical_predecessor_leaf_sum (fun _ : Fin 1 => G.sign a.toNode)
        (fun x : GNode (CLTreeForest R) => κ (clTreeNode R x)) (clTreeNode_conservation_local hU R κ hκ) v
    _ = ∑ l ∈ clPredecessorSupport R v,
        predecessorLeafCoeff (fun _ : Fin 1 => G.sign a.toNode) v l •
          clOriginValue hU R hG κ (clLeafOrigin hU R hG l) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [clLeafOrigin_value hU R hG κ hp]
    _ = _ := pushSignedCoeff_smul _ _ _ _

/-- The numbered k and ell variables are actual source pair and branch
momenta. The identity holds in every abelian group, hence also coefficientwise. -/
theorem clOrdered_predecessor_identity_local {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R))
    (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, v ∈ U → κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : Fin (clLocalOrder1 R)) :
    clOrderedBranchValue hU R Ei κ v-(clOrderedPrev hU R Ei v).elim 0 (clOrderedBranchValue hU R Ei κ) =
      (∑ p, clOrderedCoeff hU R hG Ei Ep v (.inl p) • clOrderedPairValue hU R hG Ep κ p) +
      ∑ c, clOrderedCoeff hU R hG Ei Ep v (.inr c) • κ (clBoundaryNodes R c) := by
  let u := Ei.e.symm v
  have hr := cl_physical_predecessor_row_local hU R hG κ hκ hp (clInteriorCrop hU R u)
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

end WaveTurbulence.VineEstS2
