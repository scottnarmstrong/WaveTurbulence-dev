/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSlotDifferenceCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalSlotFlow

/-! # Original garden slot differences have unit source inverse rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Restricting the original local branching incidence to the literal crop
preserves parent and all three children, including cut boundary children. -/
theorem clTreeSlot_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GBranch G.tree) (hv : v ∈ U) (i : Fin 4) :
    clTreeNode R (treeSlotNode ((clForestBranchEquiv hU R).symm ⟨v,hv⟩) i) = Mole.slotNode G v i := by
  let q := (clForestBranchEquiv hU R).symm ⟨v,hv⟩
  have hq : clTreeNode R q.toNode = v.toNode := by
    rw [clForestBranch_node]
    exact congrArg (fun z : ↥U => z.1.toNode) ((clForestBranchEquiv hU R).apply_symm_apply ⟨v,hv⟩)
  have hbranch : clTreeBranch R ⟨q.1.2,q.2⟩ = v :=
    Mole.branch_toNode_injective ((clTreeNode_branch R q).symm.trans hq)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hq
  · change clTreeNode R (q.child j) = v.child j
    rw [clTreeNode_child,hbranch]

/-- Opposite original incidence weights force one of the checked local
nested/disjoint geometries. Boundary slots are included without an extra
matching or nonzero-gap assumption. -/
theorem clSlot_difference_coeffs (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (v : GBranch G.tree) (hv : v ∈ U) (i j : Fin 4)
    (h : Mole.slotWeight G v i = -Mole.slotWeight G v j) :
    ∃ σ : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ, (∀ o, IsUnitCoeff (σ o)) ∧
      ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ z ∈ U, κ z.toNode = κ (z.child 0)-κ (z.child 1)+κ (z.child 2)) →
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        κ (Mole.slotNode G v i)-κ (Mole.slotNode G v j) = ∑ o, σ o • clOriginValue hU R hG κ o := by
  have hp : treeSlotParity i = -treeSlotParity j := by
    rcases Int.units_eq_one_or (G.sign v.toNode) with hs | hs <;>
      fin_cases i <;> fin_cases j <;> norm_num [Mole.slotWeight,hs,treeSlotParity] at h <;> norm_num [treeSlotParity]
  obtain ⟨σ,hσ,he⟩ := clTreeSlot_difference_coeffs hU R hG
    ((clForestBranchEquiv hU R).symm ⟨v,hv⟩) i j hp
  refine ⟨σ,hσ,?_⟩
  intro E _ κ hc hmatch
  have hh := he κ hc hmatch
  rw [clTreeSlot_node,clTreeSlot_node] at hh
  exact hh

end WaveTurbulence.VineEstS2
