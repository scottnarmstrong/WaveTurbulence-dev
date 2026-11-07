/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInternalDartNodes
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOrderedIdentity

/-! # Actual bonds representing every regional source pair and branch -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clRealizedNodeDart (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    InternalDart G.molecule U := Classical.choose (clNode_internalDart_exists hU R x hx hne)

noncomputable def clRealizedNodeBond (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    Bond G.molecule U := (internalDartBond G.molecule U (clRealizedNodeDart hU R x hx hne)).1

/-- This representative reads exactly the original source node label;
only internal source leaf matching is required. -/
theorem clRealizedNodeBond_value {E : Type*}
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode)
    (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    Mole.restrictLabels G κ (clRealizedNodeBond hU R x hx hne).1 = κ x := by
  let d := clRealizedNodeDart hU R x hx hne
  have hv := gardenInternalDartValue κ hp d
  have he := (internalBondDartEquiv G.molecule U).apply_symm_apply d
  have hb := internalDartValue_bondDart G.molecule U (fun e => Mole.restrictLabels G κ e.1)
    (internalDartBond G.molecule U d)
  change internalBondDart G.molecule U (internalDartBond G.molecule U d) = d at he
  rw [he] at hb
  exact hb.symm.trans (hv.trans (congrArg κ (Classical.choose_spec (clNode_internalDart_exists hU R x hx hne))))

noncomputable def clOrderedBranchBond (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R)
    (v : Fin (clLocalOrder1 R)) : Bond G.molecule U := by
  let z := Ei.e.symm v
  exact clRealizedNodeBond hU R z.1.toNode
    ((branch_mem_clRealizationNodes z.1).mpr (Finset.mem_erase.mp z.2).2)
    (fun he => (Finset.mem_erase.mp z.2).1 (Mole.branch_toNode_injective he))

noncomputable def clOrderedPairBond (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (p : Fin (clLocalOrder1 R)) : Bond G.molecule U := by
  let z := Ep.symm p
  exact clRealizedNodeBond hU R (z.1.firstLeaf hG).toNode
    (clRegionalPair_realization hG z.1 z.2).1
    (Ne.symm (Mole.branch_toNode_ne_leaf a (z.1.firstLeaf hG)))

theorem clOrderedBranchBond_value {E : Type*}
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R)
    (v : Fin (clLocalOrder1 R)) (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    Mole.restrictLabels G κ (clOrderedBranchBond hU R Ei v).1 = clOrderedBranchValue hU R Ei κ v :=
  clRealizedNodeBond_value hU R _ _ _ κ hp

theorem clOrderedPairBond_value {E : Type*}
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R))
    (p : Fin (clLocalOrder1 R)) (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    Mole.restrictLabels G κ (clOrderedPairBond hU R hG Ep p).1 = clOrderedPairValue hU R hG Ep κ p := by
  exact (clRealizedNodeBond_value hU R _ _ _ κ hp).trans
    (congrArg κ (clPairFirstLeaf_node hU R hG (Ep.symm p))).symm

end WaveTurbulence.VineEstS2
