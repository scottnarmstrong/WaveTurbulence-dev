/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSignedSubset
public import WaveTurbulence.Foundations.VineEst.VineEstS2.LocalNodeLeafDifferences
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLRegionalPredecessors

/-! # Unit source coefficients for the two local incidence geometries -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Conditional geometric helper: a same-sign nested pair of actual crop
nodes has a unit coefficient difference in the source leaf-pair basis. -/
theorem clDescendant_difference_coeffs (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (q : GBranch (CLTreeForest R)) (u v : GNode (CLTreeForest R))
    (hd : u.IsDesc v)
    (hs : nodeSign (fun _ : Fin 1 => G.sign a.toNode) u.1 = nodeSign (fun _ : Fin 1 => G.sign a.toNode) v.1) :
    ∃ σ : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ, (∀ o, IsUnitCoeff (σ o)) ∧
      ∀ {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ z ∈ U, κ z.toNode = κ (z.child 0)-κ (z.child 1)+κ (z.child 2)) →
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        κ (clTreeNode R u)-κ (clTreeNode R v) = ∑ o, σ o • clOriginValue hU R hG κ o := by
  let S := u.leavesBelow \ v.leavesBelow
  let ζ := nodeSign (fun _ : Fin 1 => G.sign a.toNode) u.1
  refine ⟨clSignedSubsetCoeff hU R hG S q ζ,clSignedSubsetCoeff_unit hU R hG S q ζ,?_⟩
  intro E _ κ hc hp
  exact (node_difference_leaf_sum_of_desc (fun _ : Fin 1 => G.sign a.toNode)
    (fun z => κ (clTreeNode R z)) (clTreeNode_conservation_local hU R κ hc) u v hd hs).trans
      (clSignedSubset_sum hU R hG S q ζ κ hp)

/-- Conditional geometric helper: opposite signs on disjoint subtrees
produce a unit coefficient difference by pair cancellation on their union. -/
theorem clDisjoint_difference_coeffs (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (q : GBranch (CLTreeForest R)) (u v : GNode (CLTreeForest R))
    (hd : Disjoint u.leavesBelow v.leavesBelow)
    (hs : nodeSign (fun _ : Fin 1 => G.sign a.toNode) v.1 = -nodeSign (fun _ : Fin 1 => G.sign a.toNode) u.1) :
    ∃ σ : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ, (∀ o, IsUnitCoeff (σ o)) ∧
      ∀ {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ z ∈ U, κ z.toNode = κ (z.child 0)-κ (z.child 1)+κ (z.child 2)) →
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        κ (clTreeNode R u)-κ (clTreeNode R v) = ∑ o, σ o • clOriginValue hU R hG κ o := by
  let S := u.leavesBelow ∪ v.leavesBelow
  let ζ := nodeSign (fun _ : Fin 1 => G.sign a.toNode) u.1
  refine ⟨clSignedSubsetCoeff hU R hG S q ζ,clSignedSubsetCoeff_unit hU R hG S q ζ,?_⟩
  intro E _ κ hc hp
  exact (node_difference_leaf_sum_of_disjoint (fun _ : Fin 1 => G.sign a.toNode)
    (fun z => κ (clTreeNode R z)) (clTreeNode_conservation_local hU R κ hc) u v hd hs).trans
      (clSignedSubset_sum hU R hG S q ζ κ hp)

end WaveTurbulence.VineEstS2
