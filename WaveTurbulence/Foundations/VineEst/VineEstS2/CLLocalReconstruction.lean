/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLIntegerReconstruction
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBondLabelInjectivity

/-! # Rebuilding the genuine V3 regional decoration from an integer flow -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Fold the raw integer node assignment before attaching source proofs. -/
noncomputable def clFlowNodeLabels (R : CLRegionData G U a b) (β : Fin 4 → (Fin d → ℤ))
    (k : FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3)) : GNode G.tree → (Fin d → ℤ) :=
  clRebuildLabels R k.1 β

theorem clFlowLabels_valid (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (k : FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3)) :
    let z : ↥(clLocalSupport R) → (Fin d → ℤ) := fun x => clFlowNodeLabels R β k x.1
    (∀ v ∈ U, clExtendIndices R z v.toNode = clExtendIndices R z (v.child 0)-
      clExtendIndices R z (v.child 1)+clExtendIndices R z (v.child 2)) ∧
    (∀ ℓ, Mole.IsInternalLeaf G U ℓ → clExtendIndices R z ℓ.toNode =
      clExtendIndices R z (G.pair ℓ).toNode) ∧
    ∀ j, base+latticePoint L (clExtendIndices R z (clBoundaryNodes R j)) =
      base+latticePoint L (β j) := by
  let κ := clFlowNodeLabels R β k
  refine ⟨?_,?_,?_⟩
  · intro v hv
    have hp := cl_realization_mem_support R ((branch_mem_clRealizationNodes v).mpr hv)
    rw [clExtendIndices_restrict R κ _ hp,
      clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 0),
      clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 1),
      clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 2)]
    exact clRebuildInteger_conservation hU R β hβ k v hv
  · intro ℓ hℓ
    have hp := cl_realization_mem_support R ((leaf_mem_clRealizationNodes ℓ).mpr hℓ)
    have hq := cl_realization_mem_support R ((leaf_mem_clRealizationNodes (G.pair ℓ)).mpr
      ((Mole.internal_leaf_pair_iff G U ℓ).mpr hℓ))
    rw [clExtendIndices_restrict R κ _ hp,clExtendIndices_restrict R κ _ hq]
    exact clRebuildLabels_matching R k.1 β ℓ hℓ
  · intro j
    rw [clExtendIndices_restrict R κ _ (clBoundaryNodes_mem_support R j)]
    exact congrArg (fun z => base+latticePoint L z) (clRebuildLabels_boundary hU R k.1 β j)


noncomputable def clLocalFromFlow (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (k : FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3)) :
    CLLocalDecoration R L base (fun j => base+latticePoint L (β j)) :=
  ⟨fun x => clFlowNodeLabels R β k x.1,clFlowLabels_valid hU R L base β hβ k⟩

/-- Expose only the data projection to consumers, keeping the conservation
proofs out of definitional comparison. -/
theorem clLocalFromFlow_val (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (k : FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3)) :
    (clLocalFromFlow hU R L base β hβ k).1 =
      fun x : ↥(clLocalSupport R) => clFlowNodeLabels R β k x.1 := by
  dsimp only [clLocalFromFlow]

/-- Reconstruction has no extra bond-label multiplicity. -/
theorem clLocalFromFlow_bondLabels (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (k : FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3)) :
    clLocalBondLabels R L base (fun j => base+latticePoint L (β j))
      (clLocalFromFlow hU R L base β hβ k) = k.1 := by
  unfold clLocalBondLabels
  rw [clLocalFromFlow_val]
  unfold clFlowNodeLabels
  funext e
  unfold Mole.restrictLabels
  have hx := cl_realization_mem_support R ((mem_clRealizationNodes _).mpr
    (internalDart_node_realization (internalBondDart G.molecule U (e,false))))
  change Mole.dartNode G e.1 ∈ clLocalSupport R at hx
  rw [clExtendIndices_restrict R (clRebuildLabels R k.1 β) _ hx]
  exact clRebuildLabels_bond R k.1 β e

/-- A physical boundary value determines its unique integer index when L≠0. -/
theorem clLocal_boundaryIndex {L : ℝ} (hL : L ≠ 0) (R : CLRegionData G U a b)
    (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (κ : CLLocalDecoration R L base (fun j => base+latticePoint L (β j))) (j : Fin 4) :
    clExtendIndices R κ.1 (clBoundaryNodes R j) = β j :=
  latticePoint_injective_of_ne_zero hL (add_left_cancel (κ.2.2.2 j))

end WaveTurbulence.VineEstS2
