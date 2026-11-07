/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepE1
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr6
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr8
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowCoh
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowBridge

/-!
# S2 REPRESENTS, VINE-E (2): VINEEST's premise `RowCoherent` holds for canonical gardens

V5's `rowCoherent_iff` reduces `RowCoherent` (for the Step 3 data `step3W … (qOutOf …)`) to the chart-free `RowsCoh`: every
regional couple and every interior tree of incoherency count `0` is coherent at the parent-core layers.  For a canonical
garden this is S2's `couple_coherent_at` / `tree_coherent_at` (RepBr6/RepBr8), with V5's bridges
`incoherency_native_couple` / `incoherency_native_tree` (count = native incoherency) and the identification of the slot clock
layers with the parent-core layers at non-root nodes (`clkLayer_nonroot`); regional leaves and interior branches are
non-root (`cl_realization_parent`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.Reg TTree
  VineParamContract

variable {w : ℕ} {S : Garden w}

theorem clkLayer_nonroot (p : ℕ) (layer0 : GBranch S.tree → ℕ) (ν : GNode S.tree) (h : ν.1.2 ≠ []) :
    clkLayer p layer0 (clkOfNode S ν) = layer0 (ν.parent h) := by
  unfold clkOfNode
  unfold nodeToSlot
  rw [dif_neg h]
  rfl

theorem parentCoreLayer_nonroot (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (ν : GNode S.tree) (h : ν.1.2 ≠ []) :
    parentCoreLayer D hS layer ν = layer (D.coreBranch hS (ν.parent h)).toNode := by
  unfold parentCoreLayer
  rw [dif_neg h]

/-- **`RowsCoh` for canonical gardens.** -/
theorem rowsCoh_of_canonical (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (p : ℕ)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} (hU : S.molecule.IsBlock U a b)
    (R : CLRegionData S U a b) :
    RowsCoh D hS layer hLayer p U a := by
  refine ⟨fun q hq hcnt => ?_, fun c hc hcnt => ?_⟩
  · have hg : (nativeCoupleLayered D hS layer hLayer q).incoherency (D.couple q).links = 0 := by
      rw [incoherency_native_couple]; exact hcnt
    have key := couple_coherent_at D hS layer hLayer p hcan q hg
    have hreal := clRegionalPair_realization hS q hq
    have hp := pairLeaf_ne (a := a) hS ⟨q, hq⟩
    obtain ⟨n1, -⟩ := cl_realization_parent hU R _ hreal.1 hp.1
    obtain ⟨n2, -⟩ := cl_realization_parent hU R _ hreal.2 hp.2
    have e1 : clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl q) 0) =
        (pairQ D hS layer q).1 := by
      show clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (clkOfNode S (q.firstLeaf hS).toNode) = _
      rw [clkLayer_nonroot p _ _ n1, pairQ, parentCoreLayer_nonroot D hS layer _ n1]
    have e2 : clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl q) 1) =
        (pairQ D hS layer q).2 := by
      show clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (clkOfNode S (q.secondLeaf hS).toNode) = _
      rw [clkLayer_nonroot p _ _ n2, pairQ, parentCoreLayer_nonroot D hS layer _ n2]
    rw [e1, e2] at key
    exact key
  · have hg : (nativeChainLayered D hS layer hLayer c).incoherency
        ((D.tree c).treeLinks ((nativeChainLayered D hS layer hLayer c).garden.sig 0)) = 0 := by
      rw [incoherency_native_tree]; exact hcnt
    have key := tree_coherent_at D hS layer hLayer p hcan c hg
    have hcU : c ∈ U := (Finset.mem_erase.mp hc).2
    have hca : c ≠ a := (Finset.mem_erase.mp hc).1
    have hreal : c.toNode ∈ RegRed.clRealizationNodes S U := (branch_mem_clRealizationNodes c).mpr hcU
    have hne : c.toNode ≠ a.toNode := fun h => hca (Mole.branch_toNode_injective h)
    obtain ⟨n1, -⟩ := cl_realization_parent hU R _ hreal hne
    have e1 : clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr c) 0) =
        (branchQ D hS layer c).1 := by
      show clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (clkOfNode S c.toNode) = _
      rw [clkLayer_nonroot p _ _ n1, branchQ, parentCoreLayer_nonroot D hS layer _ n1]
    have e2 : clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr c) 1) =
        (branchQ D hS layer c).2 := by
      rfl
    rw [e1, e2] at key
    exact key

/-- **VINEEST's `RowCoherent` premise for a unit of a canonical garden.** -/
theorem rowCoherent_of_canonical (hM9 : VINEPARAM) {U : Finset (GBranch S.tree)} {a b : GBranch S.tree}
    {R : CLRegionData S U a b} {n : ℕ} (B : CLChainAssembly S R n) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer))
    {d : ℕ} (centre : Fin 4 → Mom d) (wBar : Mom d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) :
    RowCoherent hM9 B D hS layer hLayer
      (step3W hM9 B D hS layer hLayer (canonBadKind hM9 B D hS layer) (qOutOf D hS layer a b R) centre wBar)
      L γ δ F p := by
  rw [rowCoherent_iff hM9 B D hS layer hLayer _ rfl rfl]
  exact rowsCoh_of_canonical D hS layer hLayer p hcan B.isBlock R

end WaveTurbulence.Represents
