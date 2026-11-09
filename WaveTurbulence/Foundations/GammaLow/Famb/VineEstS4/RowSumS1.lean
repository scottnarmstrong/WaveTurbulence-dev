/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowBridge
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At
public import WaveTurbulence.Foundations.Spine.CoherentObjects
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrderS1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS4.RowSum` (sha256 e6eb4e1fdf7e0d55…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Row sums and row coherence over pairs and branches (V5 Step 4b, step 1)

The rows of a vine-chain assembly are in bijection with the regional pairs (`assemblyPairBij`) and with the interior
branches (`assemblyBranchBij`).  Hence
* `step3D_M1`: `M₁ = Σ_{q regional} coupleCnt q + Σ_{c ∈ U \ a} treeCnt c`, a chart-free expression;
* `rowCoherent_iff`: `RowCoherent` is the chart-free statement `RowsCoh` (coherence of each regional couple and each
  interior tree of index `0`, with the parent-core layers `pairQ`, `branchQ`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg WaveTurbulence.LGSpine VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section Rows
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem rowCoupleG_eqΓ (v : (assemblyShapeΓ hM9 B).VIdx) :
    rowCoupleGΓ hM9 B RD hG layer hLayer v =
      coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) (assemblyPairOfΓ hM9 B hG v).1 :=
  incoherency_native_couple RD hG layer hLayer _

theorem rowTreeG_eqΓ (v : (assemblyShapeΓ hM9 B).VIdx) :
    rowTreeGΓ hM9 B RD hG layer hLayer v =
      treeCnt RD (layeredReconstruction RD hG layer hLayer) (assemblyBranchOfΓ hM9 B v).1 :=
  incoherency_native_tree RD hG layer hLayer _

/-- **Chart-free `M₁`.** -/
theorem step3D_M1Γ {d : ℕ} (badKind : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ)
    (centre : Fin 4 → Mom d) (wBar : Mom d) :
    (step3DΓ hM9 B RD hG layer hLayer badKind qOut centre wBar).M₁ =
      (∑ q ∈ clRegionalPairs hG U, coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) q) +
        ∑ c ∈ U.erase a, treeCnt RD (layeredReconstruction RD hG layer hLayer) c := by
  have e1 : (step3DΓ hM9 B RD hG layer hLayer badKind qOut centre wBar).M₁ =
      (∑ v, rowCoupleGΓ hM9 B RD hG layer hLayer v) + ∑ v, rowTreeGΓ hM9 B RD hG layer hLayer v := by
    unfold SumintDatum.M₁
    rw [← Finset.sum_add_distrib]
    rfl
  rw [e1]
  congr 1
  · simp_rw [rowCoupleG_eqΓ]
    rw [← Finset.sum_coe_sort (clRegionalPairs hG U)]
    exact (Equiv.sum_comp (assemblyPairBijΓ hG B hM9) (fun v =>
      coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) (assemblyPairOfΓ hM9 B hG v).1)).symm.trans
      (Finset.sum_congr rfl fun p _ => by rw [assemblyPairOf_bijΓ])
  · simp_rw [rowTreeG_eqΓ]
    rw [show U.erase a = clInteriorBranches R from rfl, ← Finset.sum_coe_sort (clInteriorBranches R)]
    exact (Equiv.sum_comp (assemblyBranchBijΓ hM9 B) (fun v =>
      treeCnt RD (layeredReconstruction RD hG layer hLayer) (assemblyBranchOfΓ hM9 B v).1)).symm.trans
      (Finset.sum_congr rfl fun c _ => by rw [assemblyBranchOf_bijΓ])

end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS4
