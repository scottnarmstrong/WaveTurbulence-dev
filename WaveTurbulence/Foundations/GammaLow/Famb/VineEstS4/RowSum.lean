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
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowOrder
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
open WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg WaveTurbulence.LGSpine VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section Rows
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem assemblyPairOf_bijΓ (p : ↥(clRegionalPairs hG U)) :
    assemblyPairOfΓ hM9 B hG (assemblyPairBijΓ hG B hM9 p) = p := by
  apply (assemblyPairBijΓ hG B hM9).injective
  rw [assemblyPairBij_assemblyPairOfΓ]

theorem assemblyBranchOf_bijΓ (c : ↥(clInteriorBranches R)) :
    assemblyBranchOfΓ hM9 B (assemblyBranchBijΓ hM9 B c) = c := by
  apply (assemblyBranchBijΓ hM9 B).injective
  rw [assemblyBranchBij_assemblyBranchOfΓ]

end Rows

end WaveTurbulence.GammaLow.Famb.VineEstS4
