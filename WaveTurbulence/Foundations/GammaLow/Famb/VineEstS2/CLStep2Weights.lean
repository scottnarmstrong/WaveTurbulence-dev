/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Weights
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssemblyOf
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Weights` (sha256 035d5da0cf7b4877…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # TARGET Step 2: the starred-kernel product as the sumint weight product

The native product `∏ K_Q^* ∏ K_T^*` of the CL-local expression is rewritten over the frozen
sumint row index `v`: the `v`-th factor of the first product is a function `assemblyWK` of the
pair momentum `k_v` and the `v`-th factor of the second is a function `assemblyWL` of the
branch momentum `ℓ_v`. They are the actual `K^*` factors, still depending on the clocks; the
expansion that makes them time-independent weights (Propositions `proplayer1/2`) is TARGET
Step 3. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The `K_Q^*` factor of the pair of the `v`-th sumint row, as a function of its momentum. -/
noncomputable def assemblyWKΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShapeΓ hM9 B).VIdx) (k : Mom d) : ℂ :=
  VineEst.selCoupleRow L γ δ F D hG layer hLayer (assemblyPairOfΓ hM9 B hG v).1
    (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode)
    (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode) k

/-- The `K_T^*` factor of the branch of the `v`-th sumint row, as a function of its momentum. -/
noncomputable def assemblyWLΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShapeΓ hM9 B).VIdx) (k : Mom d) : ℂ :=
  VineEst.selTreeRow L γ δ F D hG layer hLayer (assemblyBranchOfΓ hM9 B v).1
    (parentClock (t 0) (clLocalClock R t τ) (assemblyBranchOfΓ hM9 B v).1.toNode)
    (clLocalClock R t τ (assemblyBranchOfΓ hM9 B v).1) k

theorem clLocalStarProduct_eq_weightsΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProduct D hG R L γ δ F layer hLayer base κ t τ =
      ∏ v : (assemblyShapeΓ hM9 B).VIdx,
        (assemblyWKΓ hM9 B D hG L γ δ F layer hLayer t τ v
            (cosetDecoration G L base κ ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode) *
          assemblyWLΓ hM9 B D hG L γ δ F layer hLayer t τ v
            (cosetDecoration G L base κ (assemblyBranchOfΓ hM9 B v).1.toNode)) := by
  rw [Finset.prod_mul_distrib]
  simp only [clLocalStarProduct]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquivΓ hM9 B).symm.trans (assemblyPairOrderΓ hG B hM9).symm)
      (fun p : ↥(clRegionalPairs hG U) => VineEst.selCoupleRow L γ δ F D hG layer hLayer p.1
        (parentClock (t 0) (clLocalClock R t τ) (p.1.firstLeaf hG).toNode)
        (parentClock (t 0) (clLocalClock R t τ) (p.1.secondLeaf hG).toNode)
        (cosetDecoration G L base κ (p.1.firstLeaf hG).toNode))).symm
  · rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquivΓ hM9 B).symm.trans (assemblyIntOrderΓ hM9 B).e.symm)
      (fun z : ↥(clInteriorBranches R) => VineEst.selTreeRow L γ δ F D hG layer hLayer z.1
        (parentClock (t 0) (clLocalClock R t τ) z.1.toNode) (clLocalClock R t τ z.1)
        (cosetDecoration G L base κ z.1.toNode))).symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
