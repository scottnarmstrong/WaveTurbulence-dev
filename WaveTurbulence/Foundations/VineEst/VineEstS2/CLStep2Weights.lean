/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta

/-! # TARGET Step 2: the starred-kernel product as the sumint weight product

The native product `∏ K_Q^* ∏ K_T^*` of the CL-local expression is rewritten over the frozen
sumint row index `v`: the `v`-th factor of the first product is a function `assemblyWK` of the
pair momentum `k_v` and the `v`-th factor of the second is a function `assemblyWL` of the
branch momentum `ℓ_v`. They are the actual `K^*` factors, still depending on the clocks; the
expansion that makes them time-independent weights (Propositions `proplayer1/2`) is TARGET
Step 3. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The `K_Q^*` factor of the pair of the `v`-th sumint row, as a function of its momentum. -/
noncomputable def assemblyWK (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShape hM9 B).VIdx) (k : Mom d) : ℂ :=
  KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer (assemblyPairOf hM9 B hG v).1)
    (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode)
    (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode) k

/-- The `K_T^*` factor of the branch of the `v`-th sumint row, as a function of its momentum. -/
noncomputable def assemblyWL (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShape hM9 B).VIdx) (k : Mom d) : ℂ :=
  KTstar L γ δ F (nativeChainLayered D hG layer hLayer (assemblyBranchOf hM9 B v).1)
    (parentClock (t 0) (clLocalClock R t τ) (assemblyBranchOf hM9 B v).1.toNode)
    (clLocalClock R t τ (assemblyBranchOf hM9 B v).1) k

theorem clLocalStarProduct_eq_weights (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProduct D hG R L γ δ F layer hLayer base κ t τ =
      ∏ v : (assemblyShape hM9 B).VIdx,
        (assemblyWK hM9 B D hG L γ δ F layer hLayer t τ v
            (cosetDecoration G L base κ ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode) *
          assemblyWL hM9 B D hG L γ δ F layer hLayer t τ v
            (cosetDecoration G L base κ (assemblyBranchOf hM9 B v).1.toNode)) := by
  rw [Finset.prod_mul_distrib]
  simp only [clLocalStarProduct]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyPairOrder hG B hM9).symm)
      (fun p : ↥(clRegionalPairs hG U) => KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p.1)
        (parentClock (t 0) (clLocalClock R t τ) (p.1.firstLeaf hG).toNode)
        (parentClock (t 0) (clLocalClock R t τ) (p.1.secondLeaf hG).toNode)
        (cosetDecoration G L base κ (p.1.firstLeaf hG).toNode))).symm
  · rw [← Finset.prod_coe_sort]
    exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyIntOrder hM9 B).e.symm)
      (fun z : ↥(clInteriorBranches R) => KTstar L γ δ F (nativeChainLayered D hG layer hLayer z.1)
        (parentClock (t 0) (clLocalClock R t τ) z.1.toNode) (clLocalClock R t τ z.1)
        (cosetDecoration G L base κ z.1.toNode))).symm

end WaveTurbulence.VineEstS2
