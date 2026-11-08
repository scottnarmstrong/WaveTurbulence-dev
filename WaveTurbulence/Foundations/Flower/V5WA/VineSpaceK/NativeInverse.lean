/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates
/-! Data projection of the normalized decoration inverse, without its proofs. -/
@[expose] public section
namespace WaveTurbulence.VineSpaceK
open VineEstS2 VineEstS3 RegRed VineParamContract
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

theorem normalized_inverse_val (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → Fin d → ℤ)
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (assemblyShape hM9 B).VIdx → Fin d → ℤ) :
    ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 =
      fun z => clRebuildLabels R
        ((chainFlowChart hM9 B (β 2) (β 2 - β 3)).symm
          (fun i => jointFlip (assemblyShape hM9 B) x (assemblyVectorEquiv hM9 B i))).1 β z.1 := by
  unfold clNormalizedChainEquiv clChainCoordinateEquiv
  simp only [Equiv.symm_trans_apply]
  exact clLocalFromFlow_val B.isBlock R L base β hβ _
end WaveTurbulence.VineSpaceK
