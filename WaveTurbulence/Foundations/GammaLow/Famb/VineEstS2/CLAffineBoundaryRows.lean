/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.VineEst.VineEstS2.GapBoundaryAffine
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrixValues
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows` (sha256 0b39b575b5bd0377…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact affine source boundary rows for the frozen sumint datum -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyPairBoundaryRowΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) : Fin 4 → ℤ :=
  gapBoundaryRow (chainDecodeGapΓ hM9 B (clOrderedPairBond B.isBlock R hG (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v)))

noncomputable def assemblyBranchBoundaryRowΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : (assemblyShapeΓ hM9 B).VIdx) : Fin 4 → ℤ :=
  gapBoundaryRow (chainDecodeGapΓ hM9 B (clOrderedBranchBond B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v)))

theorem assemblyBoundaryRows_cosetΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    (∑ c, assemblyPairBoundaryRowΓ hM9 B hG v c) = 1 ∧ (∑ c, assemblyBranchBoundaryRowΓ hM9 B v c) = 1 :=
  ⟨sum_gapBoundaryRow _,sum_gapBoundaryRow _⟩

theorem assemblyPairBoundaryRow_zeroΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) : assemblyPairBoundaryRowΓ hM9 B hG v 0 = 0 := by
  norm_num [assemblyPairBoundaryRowΓ,gapBoundaryRow]

theorem assemblyBranchBoundaryRow_zeroΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : (assemblyShapeΓ hM9 B).VIdx) : assemblyBranchBoundaryRowΓ hM9 B v 0 = 0 := by
  norm_num [assemblyBranchBoundaryRowΓ,gapBoundaryRow]

theorem clChain_pair_affine_valueΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF) (hG : G.IsPlain)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    assemblyPairValueΓ hM9 B hG (clExtendIndices R κ.1) v =
      (∑ j, assemblyPairMatrixΓ hM9 B hG v j • x j) + ∑ c, assemblyPairBoundaryRowΓ hM9 B hG v c • β c := by
  calc
    _ = _ := clChain_pair_matrix_valueΓ hL B base β hβ hM9 hG x v
    _ = _ := by rw [assemblyPairBoundaryRowΓ,gapBoundaryRow_eval]; abel

theorem clChain_branch_affine_valueΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    let κ := (clChainCoordinateEquivΓ hL B base β hβ hM9).symm x
    assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1) v =
      (∑ j, assemblyBranchMatrixΓ hM9 B v j • x j) + ∑ c, assemblyBranchBoundaryRowΓ hM9 B v c • β c := by
  calc
    _ = _ := clChain_branch_matrix_valueΓ hL B base β hβ hM9 x v
    _ = _ := by rw [assemblyBranchBoundaryRowΓ,gapBoundaryRow_eval]; abel

end WaveTurbulence.GammaLow.Famb.VineEstS2
