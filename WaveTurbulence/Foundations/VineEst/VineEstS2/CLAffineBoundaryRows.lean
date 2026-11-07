/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.VineEst.VineEstS2.GapBoundaryAffine

/-! # Exact affine source boundary rows for the frozen sumint datum -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyPairBoundaryRow (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) : Fin 4 → ℤ :=
  gapBoundaryRow (chainDecodeGap hM9 B (clOrderedPairBond B.isBlock R hG (assemblyPairOrder hG B hM9) ((assemblyRowEquiv hM9 B).symm v)))

noncomputable def assemblyBranchBoundaryRow (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : (assemblyShape hM9 B).VIdx) : Fin 4 → ℤ :=
  gapBoundaryRow (chainDecodeGap hM9 B (clOrderedBranchBond B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v)))

theorem assemblyBoundaryRows_coset (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) :
    (∑ c, assemblyPairBoundaryRow hM9 B hG v c) = 1 ∧ (∑ c, assemblyBranchBoundaryRow hM9 B v c) = 1 :=
  ⟨sum_gapBoundaryRow _,sum_gapBoundaryRow _⟩

theorem assemblyPairBoundaryRow_zero (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) : assemblyPairBoundaryRow hM9 B hG v 0 = 0 := by
  norm_num [assemblyPairBoundaryRow,gapBoundaryRow]

theorem assemblyBranchBoundaryRow_zero (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : (assemblyShape hM9 B).VIdx) : assemblyBranchBoundaryRow hM9 B v 0 = 0 := by
  norm_num [assemblyBranchBoundaryRow,gapBoundaryRow]

theorem clChain_pair_affine_value {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM) (hG : G.IsPlain)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShape hM9 B).VIdx) :
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    assemblyPairValue hM9 B hG (clExtendIndices R κ.1) v =
      (∑ j, assemblyPairMatrix hM9 B hG v j • x j) + ∑ c, assemblyPairBoundaryRow hM9 B hG v c • β c := by
  calc
    _ = _ := clChain_pair_matrix_value hL B base β hβ hM9 hG x v
    _ = _ := by rw [assemblyPairBoundaryRow,gapBoundaryRow_eval]; abel

theorem clChain_branch_affine_value {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShape hM9 B).VIdx) :
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    assemblyBranchValue hM9 B (clExtendIndices R κ.1) v =
      (∑ j, assemblyBranchMatrix hM9 B v j • x j) + ∑ c, assemblyBranchBoundaryRow hM9 B v c • β c := by
  calc
    _ = _ := clChain_branch_matrix_value hL B base β hβ hM9 x v
    _ = _ := by rw [assemblyBranchBoundaryRow,gapBoundaryRow_eval]; abel

end WaveTurbulence.VineEstS2
