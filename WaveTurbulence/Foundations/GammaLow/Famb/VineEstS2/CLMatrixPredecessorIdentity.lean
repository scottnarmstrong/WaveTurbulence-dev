/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrixValues
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorIdentity
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrixValues
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorIdentity` (sha256 a12737017408ef6b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The source predecessor identity holds for the actual decoder matrices -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- A polynomial identity on all free lattice inputs, obtained from the
literal regional source equations at zero boundary data. -/
theorem assembly_matrix_predecessor_applyΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (hG : G.IsPlain) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    (∑ j, assemblyBranchMatrixΓ hM9 B v j • x j) -
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => ∑ j, assemblyBranchMatrixΓ hM9 B u j • x j) =
      ∑ p, assemblyCoeffΓ hM9 B hG v (.inl p) • (∑ j, assemblyPairMatrixΓ hM9 B hG p j • x j) := by
  have hβ : ((G.sign a.toNode : ℤ) • ((0 : Fin 4 → (Fin d → ℤ)) 0-0)) = 0-0 := by simp
  let κ := (clChainCoordinateEquivΓ (L := 1) one_ne_zero B (0 : Mom d) 0 hβ hM9).symm x
  have hb (u : (assemblyShapeΓ hM9 B).VIdx) :
      assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1) u =
        ∑ j, assemblyBranchMatrixΓ hM9 B u j • x j := by
    simpa only [Pi.zero_apply,sub_self,smul_zero,add_zero,zero_add] using
      clChain_branch_matrix_valueΓ (L := 1) one_ne_zero B (0 : Mom d) 0 hβ hM9 x u
  have hp (u : (assemblyShapeΓ hM9 B).VIdx) :
      assemblyPairValueΓ hM9 B hG (clExtendIndices R κ.1) u =
        ∑ j, assemblyPairMatrixΓ hM9 B hG u j • x j := by
    simpa only [Pi.zero_apply,sub_self,smul_zero,add_zero,zero_add] using
      clChain_pair_matrix_valueΓ (L := 1) one_ne_zero B (0 : Mom d) 0 hβ hM9 hG x u
  have hbound (c : Fin 4) : clExtendIndices R κ.1 (clBoundaryNodes R c) = 0 := by
    exact latticePoint_injective_of_ne_zero one_ne_zero (add_left_cancel (κ.2.2.2 c))
  have hi := assembly_predecessor_identityΓ hM9 B hG (clExtendIndices R κ.1) κ.2.1 κ.2.2.1 v
  have hprev : (assemblyPrevΓ hM9 B v).elim 0 (assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1)) =
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => ∑ j, assemblyBranchMatrixΓ hM9 B u j • x j) := by
    cases assemblyPrevΓ hM9 B v with
    | none => rfl
    | some u => exact hb u
  simpa only [hb,hp,hprev,hbound,smul_zero,Finset.sum_const_zero,add_zero] using hi

end WaveTurbulence.GammaLow.Famb.VineEstS2
