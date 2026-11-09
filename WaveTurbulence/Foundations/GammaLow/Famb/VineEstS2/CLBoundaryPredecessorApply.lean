/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorApply
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAffineBoundaryRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorApply` (sha256 c30148551637210b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Source-consistent affine boundary predecessor identities -/

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

theorem assemblyCoeff_upper_zeroΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) : assemblyCoeffΓ hM9 B hG v (.inr 0) = 0 :=
  clOriginCoeff_upper B.isBlock R hG _ _

/-- Set only the free variables to zero; all actual boundary data remain
arbitrary subject to their original signed source momentum relation. -/
theorem assembly_boundary_predecessor_applyΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    (∑ c, assemblyBranchBoundaryRowΓ hM9 B v c • β c) -
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => ∑ c, assemblyBranchBoundaryRowΓ hM9 B u c • β c) =
      (∑ p, assemblyCoeffΓ hM9 B hG v (.inl p) • (∑ c, assemblyPairBoundaryRowΓ hM9 B hG p c • β c)) +
      ∑ c, assemblyCoeffΓ hM9 B hG v (.inr c) • β c := by
  let κ := (clChainCoordinateEquivΓ (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9).symm 0
  have hb (u : (assemblyShapeΓ hM9 B).VIdx) :
      assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1) u = ∑ c, assemblyBranchBoundaryRowΓ hM9 B u c • β c := by
    simpa only [Pi.zero_apply,smul_zero,Finset.sum_const_zero,zero_add] using
      clChain_branch_affine_valueΓ (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9 0 u
  have hp (u : (assemblyShapeΓ hM9 B).VIdx) :
      assemblyPairValueΓ hM9 B hG (clExtendIndices R κ.1) u = ∑ c, assemblyPairBoundaryRowΓ hM9 B hG u c • β c := by
    simpa only [Pi.zero_apply,smul_zero,Finset.sum_const_zero,zero_add] using
      clChain_pair_affine_valueΓ (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9 hG 0 u
  have hbound (c : Fin 4) : clExtendIndices R κ.1 (clBoundaryNodes R c) = β c :=
    latticePoint_injective_of_ne_zero one_ne_zero (add_left_cancel (κ.2.2.2 c))
  have hi := assembly_predecessor_identityΓ hM9 B hG (clExtendIndices R κ.1) κ.2.1 κ.2.2.1 v
  have hprev : (assemblyPrevΓ hM9 B v).elim 0 (assemblyBranchValueΓ hM9 B (clExtendIndices R κ.1)) =
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => ∑ c, assemblyBranchBoundaryRowΓ hM9 B u c • β c) := by
    cases assemblyPrevΓ hM9 B v with
    | none => rfl
    | some u => exact hb u
  simpa only [hb,hp,hbound,hprev] using hi

end WaveTurbulence.GammaLow.Famb.VineEstS2
