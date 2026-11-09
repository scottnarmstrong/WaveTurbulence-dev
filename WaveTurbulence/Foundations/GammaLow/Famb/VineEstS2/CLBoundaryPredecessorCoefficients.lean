/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorApply
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SourceBoundaryBasis
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLBoundaryPredecessorApply
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorCoefficients` (sha256 665b28046fa0615e…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # All four exact affine identities of frozen sumint hypothesis (ii) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assembly_boundary_predecessor_coeffΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) (c : Fin 4) :
    assemblyBranchBoundaryRowΓ hM9 B v c -
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => assemblyBranchBoundaryRowΓ hM9 B u c) =
      (∑ p, assemblyCoeffΓ hM9 B hG v (.inl p)*assemblyPairBoundaryRowΓ hM9 B hG p c) +
        assemblyCoeffΓ hM9 B hG v (.inr c) := by
  let β := sourceBoundaryBasis (G.sign a.toNode) c
  have he := congrArg (fun f : Fin 1 → ℤ => f 0)
    (assembly_boundary_predecessor_applyΓ hM9 B hG β (sourceBoundaryBasis_conservation _ c) v)
  have hb (u : (assemblyShapeΓ hM9 B).VIdx) :
      ((∑ j, assemblyBranchBoundaryRowΓ hM9 B u j • β j) : Fin 1 → ℤ) 0 = assemblyBranchBoundaryRowΓ hM9 B u c :=
    sourceBoundaryBasis_eval _ c _ (assemblyBranchBoundaryRow_zeroΓ hM9 B u)
  have hp (u : (assemblyShapeΓ hM9 B).VIdx) :
      ((∑ j, assemblyPairBoundaryRowΓ hM9 B hG u j • β j) : Fin 1 → ℤ) 0 = assemblyPairBoundaryRowΓ hM9 B hG u c :=
    sourceBoundaryBasis_eval _ c _ (assemblyPairBoundaryRow_zeroΓ hM9 B hG u)
  have hs : ((∑ j, assemblyCoeffΓ hM9 B hG v (.inr j) • β j) : Fin 1 → ℤ) 0 = assemblyCoeffΓ hM9 B hG v (.inr c) :=
    sourceBoundaryBasis_eval _ c _ (assemblyCoeff_upper_zeroΓ hM9 B hG v)
  have hprev : ((assemblyPrevΓ hM9 B v).elim (0 : Fin 1 → ℤ)
      (fun u => ∑ j, assemblyBranchBoundaryRowΓ hM9 B u j • β j)) 0 =
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => assemblyBranchBoundaryRowΓ hM9 B u c) := by
    cases assemblyPrevΓ hM9 B v with
    | none => rfl
    | some u => exact hb u
  simpa only [Pi.sub_apply,Pi.add_apply,hb,hp,hs,hprev,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he

end WaveTurbulence.GammaLow.Famb.VineEstS2
