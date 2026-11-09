/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyInputEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyInputEquations` (sha256 172186817c509876…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Literal block index equations for the source-chain coordinate change -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

 theorem assemblyInputEquiv_single_symmΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hV : FinalCount.Src.IsSomeVine γF G.molecule U a b) (R : CLRegionData G U a b) (i : Fin 1)
    (j : Fin (assemblyChartAtΓ hM9 (.single hV R) i).indexing.shape.n) :
    (assemblyInputEquivΓ hM9 (.single hV R)).symm ⟨i,j⟩ = j := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
variable {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssemblyΓ γF G RP n)
variable (hT : FinalCount.Src.IsSomeVine γF G.molecule T b c) (hi : S ∩ T = {b})
variable (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)

theorem assemblyInputEquiv_append_zero_symmΓ (hM9 : NormalChartSupply γF)
    (j : Fin (assemblyChartAtΓ hM9 (.append B hT hi hU R) 0).indexing.shape.n) :
    (assemblyInputEquivΓ hM9 (.append B hT hi hU R)).symm ⟨0,j⟩ = .inl j := rfl

end WaveTurbulence.GammaLow.Famb.VineEstS2
