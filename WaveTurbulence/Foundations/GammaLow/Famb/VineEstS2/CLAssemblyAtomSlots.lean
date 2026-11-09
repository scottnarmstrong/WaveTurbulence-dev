/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyInputEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtomSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyInputEquations
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtomSlots` (sha256 4ef7e645a7229f22…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The global atom bijection restricts to each ingredient's own atom bijection -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

theorem assemblyAtomEquiv_inputΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (i : Fin n) (j : Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) :
    (assemblyAtomEquivΓ hM9 B ((assemblyInputEquivΓ hM9 B).symm ⟨i,j⟩)).1 =
      ((assemblyChartAtΓ hM9 B i).indexing.atom j).1 := by
  induction B with
  | single hV R =>
    rw [assemblyInputEquiv_single_symmΓ]
    rfl
  | append B hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [assemblyInputEquiv_append_zero_symmΓ]
      rfl
    · exact ih i j

end WaveTurbulence.GammaLow.Famb.VineEstS2
