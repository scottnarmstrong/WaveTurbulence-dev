/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape` (sha256 8c4267a5f2cd80a6…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact frozen sumint shape of an actual CL vine chain -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyShapeΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) : SumintShape :=
  shapeFamily (fun i => (assemblyPieceAtΓ B i).label) (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape)

/-- Exact block-preserving map to frozen vector slots. -/
noncomputable def assemblyVectorEquivΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    chainInputIndexΓ hM9 B ≃ (assemblyShapeΓ hM9 B).VIdx :=
  (assemblyInputEquivΓ hM9 B).trans (Equiv.sigmaCongrRight
    (familySlotEquiv (fun i => (assemblyPieceAtΓ B i).label)
      (fun i => (assemblyChartAtΓ hM9 B i).indexing.shape)))

noncomputable def assemblyTimeEquivΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    (assemblyShapeΓ hM9 B).TVar ≃ chainInputIndexΓ hM9 B :=
  (Sumint.timeVectorEquiv _).trans (assemblyVectorEquivΓ hM9 B).symm

theorem assemblyShape_MΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    (assemblyShapeΓ hM9 B).M = clLocalOrder1 R :=
  (Sumint.card_vector_index _).symm.trans
    ((Fintype.card_congr (assemblyVectorEquivΓ hM9 B)).symm.trans (card_chainInputIndexΓ hM9 B))

theorem assemblyShape_I_posΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    0 < (assemblyShapeΓ hM9 B).I := B.length_pos

end WaveTurbulence.GammaLow.Famb.VineEstS2
