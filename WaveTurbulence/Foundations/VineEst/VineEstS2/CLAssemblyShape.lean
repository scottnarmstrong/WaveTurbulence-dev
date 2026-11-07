/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces

/-! # Exact frozen sumint shape of an actual CL vine chain -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyShape (hM9 : VINEPARAM) (B : CLChainAssembly G R n) : SumintShape :=
  shapeFamily (fun i => (assemblyPieceAt B i).vineType) (fun i => (assemblyChartAt hM9 B i).indexing.shape)

/-- Exact block-preserving map to frozen vector slots. -/
noncomputable def assemblyVectorEquiv (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    chainInputIndex hM9 B ≃ (assemblyShape hM9 B).VIdx :=
  (assemblyInputEquiv hM9 B).trans (Equiv.sigmaCongrRight
    (familySlotEquiv (fun i => (assemblyPieceAt B i).vineType)
      (fun i => (assemblyChartAt hM9 B i).indexing.shape)))

noncomputable def assemblyTimeEquiv (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    (assemblyShape hM9 B).TVar ≃ chainInputIndex hM9 B :=
  (Sumint.timeVectorEquiv _).trans (assemblyVectorEquiv hM9 B).symm

theorem assemblyShape_M (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    (assemblyShape hM9 B).M = clLocalOrder1 R :=
  (Sumint.card_vector_index _).symm.trans
    ((Fintype.card_congr (assemblyVectorEquiv hM9 B)).symm.trans (card_chainInputIndex hM9 B))

theorem assemblyShape_I_pos (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    0 < (assemblyShape hM9 B).I := B.length_pos

end WaveTurbulence.VineEstS2
