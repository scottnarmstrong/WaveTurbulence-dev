/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyIndex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainChartIndexing
public import WaveTurbulence.Foundations.VineEst.VineEstS2.FiniteBlockIndex
public import Mathlib.Logic.Equiv.Prod
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyIndex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainChartIndexing
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces` (sha256 00b64a4018e183ca…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The actual bottom-to-top vine family of a chain assembly -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Actual source ingredients, with the terminal vine first. -/
noncomputable def assemblyPieceAtΓ
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) : Fin n → ChainPieceΓ γF G.molecule :=
  match B with
  | .single hV _ => fun _ => ⟨_,_,_,hV⟩
  | .append B hT _ _ _ => Fin.cases ⟨_,_,_,hT⟩ (assemblyPieceAtΓ B)

noncomputable def assemblyChartAtΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (i : Fin n) :=
  chainPieceChartΓ hM9 (Mole.garden_isMolecule G) (assemblyPieceAtΓ B i)

/-- The recursively glued chart indices are exactly the dependent family
of M9 slots; no arbitrary cardinality bijection is used. -/
noncomputable def assemblyInputEquivΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) :
    chainInputIndexΓ hM9 B ≃ (Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n) := by
  induction B with
  | single hV R =>
    exact (Equiv.uniqueSigma (fun i : Fin 1 => Fin (assemblyChartAtΓ hM9 (.single hV R) i).indexing.shape.n)).symm
  | append B hT hi hU R ih =>
    exact (Equiv.sumCongr (Equiv.refl _) ih).trans (sigmaFinSuccEquiv (fun i => Fin (assemblyChartAtΓ hM9 (.append B hT hi hU R) i).indexing.shape.n)).symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
