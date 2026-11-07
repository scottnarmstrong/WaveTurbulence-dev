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

/-! # The actual bottom-to-top vine family of a chain assembly -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Actual source ingredients, with the terminal vine first. -/
noncomputable def assemblyPieceAt
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : Fin n → ChainPiece G.molecule :=
  match B with
  | .single hV _ => fun _ => ⟨_,_,_,_,hV⟩
  | .append B hT _ _ _ => Fin.cases ⟨_,_,_,_,hT⟩ (assemblyPieceAt B)

noncomputable def assemblyChartAt (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i : Fin n) :=
  chainPieceChart hM9 (Mole.garden_isMolecule G) (assemblyPieceAt B i)

/-- The recursively glued chart indices are exactly the dependent family
of M9 slots; no arbitrary cardinality bijection is used. -/
noncomputable def assemblyInputEquiv (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) :
    chainInputIndex hM9 B ≃ (Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n) := by
  induction B with
  | single hV R =>
    exact (Equiv.uniqueSigma (fun i : Fin 1 => Fin (assemblyChartAt hM9 (.single hV R) i).indexing.shape.n)).symm
  | append B hT hi hU R ih =>
    exact (Equiv.sumCongr (Equiv.refl _) ih).trans (sigmaFinSuccEquiv (fun i => Fin (assemblyChartAt hM9 (.append B hT hi hU R) i).indexing.shape.n)).symm

end WaveTurbulence.VineEstS2
