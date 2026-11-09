/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtoms` (sha256 1326240e9971823b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Actual source atom and clock correspondence for the full-chain chart -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Every free slot indexes its original interior branch. At concatenation
the shared joint belongs to the prefix, exactly as in the source. -/
noncomputable def assemblyAtomEquivΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) : chainInputIndexΓ hM9 B ≃ ↥(U.erase a) := by
  induction B with
  | single hV R => exact (chosenVineChartΓ hM9 hV).indexing.atom
  | @append S T a b c n RP B hT hi hU R ih =>
    have hS := B.isBlock
    have hp := chainInterior_union S T a b hS.2.1 hS.2.2.1 hS.2.2.2.1 hi
    exact (Equiv.sumCongr (chosenVineChartΓ hM9 hT).indexing.atom ih).trans
      ((Equiv.sumComm _ _).trans ((Equiv.Finset.union _ _ (chainInterior_disjoint S T a b hi)).trans
        (Set.equivOfEq (congrArg (fun q : Finset (GBranch G.tree) => (q : Set (GBranch G.tree))) hp.symm))))

noncomputable def assemblyClockAtomEquivΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) : (assemblyShapeΓ hM9 B).TVar ≃ ↥(U.erase a) :=
  (assemblyTimeEquivΓ hM9 B).trans (assemblyAtomEquivΓ hM9 B)

end WaveTurbulence.GammaLow.Famb.VineEstS2
