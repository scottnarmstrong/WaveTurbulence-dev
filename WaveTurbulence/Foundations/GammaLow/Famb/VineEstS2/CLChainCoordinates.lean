/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyDecode
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLocalFlowEquiv
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyDecode
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates` (sha256 148aa5da9c20df51…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Actual regional lattice reparametrization into frozen sumint slots -/

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

/-- The source local-decoration carrier is bijective with exactly the
frozen sumint vector lattice of the actual full chain. -/
noncomputable def clChainCoordinateEquivΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF) :
    CLLocalDecoration R L base (fun j => base+latticePoint L (β j)) ≃
      ((assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) :=
  (clLocalFlowEquiv hL B.isBlock R base β hβ).trans
    ((chainFlowChartΓ hM9 B (β 2) (β 2-β 3)).trans
      (Equiv.arrowCongr (assemblyVectorEquivΓ hM9 B) (Equiv.refl _)))

/-- Literal outgoing bond reconstruction after the full-chain lattice
change of variables, with the previously proved unit integer matrix. -/
theorem clChainCoordinateEquiv_bondΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (e : Bond G.molecule U) :
    clLocalBondLabels R L base (fun j => base+latticePoint L (β j))
      ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm x) e =
      β 2 + (∑ i, chainDecodeFreeΓ hM9 B e i • x (assemblyVectorEquivΓ hM9 B i)) +
        chainDecodeGapΓ hM9 B e • (β 2-β 3) := by
  have hl := clLocalFromFlow_bondLabels B.isBlock R L base β hβ
    ((chainFlowChartΓ hM9 B (β 2) (β 2-β 3)).symm (fun i => x (assemblyVectorEquivΓ hM9 B i)))
  exact (congrArg (fun k : Bond G.molecule U → (Fin d → ℤ) => k e) hl).trans
    (chainFlowChart_decodeΓ hM9 B (β 2) (β 2-β 3) _ e)

end WaveTurbulence.GammaLow.Famb.VineEstS2
