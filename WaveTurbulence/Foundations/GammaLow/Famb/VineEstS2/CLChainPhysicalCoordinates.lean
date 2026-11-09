/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainPhysicalCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainCoordinates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainPhysicalCoordinates` (sha256 5f474ef31cbb508c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Full-chain affine decoding commutes with the physical lattice embedding -/

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

/-- Every reconstructed source bond is exactly the uniform real chart
bond, including the common physical coset shift. -/
theorem clChainCoordinateEquiv_physical_bondΓ {L : ℝ} (hL : L ≠ 0)
    (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (e : Bond G.molecule U) :
    base+latticePoint L (clLocalBondLabels R L base (fun j => base+latticePoint L (β j))
      ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm x) e) =
      ((chainFlowChartΓ hM9 B (base+latticePoint L (β 2)) (latticePoint L (β 2-β 3))).symm
        (fun i => latticePoint L (x (assemblyVectorEquivΓ hM9 B i)))).1 e := by
  let f := latticePointAddHom (d := d) L
  calc
    _ = base+f (β 2+(∑ i, chainDecodeFreeΓ hM9 B e i • x (assemblyVectorEquivΓ hM9 B i))+
        chainDecodeGapΓ hM9 B e • (β 2-β 3)) :=
      congrArg (fun z => base+f z) (clChainCoordinateEquiv_bondΓ hL B base β hβ hM9 x e)
    _ = (base+f (β 2))+(∑ i, chainDecodeFreeΓ hM9 B e i • f (x (assemblyVectorEquivΓ hM9 B i)))+
        chainDecodeGapΓ hM9 B e • f (β 2-β 3) := by
      rw [map_add,map_add,map_sum,map_zsmul]
      simp only [map_zsmul]
      abel
    _ = _ := (chainFlowChart_decodeΓ hM9 B (base+f (β 2)) (f (β 2-β 3))
      (fun i => f (x (assemblyVectorEquivΓ hM9 B i))) e).symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
