/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates

/-! # Full-chain affine decoding commutes with the physical lattice embedding -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Every reconstructed source bond is exactly the uniform real chart
bond, including the common physical coset shift. -/
theorem clChainCoordinateEquiv_physical_bond {L : ℝ} (hL : L ≠ 0)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (e : Bond G.molecule U) :
    base+latticePoint L (clLocalBondLabels R L base (fun j => base+latticePoint L (β j))
      ((clChainCoordinateEquiv hL B base β hβ hM9).symm x) e) =
      ((chainFlowChart hM9 B (base+latticePoint L (β 2)) (latticePoint L (β 2-β 3))).symm
        (fun i => latticePoint L (x (assemblyVectorEquiv hM9 B i)))).1 e := by
  let f := latticePointAddHom (d := d) L
  calc
    _ = base+f (β 2+(∑ i, chainDecodeFree hM9 B e i • x (assemblyVectorEquiv hM9 B i))+
        chainDecodeGap hM9 B e • (β 2-β 3)) :=
      congrArg (fun z => base+f z) (clChainCoordinateEquiv_bond hL B base β hβ hM9 x e)
    _ = (base+f (β 2))+(∑ i, chainDecodeFree hM9 B e i • f (x (assemblyVectorEquiv hM9 B i)))+
        chainDecodeGap hM9 B e • f (β 2-β 3) := by
      rw [map_add,map_add,map_sum,map_zsmul]
      simp only [map_zsmul]
      abel
    _ = _ := (chainFlowChart_decode hM9 B (base+f (β 2)) (f (β 2-β 3))
      (fun i => f (x (assemblyVectorEquiv hM9 B i))) e).symm

end WaveTurbulence.VineEstS2
