/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam

/-! # P4-W2 AUX (d''): the leaf-cost identity at the level of `Lvl` (`zp_leafCost_eq_lvl`, the form W2's exceptional rows use). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.W13

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {hprime : IsPrimeGarden G}

/-- **The leaf-cost identity at a level**: every member `bb` of the bundle of the operative member `pstar` of the level `lv`. -/
theorem zp_leafCost_eq_lvl (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (bb : ST w lv.ι pstar {j | (lv.e j).1.val < (lv.e pstar).1.val})
    (hb : bb ∈ zpFinset p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime) (B0 : ℝ) :
    layerCost (fun _ => B0) (zpObjC bb.1 pstar) * layerCost (fun _ => B0) (zpObjT bb.1 pstar) =
      layerCost (fun _ => B0) (nativeCoupleLayered RD hG layer hLayer
          (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement (lv.e pstar)).retained)) *
        layerCost (fun _ => B0) (nativeChainLayered RD hG layer hLayer
          ((startState B RD hG layer hLayer).family.placement (lv.e pstar)).lower) :=
  zp_leafCost_eq_native B RD hG layer hLayer (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent (lv.e pstar) (zpN_lvl B RD hG layer hLayer lv pstar) bb hb B0
end WaveTurbulence.VineEstS5C.P4.W2
