/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainDifferences
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceTags
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates

/-! # Full-chain coordinate differences use only independent lower boundary tags -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Both source tags are selected from geometry once and for all. The
identity holds on every actual local-decoration lattice parametrization. -/
theorem clChainCoordinate_chartTag_difference (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (i : (assemblyShape hM9 B).VIdx) :
    ∃ p q : CLChartSourceTag R,
      ∀ {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
        (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
        (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)),
        let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
        x i = clSourceOriginValue B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (clExtendIndices R κ.1) (chartSourceTag R p) -
          clSourceOriginValue B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (clExtendIndices R κ.1) (chartSourceTag R q) := by
  obtain ⟨p,q,hpq⟩ := chainFlowChart_difference hM9 B ((assemblyVectorEquiv hM9 B).symm i)
  obtain ⟨p',hp⟩ := clOrigin_chartSourceTag B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) p
  obtain ⟨q',hq⟩ := clOrigin_chartSourceTag B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) q
  refine ⟨p',q',?_⟩
  intro d L hL base β hβ x
  let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
  let k := (chainFlowChart hM9 B (β 2) (β 2-β 3)).symm (fun j => x (assemblyVectorEquiv hM9 B j))
  have hlabels : clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ = k.1 :=
    clLocalFromFlow_bondLabels B.isBlock R L base β hβ k
  have hbound (c : Fin 4) : clExtendIndices R κ.1 (clBoundaryNodes R c) = β c :=
    latticePoint_injective_of_ne_zero hL (add_left_cancel (κ.2.2.2 c))
  have hd := hpq (β 2) (β 2-β 3) k
  have hchart : chainFlowChart hM9 B (β 2) (β 2-β 3) k = fun j => x (assemblyVectorEquiv hM9 B j) :=
    (chainFlowChart hM9 B (β 2) (β 2-β 3)).apply_symm_apply _
  rw [hchart] at hd
  have hd' : x i = origin G.molecule U k.1 (β 2) (β 2-β 3) p -
      origin G.molecule U k.1 (β 2) (β 2-β 3) q := by
    simpa only [Equiv.apply_symm_apply] using hd
  have hp' := hp (clExtendIndices R κ.1) κ.2.2.1
  have hq' := hq (clExtendIndices R κ.1) κ.2.2.1
  change origin G.molecule U (clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ)
    _ _ p = _ at hp'
  change origin G.molecule U (clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ)
    _ _ q = _ at hq'
  rw [hlabels,hbound,hbound] at hp' hq'
  exact hd'.trans (congrArg₂ (fun u v : Fin d → ℤ => u-v) hp' hq')

end WaveTurbulence.VineEstS2
