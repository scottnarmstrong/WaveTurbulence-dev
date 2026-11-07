/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainLocalWitnesses
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLocalOriginCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates

/-! # Actual full-chain inverse rows have unit source coefficients -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The source inverse row is obtained by proved local incidence geometry
and actual leaf-pair cancellation. There is no inverse-unit premise. -/
theorem exists_chainInverseRow (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (i : chainInputIndex hM9 B) :
    ∃ σ : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ, (∀ o, IsUnitCoeff (σ o)) ∧
      ∀ {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
        (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
        (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)),
        let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
        x (assemblyVectorEquiv hM9 B i) = ∑ o, σ o • clOriginValue B.isBlock R hG (clExtendIndices R κ.1) o := by
  obtain ⟨p,q,⟨v,hv,out,hp,hq⟩,hpq⟩ := chainFlowChart_local_difference hM9 B i
  obtain ⟨σ,hσ,he⟩ := clLocalOrigin_difference_coeffs B.isBlock R hG p q v hv out hp hq
  refine ⟨σ,hσ,?_⟩
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
  have hsource := he (clExtendIndices R κ.1) κ.2.1 κ.2.2.1
  change origin G.molecule U (clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ)
    (clExtendIndices R κ.1 (clBoundaryNodes R 2))
    (clExtendIndices R κ.1 (clBoundaryNodes R 2)-clExtendIndices R κ.1 (clBoundaryNodes R 3)) p -
    origin G.molecule U (clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ)
    (clExtendIndices R κ.1 (clBoundaryNodes R 2))
    (clExtendIndices R κ.1 (clBoundaryNodes R 2)-clExtendIndices R κ.1 (clBoundaryNodes R 3)) q = _ at hsource
  rw [hlabels,hbound,hbound] at hsource
  exact hd.trans hsource

end WaveTurbulence.VineEstS2
