/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyResonances
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieceCoordinates
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainPhysicalCoordinates
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLRegionalPhaseSlots
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPhysicalResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieceCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyResonances
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainPhysicalCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLRegionalPhaseSlots
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPhysicalResonance` (sha256 fc527229679aa044…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The signed source resonance at every slot of the physical chain decoration -/

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

/-- The physical momentum decoration of the regional lattice point with source
chain coordinates `xs`. -/
noncomputable def clChainMomentumΓ {L : ℝ} (hL : L ≠ 0) (B : CLChainAssemblyΓ γF G R n) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF)
    (xs : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) : GNode G.tree → Mom d :=
  cosetDecoration G L base (clExtendIndices R ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm xs).1)

variable {L : ℝ} (hL : L ≠ 0) (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
  (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF)
  (xs : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))

theorem clChainMomentum_conservationΓ (v : GBranch G.tree) (hv : v ∈ U) :
    clChainMomentumΓ hL B base β hβ hM9 xs v.toNode =
      clChainMomentumΓ hL B base β hβ hM9 xs (v.child 0) -
        clChainMomentumΓ hL B base β hβ hM9 xs (v.child 1) +
        clChainMomentumΓ hL B base β hβ hM9 xs (v.child 2) := by
  have h := ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm xs).2.1 v hv
  unfold clChainMomentumΓ cosetDecoration
  rw [h]
  simp only [latticePoint_add, latticePoint_sub]
  abel

theorem clChainMomentum_matchingΓ (ℓ : GLeaf G.tree) (hℓ : Mole.IsInternalLeaf G U ℓ) :
    clChainMomentumΓ hL B base β hβ hM9 xs ℓ.toNode =
      clChainMomentumΓ hL B base β hβ hM9 xs (G.pair ℓ).toNode := by
  unfold clChainMomentumΓ cosetDecoration
  exact congrArg (fun z => base+latticePoint L z)
    (((clChainCoordinateEquivΓ hL B base β hβ hM9).symm xs).2.2.1 ℓ hℓ)

theorem clChainMomentum_boundaryΓ (j : Fin 4) :
    clChainMomentumΓ hL B base β hβ hM9 xs (clBoundaryNodes R j) = base+latticePoint L (β j) := by
  unfold clChainMomentumΓ cosetDecoration
  exact ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm xs).2.2.2 j

theorem clChainMomentum_bondΓ (e : Bond G.molecule U) :
    Mole.restrictLabels G (clChainMomentumΓ hL B base β hβ hM9 xs) e.1 =
      ((chainFlowChartΓ hM9 B (base+latticePoint L (β 2)) (latticePoint L (β 2-β 3))).symm
        (fun i => latticePoint L (xs (assemblyVectorEquivΓ hM9 B i)))).1 e :=
  clChainCoordinateEquiv_physical_bondΓ hL hM9 B base β hβ xs e

end WaveTurbulence.GammaLow.Famb.VineEstS2
