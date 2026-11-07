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

/-! # The signed source resonance at every slot of the physical chain decoration -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The physical momentum decoration of the regional lattice point with source
chain coordinates `xs`. -/
noncomputable def clChainMomentum {L : ℝ} (hL : L ≠ 0) (B : CLChainAssembly G R n) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM)
    (xs : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) : GNode G.tree → Mom d :=
  cosetDecoration G L base (clExtendIndices R ((clChainCoordinateEquiv hL B base β hβ hM9).symm xs).1)

variable {L : ℝ} (hL : L ≠ 0) (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
  (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM)
  (xs : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))

theorem clChainMomentum_conservation (v : GBranch G.tree) (hv : v ∈ U) :
    clChainMomentum hL B base β hβ hM9 xs v.toNode =
      clChainMomentum hL B base β hβ hM9 xs (v.child 0) -
        clChainMomentum hL B base β hβ hM9 xs (v.child 1) +
        clChainMomentum hL B base β hβ hM9 xs (v.child 2) := by
  have h := ((clChainCoordinateEquiv hL B base β hβ hM9).symm xs).2.1 v hv
  unfold clChainMomentum cosetDecoration
  rw [h]
  simp only [latticePoint_add, latticePoint_sub]
  abel

theorem clChainMomentum_matching (ℓ : GLeaf G.tree) (hℓ : Mole.IsInternalLeaf G U ℓ) :
    clChainMomentum hL B base β hβ hM9 xs ℓ.toNode =
      clChainMomentum hL B base β hβ hM9 xs (G.pair ℓ).toNode := by
  unfold clChainMomentum cosetDecoration
  exact congrArg (fun z => base+latticePoint L z)
    (((clChainCoordinateEquiv hL B base β hβ hM9).symm xs).2.2.1 ℓ hℓ)

theorem clChainMomentum_boundary (j : Fin 4) :
    clChainMomentum hL B base β hβ hM9 xs (clBoundaryNodes R j) = base+latticePoint L (β j) := by
  unfold clChainMomentum cosetDecoration
  exact ((clChainCoordinateEquiv hL B base β hβ hM9).symm xs).2.2.2 j

theorem clChainMomentum_bond (e : Bond G.molecule U) :
    Mole.restrictLabels G (clChainMomentum hL B base β hβ hM9 xs) e.1 =
      ((chainFlowChart hM9 B (base+latticePoint L (β 2)) (latticePoint L (β 2-β 3))).symm
        (fun i => latticePoint L (xs (assemblyVectorEquiv hM9 B i)))).1 e :=
  clChainCoordinateEquiv_physical_bond hL hM9 B base β hβ xs e

end WaveTurbulence.VineEstS2
