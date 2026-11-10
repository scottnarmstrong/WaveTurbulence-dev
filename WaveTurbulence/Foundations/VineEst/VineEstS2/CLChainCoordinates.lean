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

/-! # Actual regional lattice reparametrization into frozen sumint slots -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The source local-decoration carrier is bijective with exactly the
frozen sumint vector lattice of the actual full chain. -/
noncomputable def clChainCoordinateEquiv {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM) :
    CLLocalDecoration R L base (fun j => base+latticePoint L (β j)) ≃
      ((assemblyShape hM9 B).VIdx → (Fin d → ℤ)) :=
  (clLocalFlowEquiv hL B.isBlock R base β hβ).trans
    ((chainFlowChart hM9 B (β 2) (β 2-β 3)).trans
      (Equiv.arrowCongr (assemblyVectorEquiv hM9 B) (Equiv.refl _)))

/-- Literal outgoing bond reconstruction after the full-chain lattice
change of variables, with the previously proved unit integer matrix. -/
theorem clChainCoordinateEquiv_bond {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (e : Bond G.molecule U) :
    clLocalBondLabels R L base (fun j => base+latticePoint L (β j))
      ((clChainCoordinateEquiv hL B base β hβ hM9).symm x) e =
      β 2 + (∑ i, chainDecodeFree hM9 B e i • x (assemblyVectorEquiv hM9 B i)) +
        chainDecodeGap hM9 B e • (β 2-β 3) := by
  have hl := clLocalFromFlow_bondLabels B.isBlock R L base β hβ
    ((chainFlowChart hM9 B (β 2) (β 2-β 3)).symm (fun i => x (assemblyVectorEquiv hM9 B i)))
  exact (congrArg (fun k : Bond G.molecule U → (Fin d → ℤ) => k e) hl).trans
    (chainFlowChart_decode hM9 B (β 2) (β 2-β 3) _ e)

end WaveTurbulence.VineEstS2
