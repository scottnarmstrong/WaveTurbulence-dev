/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPhysicalResonance

/-! # Slotwise source resonance on the physical decoration, in chart coordinates

Every actual interior atom's signed source resonance is the node resonance of
its ingredient chart, at the slice of the physical chain coordinates and some
inherited anchor, with the common physical gap. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {L : ℝ} (hL : L ≠ 0) (B : CLChainAssembly G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
  (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : VINEPARAM)
  (xs : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))

theorem assembly_slot_resonance :
    ∃ gA : Fin n → Mom d, ∀ z : Σ i : Fin n, Fin (assemblyChartAt hM9 B i).indexing.shape.n,
      (((G.sign ((assemblyChartAt hM9 B z.1).indexing.atom z.2).1.toNode : ℤ) : ℝ) *
        omegaNode G (clChainMomentum hL B base β hβ hM9 xs)
          ((assemblyChartAt hM9 B z.1).indexing.atom z.2).1) =
      nodeResonance (assemblyChartAt hM9 B z.1).indexing
        (((assemblyChartAt hM9 B z.1).chart (gA z.1) (latticePoint L (β 2-β 3))).symm
          (fun j => latticePoint L (xs (assemblyVectorEquiv hM9 B
            ((assemblyInputEquiv hM9 B).symm ⟨z.1,j⟩))))).1 (gA z.1) (latticePoint L (β 2-β 3)) z.2 := by
  let g : Mom d := base+latticePoint L (β 2)
  let r : Mom d := latticePoint L (β 2-β 3)
  let k0 := (chainFlowChart hM9 B g r).symm (fun i => latticePoint L (xs (assemblyVectorEquiv hM9 B i)))
  have hk : ∀ e, k0.1 e = Mole.restrictLabels G (clChainMomentum hL B base β hβ hM9 xs) e.1 :=
    fun e => (clChainMomentum_bond hL B base β hβ hM9 xs e).symm
  have hg : clChainMomentum hL B base β hβ hM9 xs (b.child R.positive) = g :=
    clChainMomentum_boundary hL B base β hβ hM9 xs 2
  refine ⟨assemblyAnchorAt B k0 g, fun z => ?_⟩
  have h := assembly_piece_resonance hM9 B k0 (clChainMomentum hL B base β hβ hM9 xs)
    (clChainMomentum_conservation hL B base β hβ hM9 xs) hk
    (clChainMomentum_matching hL B base β hβ hM9 xs) z.1 z.2
  rw [hg] at h
  rw [h, assembly_piece_flow_eq_chart_symm hM9 B k0 g z.1]
  simp only [k0, Equiv.apply_symm_apply]
  rfl

end WaveTurbulence.VineEstS2
