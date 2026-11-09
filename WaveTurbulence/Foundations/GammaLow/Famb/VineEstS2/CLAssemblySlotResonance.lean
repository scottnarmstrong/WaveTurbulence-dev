/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPhysicalResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySlotResonance
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPhysicalResonance
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblySlotResonance` (sha256 2d2a1d12a4a655a8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Slotwise source resonance on the physical decoration, in chart coordinates

Every actual interior atom's signed source resonance is the node resonance of
its ingredient chart, at the slice of the physical chain coordinates and some
inherited anchor, with the common physical gap. -/

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
variable {L : ℝ} (hL : L ≠ 0) (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
  (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF)
  (xs : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))

theorem assembly_slot_resonanceΓ :
    ∃ gA : Fin n → Mom d, ∀ z : Σ i : Fin n, Fin (assemblyChartAtΓ hM9 B i).indexing.shape.n,
      (((G.sign ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1.toNode : ℤ) : ℝ) *
        omegaNode G (clChainMomentumΓ hL B base β hβ hM9 xs)
          ((assemblyChartAtΓ hM9 B z.1).indexing.atom z.2).1) =
      nodeResonance (assemblyChartAtΓ hM9 B z.1).indexing
        (((assemblyChartAtΓ hM9 B z.1).chart (gA z.1) (latticePoint L (β 2-β 3))).symm
          (fun j => latticePoint L (xs (assemblyVectorEquivΓ hM9 B
            ((assemblyInputEquivΓ hM9 B).symm ⟨z.1,j⟩))))).1 (gA z.1) (latticePoint L (β 2-β 3)) z.2 := by
  let g : Mom d := base+latticePoint L (β 2)
  let r : Mom d := latticePoint L (β 2-β 3)
  let k0 := (chainFlowChartΓ hM9 B g r).symm (fun i => latticePoint L (xs (assemblyVectorEquivΓ hM9 B i)))
  have hk : ∀ e, k0.1 e = Mole.restrictLabels G (clChainMomentumΓ hL B base β hβ hM9 xs) e.1 :=
    fun e => (clChainMomentum_bondΓ hL B base β hβ hM9 xs e).symm
  have hg : clChainMomentumΓ hL B base β hβ hM9 xs (b.child R.positive) = g :=
    clChainMomentum_boundaryΓ hL B base β hβ hM9 xs 2
  refine ⟨assemblyAnchorAtΓ B k0 g, fun z => ?_⟩
  have h := assembly_piece_resonanceΓ hM9 B k0 (clChainMomentumΓ hL B base β hβ hM9 xs)
    (clChainMomentum_conservationΓ hL B base β hβ hM9 xs) hk
    (clChainMomentum_matchingΓ hL B base β hβ hM9 xs) z.1 z.2
  rw [hg] at h
  rw [h, assembly_piece_flow_eq_chart_symmΓ hM9 B k0 g z.1]
  simp only [k0, Equiv.apply_symm_apply]
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS2
