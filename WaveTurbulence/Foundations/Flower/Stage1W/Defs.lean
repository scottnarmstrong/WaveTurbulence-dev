/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FlowerTop.FinalFamily
public import WaveTurbulence.Foundations.VineEst.V5Proof
public import WaveTurbulence.Foundations.VineEst.RowSel.Vocab

/-! # STAGE1W-GLUE: Defs (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 1. Weight vocabulary

`topPsi`, `rowParentLayer`, `rowTopWeight`, `kernelLeavesW`, `coupleLeavesTop`, `treeLeavesTop` are now on main
(416902c8, V5W-B: `VineEst/RowSel/Vocab.lean`, the same text in this namespace), imported above. -/

/-- `J`-th moment mass of a Fourier presentation on `Mom d` (root derivatives of `g (k + ·)` cost it). -/
def momentMassMom {d : ℕ} {α : Type*} [MeasurableSpace α] (J : ℕ) (M : Cut2A.SpatialMeasure (Mom d) α) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ

/-- `g` has a Fourier presentation whose `J`-th moment mass is at most `c`. -/
def GPresented {d : ℕ} (J : ℕ) (g : Mom d → ℂ) (c : ℝ) : Prop :=
  ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
    momentMassMom J M ≤ ENNReal.ofReal c ∧ ∀ x, M.value x = g x

/-- The node product of a three-label weight over the nonroot nodes (FC23's `nodeLabelProduct`, verbatim). -/
def nodeLabelProduct {w : ℕ} {E M : Type*} [CommMonoid M] (ψ : Fin w → ℕ → ℕ → E → M)
    (LG : LayeredGarden w) (p : ℕ) (k : GNode LG.garden.tree → E) : M :=
  ∏ a : GNode LG.garden.tree,
    if a.1.2 ≠ [] then ψ a.1.1 (LG.layer a) (LG.parentLayer p a) (k a) else 1

/-! ## 2. The frontier weight and the weighted `Represents` (new, minimal) -/

/-! ## 3. The gate -/


end WaveTurbulence.Flower.Stage1W
