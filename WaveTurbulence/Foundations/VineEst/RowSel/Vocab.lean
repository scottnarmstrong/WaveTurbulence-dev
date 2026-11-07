/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer

/-! # V5W-B (ruling F2): the top-weighted row kernels, copied by source

The six weight-vocabulary definitions `topPsi`, `rowParentLayer`, `rowTopWeight`, `kernelLeavesW`, `coupleLeavesTop`,
`treeLeavesTop` are copied verbatim (text and namespace `WaveTurbulence.Flower.Stage1W` unchanged) from the flower world's
`Flower/Stage1W/Defs.lean` (sha256 `51764162a5eb0337bfaa91f999710cc0fa7e10461eae652e9cdc802cfaae8b22`, lines 16–48),
the vocabulary V5W-0's pinned kernel form imports.  They live below the V5 tower so that the row selector `RowSel`
(`VineEst/RowSel/Basic.lean`) can read them; the world's copies are retired against these when V5W-B lands.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 1. Verbatim weight vocabulary (S2-ST `TopRows`, FC23 `nodeLabelProduct`) -/

/-- FC23's lower-layer-blind top label weight: `g` on top labels (child layer `< p`, parent layer `= p`), else `1`. -/
def topPsi {d : ℕ} (p : ℕ) (g : Mom d → ℂ) : ℕ → ℕ → Mom d → ℂ :=
  fun q q' r => if q < p ∧ q' = p then g r else 1

/-- The parent layer of a node of a standalone layered regular object; the root `i` reads `qr i`. -/
def rowParentLayer {w : ℕ} (LG : LayeredGarden w) (qr : Fin w → ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 = [] then qr a.1.1 else LG.parentLayer 0 a

/-- The top weight of a regular object: `∏_a topPsi p g (layer a) (parent layer a) (k a)`. -/
def rowTopWeight {w d : ℕ} (p : ℕ) (g : Mom d → ℂ) (LG : LayeredGarden w) (qr : Fin w → ℕ)
    (k : GNode LG.garden.tree → Mom d) : ℂ :=
  ∏ a : GNode LG.garden.tree, topPsi p g (LG.layer a) (rowParentLayer LG qr a) (k a)

/-- Leafwise `kernelLeaves` with a multiplier of the actual node momenta. -/
def kernelLeavesW (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

def coupleLeavesTop (L γ δ : ℝ) {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 (rowTopWeight p g LG ![q, q'])

def treeLeavesTop (L γ δ : ℝ) {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (q : ℕ) (LG : LayeredGarden 1)
    (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 (rowTopWeight p g LG ![q])

end WaveTurbulence.Flower.Stage1W
