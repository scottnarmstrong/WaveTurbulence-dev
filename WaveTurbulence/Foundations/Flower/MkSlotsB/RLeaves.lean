/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RRedW
public import WaveTurbulence.Foundations.Flower.MkSlots.PRedLeaves
public import WaveTurbulence.Foundations.Flower.MkSlots.Slice
public import WaveTurbulence.Foundations.Flower.MkSlots.Bridge

/-! # B3s-HELPER3 (B1): the relaxed pinned leafwise skeleton reduction with general factorized weights

The twin of `MkSlotsW.kernelLeaves_skeleton_reduction_selNWFM` (`MkSlotsW/PRedM.lean`) on RELAXED domains:

* the left-hand side `kernelLeavesSelNWFMR` integrates on main's relaxed `kDomainFix` of the pins `fixG`; for EVERY
  `fixG` it is the Bridge form `MkSlots.kernelLeavesFixSelW` (main's `FlowerP1.kernelLeavesFixTerm`):
  `kernelLeavesSelNWFMR_eq`;
* the core domain is relaxed by `fixCore D hS fixG` (`coreTimeDomainWR`), each slot function by `fixNative D hS fixG s`
  including the slot-top/clock constraint (`slotFnGWFR`, domain `kDomainR` with the clock pin status `clockFree`);
* the weight is `(∏ z, W z (k z)) · Θ (collapse κ) · ∏ s, Θs s k_s (restrictRelativeDecorations κ s)`, with
  `k_s = slotMom` the slot momentum; `Θs s` enters `slotFnGWFR s` inside its `kernelNodeWR` weight.
Hypothesis on the pins: `RelaxPins layer tt fixG` (pins in `(layer, layer + 1]`, `≤ tt`, monotone along ancestry;
necessary, see `RDom`). Main theorem: **`kernelLeaves_skeleton_reduction_selNWFMR`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots WaveTurbulence.LGSpine

/-! ### The relaxed pinned leaf kernel -/

/-- **The relaxed pinned decoration-restricted leaf kernel with a momentum weight `m` and a decoration weight `Θg`**:
`MkSlotsW.kernelLeavesSelNWFM` with main's relaxed domain `kDomainFix LG up fix`. -/
def kernelLeavesSelNWFMR {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then Θg κ * (m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, (kDomainFix LG up fix).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
            ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)))
      else 0

/-- **The left-hand side is the Bridge form** (main's `FlowerP1.kernelLeavesFixTerm` on `kDomainFix`), for EVERY pin
function. -/
theorem kernelLeavesSelNWFMR_eq {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m Θg fix =
      kernelLeavesFixSelW L γ δ LG H up fix k₀ nroot nfl sel
        (fun κ => Θg κ * m (cosetDecoration LG.garden L k₀ κ.1)) := by
  unfold kernelLeavesSelNWFMR kernelLeavesFixSelW FlowerP1.kernelLeavesFixTerm
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs
  · have hI : (∫ τ, (kDomainFix LG up fix).indicator (phaseProd L γ δ LG.garden
          (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix)) =
        ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ, (kDomainFix LG up fix).indicator
          (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ) := by
      rw [integral_fixMeasure]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      dsimp only
      rw [extendFix_eq_extendFixI]
    rw [hI]
    ring
  · rfl

theorem kernelLeavesSelNWFMR_eq_integral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg Θn : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m (fun κ => Θg κ * Θn κ) fix =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, if sel κ then
          Θg κ * ∫ τ, kernelAllIntegrandNWD L γ δ LG (fun a => H a.1) m (kDomainFix LG up fix) k₀ Θn κ τ
            ∂(fixMeasure fix) else 0 := by
  unfold kernelLeavesSelNWFMR
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases h : sel κ
  · simp only [h, ite_true]
    rw [integral_kernelAllIntegrandNWD_fix L γ δ LG (fun a => H a.1) m (kDomainFix LG up fix) k₀ Θn κ fix]
    show Θg κ * Θn κ * (m _ * (_ * _ *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))) =
      Θg κ * (m _ * Θn κ * (_ * _ *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)))
    ring
  · simp only [h, ite_false]

/-! ### The relaxed slot functions -/

/-! ### The relaxed reduction -/

end WaveTurbulence.Flower.MkSlotsB
