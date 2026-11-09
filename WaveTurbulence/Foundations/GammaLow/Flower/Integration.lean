/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Assembly
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Final

/-! # FLOWER-LOW (packet L8): the integration at the level of item I's interface

Item I splits at main's B3s/B4 boundary (`Stage1MK/CONVENTIONS.md`, `status/L8-split.txt`):
* **B3s** — `MarkedClassRepresentsGateLow 452 cθ` (`Stage1MK/Iface.lean`), proved by the helper I-SLOTSI as
  `markedClassRepresentsMK_prefixLow` (main `MkSlotsI.Final.markedClassRepresentsMK_prefix`);
* **B4** — main's `Stage1MKGate.stage1ReductionAtMKFull_of_B3s` over `𝒱_γ`: from B3s, the marked Stage-1′ gate
  `Stage1MKGateLow C₀ cP cθ` for some `C₀ ≥ 2`. Stated here as `Stage1B4Low`; L8 ports its proof (I-GATE) once the
  remaining inputs are published (L5c's Geometry R83 and marked class-count legs, L6-H's `AsmVN13`/`SubproGap2`/
  `SubproObjMap`, L5a's `RepCountA`).

`flowerest1_low_of_B3s` is FL-low from L5a's Stage-1 gate, B4, B3s and the marked count H2; H2 is proved
(L8-H2: `H2.finalCountAtMKLAt_holds`), so `flowerest1_low_of_items6` / `flowerest1_low_of_B4` need only L5a's gate
and item I. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **B4 over `𝒱_γ`** (main's `Stage1MKGate.stage1ReductionAtMKFull_of_B3s`, the reduction of the marked Stage 1′ to
the class representation B3s): for all `cP cθ`, B3s gives the marked Stage-1′ gate for some `C₀ ≥ 2`. -/
def Stage1B4Low : Prop :=
  ∀ cP cθ : ℝ, MarkedClassRepresentsGateLow cP cθ → ∃ C₀ : ℕ, 2 ≤ C₀ ∧ Stage1MKGateLow C₀ cP cθ

/-- **FL-low from item I's interface**: L5a's Stage-1 gate, B4 (`Stage1B4Low`), B3s at `cP = 452`
(I-SLOTSI's `markedClassRepresentsMK_prefixLow`), and the marked count H2. -/
theorem flowerest1_low_of_B3s {cθ : ℝ} (hcθ : 1 ≤ cθ) (h5a : Fama.Stage1ReductionGateLow) (hB4 : Stage1B4Low)
    (hB3s : MarkedClassRepresentsGateLow 452 cθ)
    (hH2 : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P) : LayergardenFlowerLowGate := by
  obtain ⟨C₀, hC₀, hI⟩ := hB4 452 cθ hB3s
  exact flowerest1_low_of_items5 (by omega) hcθ h5a hI hH2

/-- **FL-low with H2 discharged** (L8-H2's `H2.finalCountAtMKLAt_holds`): from L5a's Stage-1 gate and item I. -/
theorem flowerest1_low_of_items6 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (h5a : Fama.Stage1ReductionGateLow) (hI : Stage1MKGateLow C₀ 452 cθ) : LayergardenFlowerLowGate :=
  flowerest1_low_of_items5 hC₀ hcθ h5a hI H2.finalCountAtMKLAt_holds

/-- **FL-low from item I's interface, H2 discharged**: L5a's Stage-1 gate, B4 and B3s. -/
theorem flowerest1_low_of_B4 {cθ : ℝ} (hcθ : 1 ≤ cθ) (h5a : Fama.Stage1ReductionGateLow) (hB4 : Stage1B4Low)
    (hB3s : MarkedClassRepresentsGateLow 452 cθ) : LayergardenFlowerLowGate :=
  flowerest1_low_of_B3s hcθ h5a hB4 hB3s H2.finalCountAtMKLAt_holds

end WaveTurbulence.GammaLow.Flower
