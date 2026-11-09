/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.B4
public import WaveTurbulence.Foundations.GammaLow.Fama.Final

/-! # FLOWER-LOW (packet L8): FL-low

**`flowerest1_low : LayergardenFlowerLowGate`**: the low half (`P.γ ≤ 1 / 2`) of the anchor `layergardenFlower_v4`,
with no hypotheses. `flowerest1_low_of_items6` (`Integration.lean`; H2 discharged by L8-H2's
`H2.finalCountAtMKLAt_holds`, L6's gate, the T-vine and chart inputs, H1, I3 and D inside) from
* L5a's Stage-1 reduction gate `Fama.stage1ReductionGateLow` (`Fama/Final.lean`, L5a READY), and
* item I, the marked Stage-1′ gate `stage1MKGateLow : Stage1MKGateLow C₀L 452 cθL` (`Stage1MK/B4.lean`).

`Exact.lean` checks that `wtPrefixP_of_halves layergardenFlower_v3 flowerest1_low` has the type of the anchor. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **FL-low** (the low half of `layergardenFlower_v4`), unconditional. -/
theorem flowerest1_low : LayergardenFlowerLowGate :=
  flowerest1_low_of_items6 one_le_C₀L one_le_cθL Fama.stage1ReductionGateLow stage1MKGateLow

end WaveTurbulence.GammaLow.Flower
