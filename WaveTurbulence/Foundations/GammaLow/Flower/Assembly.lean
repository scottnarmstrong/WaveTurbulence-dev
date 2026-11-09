/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Top.Glue
public import WaveTurbulence.Foundations.GammaLow.Flower.Nonreg.Assembly
public import WaveTurbulence.Foundations.GammaLow.Flower.SelSum.Core
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.Fine
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.LowL
public import WaveTurbulence.Foundations.GammaLow.LGLow.CC3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.I.Final
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainLowL

/-! # FLOWER-LOW (packet L8): FL-low from its three remaining inputs

`flowerest1_low_of_items` (conditional helper, distinct name): `LayergardenFlowerLowGate` from
* PLAN-L8 item I: the marked Stage-1′ gate over `𝒱_γ`, `Stage1MKGateLow C₀ 452 cθ` (main's B4 output);
* PLAN-L8 item H: the marked fine gate `FineSplicedGateLowMK` (main's C4b output; the marked final count);
* PLAN-L8 item D / named input: `CoupleClauseLowInput`.
Everything else is proved (and `flowerest1_low_of_items2` also discharges item H1): the carrier chain above the per-component bound (item B), the regular part (item C,
`regularComponentTargetILow`), the non-regular assembly (item F, `nonregLowTarget_of`) and D7's selected class sum
(item G, `selSumTargetTG`). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower

/-- **FL-low from items I, H and D** (conditional helper). -/
theorem flowerest1_low_of_items {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hI : Stage1MKGateLow C₀ 452 cθ) (hH : FineSplicedGateLowMK) (hD : CoupleClauseLowInput) :
    LayergardenFlowerLowGate :=
  flowerest1_low_of_parts (nonregLowTarget_of hC₀ hcθ hI selSumTargetTG hH) hD

/-- **FL-low from items I, H2 and D** (conditional helper): item H1 (`fineSplicedGateLowMK_of_count`, proved from L5c's
cover′ and its named input `SubObjectsInput` = L3's `SubObjectsStatement`) and the γL boundary
(`finalCountGateLowMK_of_L`) reduce item H to the marked count over the fixed low carrier. -/
theorem flowerest1_low_of_items2 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hSO : Famc.SubObjectsInput) (hI : Stage1MKGateLow C₀ 452 cθ)
    (hH2 : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P) (hD : CoupleClauseLowInput) :
    LayergardenFlowerLowGate :=
  flowerest1_low_of_items hC₀ hcθ hI (fineSplicedGateLowMK_of_count hSO (finalCountGateLowMK_of_L hH2)) hD

/-- **FL-low from L8's two remaining items and the other packets' published gates** (conditional helper): item D is
L07's `CC.coupleClauseLow_of_three` (the couple clause from L5a's `Stage1ReductionGateLow`, L5c's proved
`coarseSplicedGateLow`, L6's `FinalCountGateLow` and L5c's cover′ with `SubObjectsInput`). The hypotheses are:
`hSO` (L3's `SubObjectsStatement`, via L5c's `Famc.SubObjectsInput`), `h5a` (L5a), `h6` (L6), and L8's items I
(`Stage1MKGateLow`) and H2 (the marked count over `Src.γL`). -/
theorem flowerest1_low_of_items3 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hSO : Famc.SubObjectsInput) (h5a : Fama.Stage1ReductionGateLow) (h6 : FinalCount.FinalCountGateLow)
    (hI : Stage1MKGateLow C₀ 452 cθ) (hH2 : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P) :
    LayergardenFlowerLowGate :=
  flowerest1_low_of_items2 hC₀ hcθ hSO hI hH2 (LGLow.CC.coupleClauseLow_of_three h5a h6 hSO)

/-- **FL-low with TV2 discharged** (L3's `subObjects_holds`, N2 Theorem 1.15, unconditional): from L5a's and L6's
gates (D) and items I and H2. -/
theorem flowerest1_low_of_items4 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (h5a : Fama.Stage1ReductionGateLow) (h6 : FinalCount.FinalCountGateLow)
    (hI : Stage1MKGateLow C₀ 452 cθ) (hH2 : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P) :
    LayergardenFlowerLowGate :=
  flowerest1_low_of_items3 hC₀ hcθ subObjectsInput h5a h6 hI hH2

/-- **L6's final-count gate, unconditional**: `I.Final.finalCountGateLow_of_ghost` with wt-l6ghost's LOW-chain ghost
cover `Ghost.chainCoverLowL'_holds` (ruling R194). -/
theorem finalCountGateLow_closed : FinalCount.FinalCountGateLow :=
  FinalCount.finalCountGateLow_of_ghost FinalCount.Ghost.chainCoverLowL'_holds

/-- **FL-low with L6's gate discharged**: from L5a's Stage-1 gate (D), item I and item H2. -/
theorem flowerest1_low_of_items5 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (h5a : Fama.Stage1ReductionGateLow) (hI : Stage1MKGateLow C₀ 452 cθ)
    (hH2 : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P) : LayergardenFlowerLowGate :=
  flowerest1_low_of_items4 hC₀ hcθ h5a finalCountGateLow_closed hI hH2

end WaveTurbulence.GammaLow.Flower
