/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKGarden.MainMK
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKChain.Top
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.LowL
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Ghost.ChainLowLE

/-! # L8-H2: the marked count at `γ ≤ 1/2` (`FinalCountGateLowMK`)

L8's item H2 (PLAN-L8 §3 row H): `FinalCountGateLowMK` as `finalCountGateLowMK_of_L` (L8, `Carrier/LowL.lean`) applied
to the marked count over the fixed low carrier, `WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P`, which is
main's C1c route (`FinalMKGarden.MainMK.finalCountGateHalfMK_of_classBound`) on main's C1b class bound
(`FinalMKChain.Top.lowLoopClassBoundMKAll`), both ported onto L6's low run (H2-PLAN §1). The only hypothesis of the
route is H2's named input `MKLowInputs` (the R194 root form `ChainCoverLowLE'` of the marked chain cover, H2-PLAN §2);
it is discharged by wt-l6ghost's proof `Ghost.chainCoverLowLE'_holds` (`H2/Ghost/ChainLowLE.lean`), which gives the
unconditional `finalCountGateLowMK_holds`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Flower.H2

/-- **The marked count over `Src.γL` for `γ ≤ 1/2`**, from H2's class bound (C1b) through the garden route (C1c). -/
theorem finalCountAtMKLAt_low [MKLowInputs] : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P :=
  finalCountAtMKLAt_of_classBound lowLoopClassBoundMKAll

/-- **Item H2: `FinalCountGateLowMK`** (L8's target), given H2's named input `MKLowInputs`. -/
theorem finalCountGateLowMK_H2 [MKLowInputs] : FinalCountGateLowMK :=
  finalCountGateLowMK_of_L finalCountAtMKLAt_low

/-- H2's named input is proved (wt-l6ghost, `H2/Ghost/ChainLowLE.lean`). -/
instance mkLowInputs : MKLowInputs := ⟨Ghost.chainCoverLowLE'_holds⟩

/-- **The marked count over `Src.γL` for `γ ≤ 1/2`, unconditionally** (L8's `hH2` slot of
`flowerest1_low_of_items4`). -/
theorem finalCountAtMKLAt_holds : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAtMKLAt P := finalCountAtMKLAt_low

/-- **Item H2: `FinalCountGateLowMK`, unconditionally.** -/
theorem finalCountGateLowMK_holds : FinalCountGateLowMK := finalCountGateLowMK_H2

end WaveTurbulence.GammaLow.Flower.H2
