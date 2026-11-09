/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourceProviders
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.KindFinal.Export
-- L5b port of `WaveTurbulence.Foundations.VineEst.V5Proof` (its theorem `vineEstCanonLayerHalfMK`), see
-- COPIED-SHA256SUMS.

/-! # TARGET Proposition `vineest` for vine chains over `𝒱_γ` (packet L5b, FAMILY-γ: `vineest`′)

TARGET Prop `vineest` (L1742–L1751; §9.2 L1723–L1741, proof L1752–L1925) estimates the twisted, recentered class kernel
of a (CL) vine chain. Main proves it (`VineEst.vineEstCanonLayerHalfMK`, all `0 < γ < 1`) for chains of the drawn
vines (I)–(VIII). This module gives the same statement for chains whose ingredients are members of the
`γ`-dependent family `𝒱_γ` (ruling D11; for `γ ≤ 1/2`: (I), (II) and the T-vines):

* the chain is `VineEstS2.CLChainAssemblyΓ P.γ G R n` (ingredients `FinalCount.Src.IsSomeVine P.γ`, L6's carrier);
* the chart obligation is `NormalChartSupply P.γ` (L4's de-indexed chart with the cohmol groups, for the normal
  ingredients; `normalChartSupply_of_tvine` derives it from L4's Theorem C), in the place of main's `VINEPARAM`;
* the cohmol index is `VineEstS3.cohmolIndexΓ` (groups `famGroups`; for a T-vine its pieces, TARGET Def `cohmol`).

Everything else in the statement (the class kernel `Cont.twistedRecenteredModC` over the canonical twist class, the
sumint data `step3DΓ`, the rows, `regionLeafSize`, the gates) is main's, read through the chain. The proof is main's
proof (the V5 tower, `VineEstS2`–`VineEstS5C`, `HFree`) ported over the family parameter `γF`: the analysis never uses
which family the ingredients come from, only their charts (`sumint`'s Nor units for the normal ones, TARGET L1595)
and that the bad ones are the drawn (I), (II).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb

open WaveTurbulence.Induct

/-- **`vineest` for chains over `𝒱_{γF}`, every family parameter `γF`**: the family-generic port of main's
`VineEst.vineEstCanonLayerHalfMK` (from main's proved leafwise gates). -/
theorem vineEstCanonLayerHalfMKΓ {γF : ℝ} : WTPrefix (VineEstS5C.VineEstCanonLayerHalfMKΓ (γF := γF)) :=
  VineEstS5C.P4.KindFinal.vineEstCanonLayerHalfMK_of_gatesΓ Spine.leafwise_coherent_approximation
    Spine.leafwise_incoherent_decay

/-- **TARGET Proposition `vineest` (L1742–L1751) over `𝒱_γ`** at `P`: main's `VineEstS5C.VineEstCanonLayerHalfMK`
(layer-uniform, halved bad-vine gain, modulated class kernel) for every chain assembly over `𝒱_{P.γ}` and every
chart supply `NormalChartSupply P.γ`. -/
abbrev VineEstGammaHalfMK (P : WTParams) : Prop := VineEstS5C.VineEstCanonLayerHalfMKΓ (γF := P.γ) P

/-- **TARGET Proposition `vineest` over `𝒱_γ`, for all `0 < γ < 1`** (in particular the low half `γ ≤ 1/2`). -/
theorem vineEstGammaHalfMK : WTPrefix VineEstGammaHalfMK := fun d hd γ hγ =>
  vineEstCanonLayerHalfMKΓ (γF := γ) d hd γ hγ

end WaveTurbulence.GammaLow.Famb
