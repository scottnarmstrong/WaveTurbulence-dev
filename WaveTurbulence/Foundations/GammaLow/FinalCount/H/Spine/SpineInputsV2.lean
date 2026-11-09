/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpineInputsS10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SpineInputsV2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The D9/D10 successor `layergarden_v2` (restricted to `1/2 < γ`) from the spine inputs, with the
final-count gate restricted to `1/2 < γ` as the only change of hypothesis (`FinalCountGateHalf`).

**Low-range restatement (L6-HMS2, GAMMA row; PLAN-L6 §3f rule 4).** In the port the range `1/2 < γ` becomes
`γ ≤ 1/2`: `FinalCountGateHalf` is `WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAt P` (the ported `FinalCountAt` is the body
of L6's `FinalCountLAt`, so this is the hypothesis of `finalCountGateLow_of_L`), and `finalCountHalf_largeConstantMonotone`
and `nonregular_prefix_half` are restated with `P.γ ≤ 1 / 2` (same proofs). Main's `layergarden_v2_of_spine` is not
ported: its conclusion is main's frozen `LayergardenV2Gate` (range `1/2 < γ`), it has no consumer in the ported run,
and the γ ≤ 1/2 assembly of the layer-garden statements is outside the ported run (wt-orch's LG-low/FL-low). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set MeasureTheory
open scoped ENNReal

/-- Row 6 restricted to the low range `γ ≤ 1/2` (main: `1/2 < γ`). -/
abbrev FinalCountGateHalf : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAt P

theorem finalCountHalf_largeConstantMonotone :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → FinalCountAt P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    finalCountAt_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

theorem nonregular_prefix_half (hgate : Stage1ReductionGate) (hcoarse : CoarseSplicedGate)
    (hladder : LadderFourierGate) (hcount : FinalCountGateHalf) :
    WTPrefix fun P => P.γ ≤ 1 / 2 → NonregularEstimateAt P := by
  obtain ⟨C₀, hC₀, hst⟩ := hgate
  have hm1 : LargeConstantMonotone (fun P => Stage1ReductionAt (C₀ P.d P.γ) P) :=
    fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h =>
      stage1ReductionAt_largeConstantMonotone (C₀ P.d P.γ) P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  have hm2 : LargeConstantMonotone CoarseSplicedAt := coarseSplicedAt_largeConstantMonotone
  have hm3 : LargeConstantMonotone LadderFourierAt := ladderFourierAt_largeConstantMonotone
  have hm4 := finalCountHalf_largeConstantMonotone
  have hm5 : LargeConstantMonotone LowProfileAt := lowProfile_largeConstantMonotone
  have hQ45 := prefix_and hcount lowProfile_prefix hm4 hm5
  have hQ345 := prefix_and (show WTPrefix LadderFourierAt from hladder) hQ45 hm3 (hm4.and hm5)
  have hQ2345 := prefix_and (show WTPrefix CoarseSplicedAt from hcoarse) hQ345 hm2
    (hm3.and (hm4.and hm5))
  have hQ0 := prefix_and hst hQ2345 hm1 (hm2.and (hm3.and (hm4.and hm5)))
  have hm0 := hm1.and (hm2.and (hm3.and (hm4.and hm5)))
  have hQ1 := prefix_with_wke_context hQ0
  have hm01 := hm0.and wkeContext_largeConstantMonotone
  have hQ2 := prefix_with_stage1_small_fn hQ1 hm01 (fun d γ => 6 * C₀ d γ) (fun d γ => by have := hC₀ d γ; omega)
  refine prefix_late hQ2 (fun P hP => ?_)
  by_cases hγ : P.γ ≤ 1 / 2
  · refine (nonregular_late C₀ hC₀ P (fun L hL => ?_)).mono (fun L h _ => h)
    obtain ⟨⟨⟨a, b, c, d, e⟩, f⟩, g⟩ := hP L hL
    exact ⟨⟨⟨a, b, c, d hγ, e⟩, f⟩, g⟩
  · exact Filter.Eventually.of_forall (fun L h => absurd h hγ)

end WaveTurbulence.GammaLow.FinalCount.H
