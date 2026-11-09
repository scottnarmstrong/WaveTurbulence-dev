/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.NonregTG
public import WaveTurbulence.Foundations.GammaLow.LGLow.Piece
public import WaveTurbulence.Foundations.GammaLow.LGLow.NamedInputs
public import WaveTurbulence.Foundations.GammaLow.LGLow.Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Coarse.Gate
public import WaveTurbulence.Foundations.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.Spine.SourceProviders

/-! # LG-low (packet L07, item 2): `layergarden_low`

* `nonregular_prefix_low`: main's `LGSpine.nonregular_prefix_half` (`Spine/SpineInputsV2.lean`), copied by source, with
  the low gates (L5a `Fama.Stage1ReductionGateLow`, L5c `Famc.CoarseSplicedGateLow`, L6
  `FinalCount.FinalCountGateLow`) and their monotonicity lemmas, and the late step through the waist
  (`nonregular_late_of_typeGate`, `typeGateAt_of_gamma`; the finalsbest2 estimate from `FineSplicedGammaInput`).
* `layergarden_of_nonregular_on`: main's `LGSpine.layergarden_of_nonregular` in the γ-restricted form of main's own
  `layergarden_v2_of_nonregular_half` (copied by source), generic in the γ-predicate `H`. `layergarden_of_nonregular`
  itself takes the full-range `WTPrefix NonregularEstimateAt` and so cannot be applied to a half.
* `layergarden_low`: LG-low from the three low gates, L5c's finalsbest2 (named input `Famc.SubObjectsInput`,
  L3), and main's four spine gates. -/

public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open Set MeasureTheory Filter
open scoped ENNReal

theorem nonregular_prefix_low (hgate : Fama.Stage1ReductionGateLow) (hcoarse : Famc.CoarseSplicedGateLow)
    (hladder : LadderFourierGate) (hcount : FinalCount.FinalCountGateLow) (hfine : FineSplicedGammaInput) :
    WTPrefix fun P => P.γ ≤ 1 / 2 → NonregularEstimateAt P := by
  obtain ⟨C₀, hC₀, hst⟩ := hgate
  have hm1 := Fama.stage1ReductionLow_largeConstantMonotone C₀
  have hm2 := Famc.coarseSplicedLow_largeConstantMonotone
  have hm3 : LargeConstantMonotone LadderFourierAt := ladderFourierAt_largeConstantMonotone
  have hm4 := FinalCount.finalCountLow_largeConstantMonotone
  have hm5 : LargeConstantMonotone LowProfileAt := lowProfile_largeConstantMonotone
  have hQ45 := prefix_and hcount lowProfile_prefix hm4 hm5
  have hQ345 := prefix_and (show WTPrefix LadderFourierAt from hladder) hQ45 hm3 (hm4.and hm5)
  have hQ2345 := prefix_and (show WTPrefix fun P => P.γ ≤ 1 / 2 → Famc.CoarseSplicedGammaAt P from hcoarse) hQ345 hm2
    (hm3.and (hm4.and hm5))
  have hQ0 := prefix_and hst hQ2345 hm1 (hm2.and (hm3.and (hm4.and hm5)))
  have hm0 := hm1.and (hm2.and (hm3.and (hm4.and hm5)))
  have hQ1 := prefix_with_wke_context hQ0
  have hm01 := hm0.and wkeContext_largeConstantMonotone
  have hQ2 := prefix_with_stage1_small_fn hQ1 hm01 (fun d γ => 6 * C₀ d γ) (fun d γ => by have := hC₀ d γ; omega)
  refine prefix_late hQ2 (fun P hP => ?_)
  by_cases hγ : P.γ ≤ 1 / 2
  · refine (nonregular_late_of_typeGate C₀ hC₀ P (fun L hL => ?_) (fun L hL hlog => ?_)).mono
      (fun L h _ => h)
    · obtain ⟨⟨⟨-, -, -, -, e⟩, f⟩, g⟩ := hP L hL
      exact ⟨⟨e, f⟩, g⟩
    · obtain ⟨⟨⟨a, b, c, d, -⟩, -⟩, hs, -, hd3, habs⟩ := hP L hL
      exact typeGateAt_of_gamma (C₀ P.d P.γ) _ hs (b hγ)
        (hfine {P with L := L} hγ c (d hγ) (coverSmall_of_pieceSmall hs)) habs hlog (by omega) (a hγ)
  · exact Filter.Eventually.of_forall (fun L h => absurd h hγ)

theorem nonregularOn_largeConstantMonotone (H : ℝ → Prop) :
    LargeConstantMonotone (fun P => H P.γ → NonregularEstimateAt P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    nonregularEstimate_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

theorem layergarden_of_nonregular_on (H : ℝ → Prop)
    (hLeaf : LeafwiseCoherentApproximationGate) (hTaylor : CoherentTaylorGate)
    (hDecay : LeafwiseIncoherentDecayGate)
    (hnr : WTPrefix fun P => H P.γ → NonregularEstimateAt P) :
    WTPrefix fun P => H P.γ → Induct.LayergardenBody P := by
  have hsource := prefix_and hnr (regular_analytic_sources_prefix hLeaf hTaylor hDecay)
    (nonregularOn_largeConstantMonotone H) regularAnalyticSources_largeConstantMonotone
  have h1 := prefix_add_regular_comparisons hsource
  have h2 := prefix_with_three_contribution_reserve h1
  have h3 := prefix_with_basic_parameters h2
  refine prefix_map ?_ h3
  rintro P ⟨⟨⟨hnr', hcoh, hinc⟩, hres⟩, hd, hδ, hL⟩ hγ
  intro p hp R hR t ht N hN
  have htI : t ∈ Icc (p : ℝ) (p + 1) := ⟨ht.1.le, ht.2⟩
  obtain ⟨hgard, hnonreg⟩ := hnr' hγ p hp R hR N hN t htI
  refine ⟨hgard, ?_, ?_⟩
  · intro n hn
    exact truncSum_pair_off_diagonal P (inputsF P R) (p + 1) N t n hn
  · exact coupleRemainder_bound_of_three_contributions P (by omega) (by linarith) hδ.le hcoh hinc
      hres hp hN R hR t htI hnonreg

/-- **LG-low** (TARGET Prop `layergarden`, L761–L779, for `0 < γ ≤ 1/2`): the low half `LayergardenLowGate` from the
three `𝒱_γ` gates (L5a's Stage 1 reduction, L5c's finalsbest1, L6's finalcount1), L5c's finalsbest2 over `𝒱_γ`
(`fineSplicedGammaInput_of_subObjects`, with L3's named input `Famc.SubObjectsInput`), and main's four verbatim spine
gates (`Spine.leafwise_coherent_approximation`, `Spine.coherent_taylor`, `Spine.leafwise_incoherent_decay`,
`Spine.ladder_fourier`). Conditional helper (distinct name). -/
theorem layergarden_low (h5a : Fama.Stage1ReductionGateLow) (h5c : Famc.CoarseSplicedGateLow)
    (h6 : FinalCount.FinalCountGateLow) (hSO : Famc.SubObjectsInput) : LayergardenLowGate :=
  layergarden_of_nonregular_on (fun γ => γ ≤ 1 / 2) Spine.leafwise_coherent_approximation Spine.coherent_taylor
    Spine.leafwise_incoherent_decay
    (nonregular_prefix_low h5a h5c Spine.ladder_fourier h6 (fineSplicedGammaInput_of_subObjects hSO))

/-- `layergarden_low` with L5c's proved finalsbest1 over `𝒱_γ` (`Famc.coarseSplicedGateLow`) discharged. -/
theorem layergarden_low_of_three (h5a : Fama.Stage1ReductionGateLow) (h6 : FinalCount.FinalCountGateLow)
    (hSO : Famc.SubObjectsInput) : LayergardenLowGate :=
  layergarden_low h5a Famc.coarseSplicedGateLow h6 hSO

/-- **LG-low from the three low gates alone**: `layergarden_low` with L3's `Famc.SubObjectsInput` discharged by L3's
unconditional Thm 1.15 (`TVine.Struct.subObjects_holds`). -/
theorem layergarden_low_proved (h5a : Fama.Stage1ReductionGateLow) (h5c : Famc.CoarseSplicedGateLow)
    (h6 : FinalCount.FinalCountGateLow) : LayergardenLowGate :=
  layergarden_low h5a h5c h6 TVine.Struct.subObjects_holds

/-- **LG-low from L5a's and L6's gates**: `layergarden_low_of_three` with L3's input discharged
(`TVine.Struct.subObjects_holds`). -/
theorem layergarden_low_of_two (h5a : Fama.Stage1ReductionGateLow) (h6 : FinalCount.FinalCountGateLow) :
    LayergardenLowGate :=
  layergarden_low_of_three h5a h6 TVine.Struct.subObjects_holds

end WaveTurbulence.GammaLow.LGLow
