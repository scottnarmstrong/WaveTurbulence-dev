/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes
public import WaveTurbulence.Foundations.Spine.SpineInputsS10
/-! The D9/D10 successor `layergarden_v2` (restricted to `1/2 < γ`) from the spine inputs, with the
final-count gate restricted to `1/2 < γ` as the only change of hypothesis (`FinalCountGateHalf`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set MeasureTheory
open scoped ENNReal

/-- Row 6 restricted to `1/2 < γ`. -/
abbrev FinalCountGateHalf : Prop := WTPrefix fun P => 1 / 2 < P.γ → FinalCountAt P

/-- The canonical main gate with the exact frozen `layergarden_v2` body. -/
abbrev LayergardenV2Gate : Prop := V2Chain.LayergardenV2Gate

theorem finalCountHalf_largeConstantMonotone :
    LargeConstantMonotone (fun P => 1 / 2 < P.γ → FinalCountAt P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    finalCountAt_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

theorem nonregular_prefix_half (hgate : Stage1ReductionGate) (hcoarse : CoarseSplicedGate)
    (hladder : LadderFourierGate) (hcount : FinalCountGateHalf) :
    WTPrefix fun P => 1 / 2 < P.γ → NonregularEstimateAt P := by
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
  by_cases hγ : 1 / 2 < P.γ
  · refine (nonregular_late C₀ hC₀ P (fun L hL => ?_)).mono (fun L h _ => h)
    obtain ⟨⟨⟨a, b, c, d, e⟩, f⟩, g⟩ := hP L hL
    exact ⟨⟨⟨a, b, c, d hγ, e⟩, f⟩, g⟩
  · exact Filter.Eventually.of_forall (fun L h => absurd h hγ)

theorem nonregularHalf_largeConstantMonotone :
    LargeConstantMonotone (fun P => 1 / 2 < P.γ → NonregularEstimateAt P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    nonregularEstimate_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

theorem layergarden_v2_of_nonregular_half
    (hLeaf : LeafwiseCoherentApproximationGate) (hTaylor : CoherentTaylorGate)
    (hDecay : LeafwiseIncoherentDecayGate)
    (hnr : WTPrefix fun P => 1 / 2 < P.γ → NonregularEstimateAt P) : LayergardenV2Gate := by
  have hsource := prefix_and hnr (regular_analytic_sources_prefix hLeaf hTaylor hDecay)
    nonregularHalf_largeConstantMonotone regularAnalyticSources_largeConstantMonotone
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

/-- `layergarden_v2` from the spine inputs and the final-count gate restricted to `1/2 < γ`. -/
theorem layergarden_v2_of_spine (S : SpineInputs) (hcount : FinalCountGateHalf) :
    LayergardenV2Gate :=
  layergarden_v2_of_nonregular_half S.leafCoherent S.taylor S.leafDecay
    (nonregular_prefix_half S.stage1 S.coarse S.ladder hcount)

end WaveTurbulence.LGSpine
