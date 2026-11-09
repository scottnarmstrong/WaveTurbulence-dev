/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.NonregularFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.FinalCountMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.NonregularPrefix
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.NonregularFinal`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The Stage 1 reduction gate as a spine input (rows 7-10 of the SpineInputs list) and the proof of
`WTPrefix NonregularEstimateAt` (TARGET terms (a),(b)) from it, the coarse and ladder gates and the
(separate) final-count gate. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

abbrev Stage1ReductionGate : Prop :=
  ∃ C₀ : ℕ → ℝ → ℕ, (∀ d γ, 2 ≤ C₀ d γ) ∧ WTPrefix (fun P => Stage1ReductionAt (C₀ P.d P.γ) P)

theorem nonregular_prefix (hgate : Stage1ReductionGate) (hcoarse : CoarseSplicedGate)
    (hladder : LadderFourierGate) (hcount : FinalCountGate) : WTPrefix NonregularEstimateAt := by
  obtain ⟨C₀, hC₀, hst⟩ := hgate
  have hm1 : LargeConstantMonotone (fun P => Stage1ReductionAt (C₀ P.d P.γ) P) :=
    fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h =>
      stage1ReductionAt_largeConstantMonotone (C₀ P.d P.γ) P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  have hm2 : LargeConstantMonotone CoarseSplicedAt := coarseSplicedAt_largeConstantMonotone
  have hm3 : LargeConstantMonotone LadderFourierAt := ladderFourierAt_largeConstantMonotone
  have hm4 : LargeConstantMonotone FinalCountAt := finalCountAt_largeConstantMonotone
  have hm5 : LargeConstantMonotone LowProfileAt := lowProfile_largeConstantMonotone
  have hQ45 := prefix_and (show WTPrefix FinalCountAt from hcount) lowProfile_prefix hm4 hm5
  have hQ345 := prefix_and (show WTPrefix LadderFourierAt from hladder) hQ45 hm3 (hm4.and hm5)
  have hQ2345 := prefix_and (show WTPrefix CoarseSplicedAt from hcoarse) hQ345 hm2
    (hm3.and (hm4.and hm5))
  have hQ0 := prefix_and hst hQ2345 hm1 (hm2.and (hm3.and (hm4.and hm5)))
  have hm0 : LargeConstantMonotone (fun P => Stage1ReductionAt (C₀ P.d P.γ) P ∧ CoarseSplicedAt P ∧
      LadderFourierAt P ∧ FinalCountAt P ∧ LowProfileAt P) :=
    hm1.and (hm2.and (hm3.and (hm4.and hm5)))
  have hQ1 := prefix_with_wke_context hQ0
  have hm01 : LargeConstantMonotone (fun P => (Stage1ReductionAt (C₀ P.d P.γ) P ∧ CoarseSplicedAt P ∧
      LadderFourierAt P ∧ FinalCountAt P ∧ LowProfileAt P) ∧ WKEContext P) :=
    hm0.and wkeContext_largeConstantMonotone
  have hQ2 := prefix_with_stage1_small_fn hQ1 hm01 (fun d γ => 6 * C₀ d γ) (fun d γ => by have := hC₀ d γ; omega)
  exact prefix_late hQ2 (fun P hP => nonregular_late C₀ hC₀ P hP)

end WaveTurbulence.GammaLow.FinalCount.H
