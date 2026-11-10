/- Copy of INDUCT ../induct/BaseEvent.lean (sha256 579f4cd81db0da95f1851f83f047737493a4e0aafd2bd87cdce984800a79ef3e); only the namespace and imports changed. -/
/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.NLS.Measurability
public import WaveTurbulence.Foundations.Probability.RandomRapidDecay
public import WaveTurbulence.Foundations.Probability.WeightedLatticeSummability
/-! TARGET L708: the author-approved full-measure rapid-decay reading of the base event. -/
@[expose] public section
namespace WaveTurbulence.Fixedpt
open MeasureTheory ProbabilityTheory Set Filter

noncomputable def initialRapidEvent {d : ℕ} {Ω : Type*} (L : ℝ) (φ : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) : Set Ω :=
  {ω | IsRapidDecay (initialCoeff L φ g ω)}

/-- Unit-modulus coordinate multipliers preserve rapid decay pointwise. -/
theorem rapidDecay_mul_phase {d : ℕ} {c f : (Fin d → ℤ) → ℂ}
    (hc : IsRapidDecay c) (hf : ∀ n, ‖f n‖ = 1) : IsRapidDecay (fun n => f n * c n) := by
  intro N
  obtain ⟨C, hC⟩ := hc N
  exact ⟨C, fun n => by rw [norm_mul, hf n, one_mul]; exact hC n⟩

theorem initialRapidEvent_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 < L) (φ : SchwartzMap (Mom d) ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) :
    ∀ᵐ ω ∂μ, ω ∈ initialRapidEvent L φ g :=
  Probability.ae_initialCoeff_isRapidDecay hL φ g hlaw

end WaveTurbulence.Fixedpt
