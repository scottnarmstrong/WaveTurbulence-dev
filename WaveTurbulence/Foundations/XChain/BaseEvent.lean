/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.NLS.Measurability
public import WaveTurbulence.Foundations.Probability.RandomRapidDecay
public import WaveTurbulence.Foundations.Probability.WeightedLatticeSummability
/-! TARGET L708: the author-approved full-measure rapid-decay reading of the base event. -/
@[expose] public section
namespace WaveTurbulence.Induct
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

theorem measurableSet_initialRapidEvent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (L : ℝ) (φ : Mom d → ℝ) {g : (Fin d → ℤ) → Ω → ℂ}
    (hg : ∀ n, Measurable (g n)) : MeasurableSet (initialRapidEvent L φ g) :=
  NLS.measurableSet_isRapidDecay.preimage (NLS.measurable_initialCoeff L φ hg)

theorem symmetric_initialRapidEvent {d : ℕ} {Ω : Type*} (L : ℝ) (φ : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) : IsSymmetricEvent L φ g (initialRapidEvent L φ g) := by
  refine ⟨{c | IsRapidDecay c}, NLS.measurableSet_isRapidDecay, rfl, ?_, ?_⟩
  · intro θ c hc
    exact rapidDecay_mul_phase hc (fun _ => Complex.norm_exp_ofReal_mul_I θ)
  · intro x c hc
    exact rapidDecay_mul_phase hc (fun n => by
      simpa only [Complex.ofReal_neg] using Complex.norm_exp_ofReal_mul_I
        (-(2 * Real.pi * inner ℝ (latticePoint L n) x)))

theorem initialRapidEvent_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 < L) (φ : SchwartzMap (Mom d) ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) :
    ∀ᵐ ω ∂μ, ω ∈ initialRapidEvent L φ g :=
  Probability.ae_initialCoeff_isRapidDecay hL φ g hlaw

theorem restrict_initialRapidEvent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 < L) (φ : SchwartzMap (Mom d) ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) :
    μ.restrict (initialRapidEvent L φ g) = μ :=
  Measure.restrict_eq_self_of_ae_mem (initialRapidEvent_ae hL φ g hlaw)

theorem measure_initialRapidEvent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 < L) (φ : SchwartzMap (Mom d) ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) :
    μ.real (initialRapidEvent L φ g) = 1 := by
  have he : initialRapidEvent L φ g =ᵐ[μ] univ :=
    eventuallyEqSet_univ.mpr (initialRapidEvent_ae hL φ g hlaw)
  exact (measureReal_congr he).trans probReal_univ

/-- At level zero the solution-class bound is the only nontrivial pointwise condition. -/
theorem isASolution_zero_of_rapidDecay {d : ℕ} {L γ δ : ℝ} (hL : 0 < L)
    {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) :
    IsASolution L γ δ 0 c (fun _ => c) := by
  have hs := Probability.summable_real_weight_of_isRapidDecay hL hc ((d : ℝ) + 1)
  refine ⟨rfl, ⟨∑' n, (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖c n‖,
    fun _ _ n => hs.le_tsum n (fun _ _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))⟩, ?_⟩
  intro t ht n
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst t
  rw [Icc_self]
  exact HasFDerivWithinAt.singleton

end WaveTurbulence.Induct
