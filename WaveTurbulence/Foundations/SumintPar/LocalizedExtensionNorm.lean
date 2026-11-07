/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.LocalizedExtensionFourier
public import WaveTurbulence.Foundations.SumintPar.SourceEnvelope

/-!
# The exact localized ambient extension retains the normalized coefficient mass

Spatial recombination keeps the same output supremum and introduces no
output cardinality factor beyond the already proved positive endpoint.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- The normalized coefficient is dominated by the `r`-free normalized majorant. -/
theorem norm_normalizedSourceCoefficient_le {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (r : Mom d) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) :
    ‖normalizedSourceCoefficient D L γ η a b r ξ‖ ≤
      (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ := by
  unfold normalizedSourceCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (sourceWeightDecay_pos D hL γ η).le)]
  exact mul_le_mul_of_nonneg_left (norm_sourceCoefficient_le_coefMajor D hL hD a b r ξ)
    (inv_nonneg.mpr (sourceWeightDecay_pos D hL γ η).le)

/-- **Linear recombination estimate for the actual localized source extension**, with weights
depending on the output difference `r`: the bound is in terms of the `r`-free majorant. -/
theorem XNorm00_localizedSourceExtension_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ ν : D.S.VIdx → Mom d,
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p ν (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => localizedSourceExtension D hI N h L γ δ η a b p (E v) t) ≤
      ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ) * B := by
  classical
  let Cm : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) → ℝ := fun ξ =>
    (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ
  have hCmc : Continuous Cm := continuous_const.mul (continuous_coefMajor D hD a b)
  have hCm0 : ∀ ξ, 0 ≤ Cm ξ := fun ξ =>
    mul_nonneg (inv_nonneg.mpr (sourceWeightDecay_pos D hL γ η).le) (coefMajor_nonneg D hL γ η a b ξ)
  let c : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) → V → ℂ := fun ξ v =>
    normalizedSourceCoefficient D L γ η a b (E v 0 - E v 1) ξ
  have hcle : ∀ ξ v, ‖c ξ v‖ ≤ Cm ξ := fun ξ v =>
    norm_normalizedSourceCoefficient_le D hL hD a b _ ξ
  let ω : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) → V → ℂ := fun ξ v =>
    if Cm ξ = 0 then 0 else c ξ v / (Cm ξ : ℂ)
  have hωnorm : ∀ ξ v, ‖ω ξ v‖ ≤ 1 := by
    intro ξ v
    by_cases h0 : Cm ξ = 0
    · simp [ω, h0]
    · simp only [ω, h0, ite_false, norm_div, Complex.norm_real, Real.norm_of_nonneg (hCm0 ξ)]
      exact (div_le_one (lt_of_le_of_ne (hCm0 ξ) (Ne.symm h0))).mpr (hcle ξ v)
  have hωm : ∀ v, Measurable (fun ξ => ω ξ v) := by
    intro v
    apply Measurable.ite (hCmc.measurable (measurableSet_singleton 0)) measurable_const
    exact ((continuous_normalizedSourceCoefficient hd D hD a b _).measurable.div
      (Complex.measurable_ofReal.comp hCmc.measurable))
  have hc_eq : ∀ ξ v, c ξ v = (Cm ξ : ℂ) * ω ξ v := by
    intro ξ v
    by_cases h0 : Cm ξ = 0
    · have : c ξ v = 0 := norm_le_zero_iff.mp ((hcle ξ v).trans h0.le)
      simp [ω, h0, this]
    · simp only [ω, h0, ite_false]
      have : (Cm ξ : ℂ) ≠ 0 := by exact_mod_cast h0
      field_simp
  have hmain := XNorm00_integral_weightedSourceExtension_le D hI N h hL γ δ η hη p
    (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
      inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)))
    (continuous_sourceInputModulation D).measurable (fun v => E v 0 - E v 1)
    (fun ξ => (Cm ξ : ℂ)) (Complex.measurable_ofReal.comp hCmc.measurable)
    (((integrable_coefMajor D hL hD a b).const_mul _).ofReal)
    (fun ξ v => ω ξ v *
      (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) (E v)) : ℂ))
    (fun v => (hωm v).mul (continuous_sourceExternalCharacter D (E v)).measurable)
    (fun ξ v => by
      rw [norm_mul]
      exact (mul_le_mul (hωnorm ξ v) (norm_source_external_character D ξ (E v)).le (norm_nonneg _)
        zero_le_one).trans_eq (one_mul 1))
    θ B (fun ξ => hF _)
  have hfun : (fun t v => localizedSourceExtension D hI N h L γ δ η a b p (E v) t) =
      fun t v => ∫ ξ, (Cm ξ : ℂ) * (ω ξ v *
        (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) (E v)) : ℂ)) *
        weightedSourceExtension D hI N h L γ δ η p
          (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) (E v 0 - E v 1) t := by
    funext t v
    unfold localizedSourceExtension
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    change c ξ v * _ * _ = _
    rw [hc_eq]
    ring
  rw [hfun]
  have hint : Integrable Cm := (integrable_coefMajor D hL hD a b).const_mul _
  have hlin : (∫⁻ a, ‖(Cm a : ℂ)‖ₑ) = ENNReal.ofReal (∫ a, Cm a) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hCm0)]
    apply lintegral_congr
    intro a
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hCm0 a)]
  rw [hlin] at hmain
  exact hmain

end WaveTurbulence.SumintPar
