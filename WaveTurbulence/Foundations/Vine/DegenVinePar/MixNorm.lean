/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixLocalized
public import WaveTurbulence.Foundations.SumintPar.SourceExtensionIntegralBound
public import WaveTurbulence.Foundations.SumintPar.LocalizedExtensionNorm

/-! # Norm of the multiplied localized extension (DEGEN-VINE)

The multiplied localized extension is a `(ξ, a)`-mixture of the plain weighted extensions at the shifted input
modulations `ν(ξ) + ζ(a)`.  The weighted-extension bound is uniform in the modulation, hence the mixture is
bounded by the coefficient mass times the mixture mass times the same uniform bound.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- The `(ξ, a)`-mixture representation of the multiplied localized extension. -/
theorem mixLocalized_eq_integral (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ) (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    mixLocalized M hI N h L γ δ η a b p E t =
      ∫ q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α,
        normalizedSourceCoefficient D L γ η a b (E 0 - E 1) q.1 *
          ((Real.fourierChar (externalModulation D (fun v => q.1 (.inl v)) (fun v => q.1 (.inr v)) E) : ℂ) *
            M.u q.2 E) *
          weightedSourceExtension D hI N h L γ δ η p
            (inputModulation D (fun v => q.1 (.inl v)) (fun v => q.1 (.inr v)) + M.ζ q.2) (E 0-E 1) t
        ∂(volume.prod M.μ) := by
  classical
  let C := normalizedSourceCoefficient D L γ η a b (E 0 - E 1)
  let χ := fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
    (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E) : ℂ)
  let ν := fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
    inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))
  let R : ℝ := ‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card
  let W := sourceWeightDecay D L γ η
  let Q := fun x : D.S.VIdx → Fin d → ℤ =>
    ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)
  let H := fun x : D.S.VIdx → Fin d → ℤ => phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t
  have hf (x : D.S.VIdx → Fin d → ℤ) : Integrable
      (fun ξ => C ξ*χ ξ*inputCharacter D L (ν ξ) x) :=
    integrable_normalized_source_modulatedCoefficient hd D hL hD a b x E
  have hg (x : D.S.VIdx → Fin d → ℤ) : Integrable
      (fun a' : M.α => M.u a' E * inputCharacter D L (M.ζ a') x) M.μ := M.integrable_integrand L E x
  have he : (fun q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α =>
      C q.1 * (χ q.1 * M.u q.2 E) *
        weightedSourceExtension D hI N h L γ δ η p (ν q.1 + M.ζ q.2) (E 0-E 1) t) =
      fun q => ∑ x ∈ inputCutoffBox L p,
        ((C q.1*χ q.1*inputCharacter D L (ν q.1) x) * (M.u q.2 E * inputCharacter D L (M.ζ q.2) x)) *
          (((W*R:ℝ):ℂ)*Q x*H x) := by
    funext q
    rw [weightedSourceExtension_eq_sum D hI N h hL γ δ η hη,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [show inputCharacter D L (ν q.1 + M.ζ q.2) x =
      inputCharacter D L (ν q.1) x * inputCharacter D L (M.ζ q.2) x from charOf_add D.S L _ _ x]
    dsimp [W,R,Q,H]
    ring
  have hi (x : D.S.VIdx → Fin d → ℤ) : Integrable
      (fun q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α =>
        ((C q.1*χ q.1*inputCharacter D L (ν q.1) x) * (M.u q.2 E * inputCharacter D L (M.ζ q.2) x)) *
          (((W*R:ℝ):ℂ)*Q x*H x)) (volume.prod M.μ) :=
    ((hf x).mul_prod (hg x)).mul_const _
  have hcancel : ((W*R:ℝ):ℂ)*(((W⁻¹:ℝ):ℂ)) = (R:ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    have hw : W ≠ 0 := (sourceWeightDecay_pos D hL γ η).ne'
    field_simp [hw]
  change _ = ∫ q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α,
    C q.1 * (χ q.1 * M.u q.2 E) *
        weightedSourceExtension D hI N h L γ δ η p (ν q.1 + M.ζ q.2) (E 0-E 1) t ∂(volume.prod M.μ)
  rw [he,integral_finsetSum _ (fun x _ => hi x)]
  unfold mixLocalized
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hprod := integral_prod_mul (μ := (volume : Measure ((D.S.VIdx ⊕ D.S.VIdx) → Mom d))) (ν := M.μ)
    (fun ξ => C ξ*χ ξ*inputCharacter D L (ν ξ) x) (fun a' => M.u a' E * inputCharacter D L (M.ζ a') x)
  rw [integral_mul_const,hprod,
    normalized_source_coefficient_expansion hd D hL hD a b x E]
  change _ = (((W⁻¹:ℝ):ℂ)*localizedSourceWeight D L a b E x) * M.val L E x * (((W*R:ℝ):ℂ)*Q x*H x)
  calc
    _ = (R:ℂ)*(Q x*localizedSourceWeight D L a b E x*M.val L E x*H x) := by
        dsimp [R,Q,H]
    _ = (((W*R:ℝ):ℂ)*((W⁻¹:ℝ):ℂ))*(Q x*localizedSourceWeight D L a b E x*M.val L E x*H x) := by
        rw [hcancel]
    _ = _ := by ring

/-- **Norm of the multiplied localized extension** (weights depending on `r = E 0 - E 1`: the bound is in terms of the
`r`-free majorant `coefMajor`, as in `SumintPar.XNorm00_localizedSourceExtension_le`). -/
theorem XNorm00_mixLocalized_le (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ ν : D.S.VIdx → Mom d,
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p ν (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => mixLocalized M hI N h L γ δ η a b p (E v) t) ≤
      (ENNReal.ofReal (∫ ξ, (sourceWeightDecay D L γ η)⁻¹ * coefMajor D L γ η a b ξ) *
        ENNReal.ofReal M.mass) * B := by
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
  have hint : Integrable Cm := (integrable_coefMajor D hL hD a b).const_mul _
  have hcongr : (fun t (v : V) => mixLocalized M hI N h L γ δ η a b p (E v) t) =
      fun t v => ∫ q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α,
        (Cm q.1 : ℂ) * (ω q.1 v *
          ((Real.fourierChar (externalModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) (E v)) : ℂ) *
            M.u q.2 (E v))) *
          weightedSourceExtension D hI N h L γ δ η p
            (inputModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) + M.ζ q.2)
              (E v 0-E v 1) t ∂(volume.prod M.μ) := by
    funext t v
    rw [mixLocalized_eq_integral hd M hI N h hL hη hD a b p (E v) t]
    apply integral_congr_ae
    apply ae_of_all
    intro q
    change c q.1 v * _ * _ = _
    rw [hc_eq]
    ring
  rw [hcongr]
  have hmain := XNorm00_integral_weightedSourceExtension_le (μ := volume.prod M.μ) D hI N h hL γ δ η hη p
    (fun q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α =>
      inputModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) + M.ζ q.2)
    (((continuous_sourceInputModulation D).measurable.comp measurable_fst).add (M.hζ.comp measurable_snd))
    (fun v => E v 0 - E v 1)
    (fun q => (Cm q.1 : ℂ)) ((Complex.measurable_ofReal.comp hCmc.measurable).comp measurable_fst)
    (by simpa using (hint.ofReal (𝕜 := ℂ)).mul_prod (integrable_const (1 : ℂ) : Integrable (fun _ : M.α => (1:ℂ)) M.μ))
    (fun q v => ω q.1 v * ((Real.fourierChar (externalModulation D (fun v' => q.1 (.inl v')) (fun v' => q.1 (.inr v')) (E v)) : ℂ) *
      M.u q.2 (E v)))
    (fun v => ((hωm v).comp measurable_fst).mul
      (((continuous_sourceExternalCharacter D (E v)).measurable.comp measurable_fst).mul
        ((M.hu (E v)).comp measurable_snd)))
    (fun q v => by
      rw [norm_mul, norm_mul]
      calc _ ≤ 1 * (1 * 1) := mul_le_mul (hωnorm q.1 v)
              (mul_le_mul (norm_source_external_character D q.1 (E v)).le (M.hu1 _ _) (norm_nonneg _) zero_le_one)
              (by positivity) zero_le_one
        _ = 1 := by norm_num)
    θ B (fun q => hF _)
  refine hmain.trans ?_
  have hl : (∫⁻ q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α, ‖(Cm q.1 : ℂ)‖ₑ ∂(volume.prod M.μ)) =
      ENNReal.ofReal (∫ a, Cm a) * ENNReal.ofReal M.mass := by
    have hCmm : Measurable (fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d => ‖(Cm ξ : ℂ)‖ₑ) :=
      (Complex.measurable_ofReal.comp hCmc.measurable).enorm
    rw [lintegral_prod (fun q : ((D.S.VIdx ⊕ D.S.VIdx) → Mom d) × M.α => ‖(Cm q.1 : ℂ)‖ₑ)
      (hCmm.comp measurable_fst).aemeasurable]
    simp only [lintegral_const]
    rw [lintegral_mul_const _ hCmm]
    congr 1
    · rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hCm0)]
      apply lintegral_congr
      intro a
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hCm0 a)]
    · unfold CharMix.mass
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hl]

end WaveTurbulence.DegenVinePar
