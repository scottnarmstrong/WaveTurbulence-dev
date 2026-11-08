/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Cumul
public import WaveTurbulence.Foundations.Flower.FiltProd.Sel
public import WaveTurbulence.Foundations.Incoh.CoupleCutoffUniformDecay
public import WaveTurbulence.Foundations.Incoh.CouplePhysicalL1
public import WaveTurbulence.Foundations.Incoh.CouplePointwiseL1
public import WaveTurbulence.Foundations.Incoh.CoupleUpperBoxAgreement
public import WaveTurbulence.Foundations.Incoh.OneClockCouple

/-! # D5b-2 FILT-PROD: the couple extension (twins of `CoupleExtension`, `CouplePhysicalL1`, `CouplePointwiseL1`, `CoupleUpperBoxAgreement`, `OneClockCouple`, `CoupleCutoffUniformDecay`) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc
/-- Returning from local clocks preserves the weighted Fourier norm exactly. -/
theorem RootCoordinates.timeFourierNorm_coupleExtensionFilt {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ θ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) :
    Fourier.timeFourierNorm θ (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) =
      Fourier.timeFourierNorm θ (Fourier.cutoffDoubleIntegral χ (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I)) := by
  have heq : RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I =
      fun t => Fourier.cutoffDoubleIntegral χ (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I) (t + -(R.baseRootTimes Q)) := by
    funext t
    rw [RootCoordinates.coupleExtensionFilt, sub_eq_add_neg]
  rw [heq, Fourier.timeFourierNorm_translate]

/-- TARGET (incohproof20), with the actual localized couple extension and a single base constant. -/
theorem exists_coupleExtension_timeFourier_boundFilt (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm η (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C, hC, hb⟩ := exists_rootDensityFilt_Lp_bound d hd
  obtain ⟨Cₜ, hCₜ, htime, _⟩ := Fourier.exists_cutoff_timeIntegral_bounds hη hη₁ hχ hcχ
  let C₀ : ℝ := (Cₜ + 1) * C
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan K hK φ hφ I hI hbox R
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hn : n ≠ 0 := by have h := one_le_linkCount_of_incoherent Q hg; omega
  have hCpow : Cₜ ≤ (Cₜ + 1) ^ n :=
    (by linarith : Cₜ ≤ Cₜ + 1).trans (le_self_pow₀ (by linarith : 1 ≤ Cₜ + 1) hn)
  have hcoef : Cₜ * (K * C * δ) ^ n ≤ (K * C₀ * δ) ^ n := by
    calc
      _ ≤ (Cₜ + 1) ^ n * (K * C * δ) ^ n := mul_le_mul_of_nonneg_right hCpow (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; dsimp [C₀]; ring
  have hexp : -(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q ≤
      -(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q := by
    have h := mul_nonneg (Nat.cast_nonneg d) hη.le
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (incoherenceCount Q))
    nlinarith only [h]
  rw [RootCoordinates.timeFourierNorm_coupleExtensionFilt R]
  apply (htime (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I)).trans
  calc
    _ ≤ ENNReal.ofReal Cₜ * ENNReal.ofReal ((K * C * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
      apply mul_le_mul' le_rfl
      rw [RootCoordinates.eLpNorm_localLinkDensityFilt R hLp γ δ Q φ hI hbox]
      exact hb L hL n Q hg hspan K hK φ hφ I hI hbox R
    _ = ENNReal.ofReal ((Cₜ * (K * C * δ) ^ n) *
        L ^ (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
      rw [← ENNReal.ofReal_mul hCₜ.le]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (hcoef) (Real.rpow_le_rpow_of_exponent_le hLone hexp)
        (Real.rpow_nonneg hLp.le _) (by positivity)



/-- The literal canonical couple extension is time-integrable. -/
theorem RootCoordinates.integrable_coupleExtensionFilt {d n : ℕ} (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) :
    Integrable (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) := by
  have hF := RootCoordinates.integrable_localLinkDensityFilt R hL γ δ Q φ hI hbox
  have hG := integrable_cutoffDoubleIntegral hχ hc hF
  change Integrable (fun t => Fourier.cutoffDoubleIntegral χ
    (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I) (t - R.baseRootTimes Q))
  simpa only [sub_eq_add_neg] using hG.comp_add_right (-R.baseRootTimes Q)

/-- A fixed cutoff-dependent factor controls the actual couple extension's physical L¹ norm. -/
theorem RootCoordinates.eLpNorm_coupleExtension_one_leFilt {d n : ℕ} (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) :
    eLpNorm (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) 1 ≤
      (Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound) *
        eLpNorm (RootCoordinates.linkDensityFilt R L γ δ Q φ I) 1 := by
  let F := RootCoordinates.localLinkDensityFilt R L γ δ Q φ I
  have hF : Integrable F := RootCoordinates.integrable_localLinkDensityFilt R hL γ δ Q φ hI hbox
  have hG := integrable_cutoffDoubleIntegral hχ hc hF
  have he : eLpNorm (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) 1 =
      eLpNorm (Fourier.cutoffDoubleIntegral χ F) 1 := by
    change eLpNorm (fun t => Fourier.cutoffDoubleIntegral χ F (t - R.baseRootTimes Q)) 1 = _
    simpa only [Function.comp_def, sub_eq_add_neg] using
      eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
        (measurePreserving_add_right volume (-R.baseRootTimes Q))
  rw [he]
  apply (eLpNorm_cutoffDoubleIntegral_one_le hχ hc hF).trans
  exact le_of_eq (congrArg (fun a =>
    (Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound) * a)
    (RootCoordinates.eLpNorm_localLinkDensityFilt R hL γ δ Q φ hI hbox 1))



/-- The actual canonical couple extension is pointwise bounded by its physical root mass. -/
theorem RootCoordinates.enorm_coupleExtension_leFilt {d n : ℕ} (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    ‖RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I t‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 *
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ Q φ I) 1 := by
  have hb := enorm_cutoffDoubleIntegral_le hχ hc
    (RootCoordinates.integrable_localLinkDensityFilt R hL γ δ Q φ hI hbox) (t - R.baseRootTimes Q)
  rw [RootCoordinates.eLpNorm_localLinkDensityFilt R hL γ δ Q φ hI hbox 1] at hb
  exact hb

/-- The scalar extension agrees with the literal source for every external time above the
actual root layers. Its cutoff may span the entire finite layer range. -/
theorem RootCoordinates.coupleExtension_agrees_aboveFilt {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {χ : ℝ → ℝ}
    (t : Fin 2 → ℝ) (ht : R.baseRootTimes Q ≤ t)
    (hχ : ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) :
    RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I t = RootCoordinates.cumulativeKernelFilt R L γ δ Q φ I t := by
  let τ := t - R.baseRootTimes Q
  have hτ : 0 ≤ τ := sub_nonneg.mpr ht
  have hF := RootCoordinates.integrable_localLinkDensityFilt R hL γ δ Q φ hI hbox
  have hrect := integral_twoTimeBox_eq_doubleInterval hF 0 (τ 0) 0 (τ 1) (hτ 0) (hτ 1)
  have hvec : ![τ 0, τ 1] = τ := by ext i; fin_cases i <;> rfl
  have hzero : ![(0 : ℝ), 0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hvec, hzero] at hrect
  change Fourier.cutoffDoubleIntegral χ (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I) τ = _
  rw [cutoffDoubleIntegral_eq_on_rectangle _ τ hτ hχ, ← hrect]
  exact (RootCoordinates.cumulativeKernel_eq_localBoxIntegralFilt R hL γ δ Q φ hI hbox t).symm

/-- Literal source kernel, independent of the other external clock. -/
def RootCoordinates.oneClockKernelFilt {d n : ℕ} (R : RootCoordinates n) (a : Fin 2)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) : ℂ := normalizedLinkIntegralFilt L γ δ Q φ (I ∩ R.oneClockCut a (t a))

/-- Complete the auxiliary layer integration; no second source root is assumed. -/
theorem RootCoordinates.cumulativeKernel_eq_oneClockKernelFilt {d n : ℕ} (R : RootCoordinates n)
    (a : Fin 2) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin 2 → ℝ}
    (ht : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ t j) :
    RootCoordinates.cumulativeKernelFilt R L γ δ Q φ I t = RootCoordinates.oneClockKernelFilt R a L γ δ Q φ I t := by
  have hset : I ∩ R.rootCut t = I ∩ R.oneClockCut a (t a) := by
    ext w
    constructor
    · rintro ⟨hi, hc⟩
      exact ⟨hi, hc.1 a⟩
    · rintro ⟨hi, hc⟩
      refine ⟨hi, ?_⟩
      have hb : (R.equiv w).1 ∈ R.rootBox Q := by
        apply ((R.equiv_symm_mem_linkBoxes Q (R.equiv w).1 (R.equiv w).2).mp ?_).1
        simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using hbox hi
      change (R.equiv w).1 ≤ t ∧ (R.equiv w).2 ∈ univ
      refine ⟨fun j => ?_, mem_univ _⟩
      by_cases hj : j = a
      · subst j
        exact hc
      · exact (hb.2 j).trans (ht j hj)
  rw [RootCoordinates.cumulativeKernelFilt, RootCoordinates.oneClockKernelFilt, hset]



/-- TARGET (incohproof20), with the dimensional exponential constant chosen before the cutoff. -/
theorem exists_coupleExtension_cutoffUniform_decayFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm η (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) ≤
          ENNReal.ofReal ((K * C * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C, hC, hb⟩ := exists_rootDensityFilt_Lp_bound d hd
  refine ⟨C, hC, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨Cₜ, hCₜ, htime, _⟩ := Fourier.exists_cutoff_timeIntegral_bounds hη hη₁ hχ hcχ
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold Cₜ hη
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨Lᵦ, hLᵦ, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨max Lₐ Lᵦ, hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hg hspan K hK φ hφ I hI hbox R
  have hLa := (le_max_left Lₐ Lᵦ).trans hL
  have hLb := (le_max_right Lₐ Lᵦ).trans hL
  have hLone := hLₐ.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  have hCt : Cₜ ≤ L ^ (η * incoherenceCount Q) := (ha L hLa).trans
    (Real.rpow_le_rpow_of_exponent_le hLone (by
      have hgR : 1 ≤ (incoherenceCount Q : ℝ) := by exact_mod_cast hg
      nlinarith only [hgR, hη.le]))
  rw [RootCoordinates.timeFourierNorm_coupleExtensionFilt R]
  apply (htime (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I)).trans
  have hroot := hb L hLb n Q hg hspan K hK φ hφ I hI hbox R
  rw [← RootCoordinates.eLpNorm_localLinkDensityFilt R hLp γ δ Q φ hI hbox] at hroot
  apply (mul_le_mul' (ENNReal.ofReal_le_ofReal hCt) hroot).trans
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : η * incoherenceCount Q +
      (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q) ≤
      -(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q := by
    have hgR : 0 ≤ (incoherenceCount Q : ℝ) := Nat.cast_nonneg _
    have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith only [mul_nonneg hη.le hgR, mul_nonneg (sub_nonneg.mpr hdR) (mul_nonneg hη.le hgR)]
  calc
    _ = (K * C * δ) ^ n * L ^ (η * incoherenceCount Q +
        (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
      rw [Real.rpow_add hLp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLone hexp)
      (pow_nonneg (mul_nonneg (mul_nonneg hK hC.le) hδ.le) _)


end WaveTurbulence.Flower.FiltProd
