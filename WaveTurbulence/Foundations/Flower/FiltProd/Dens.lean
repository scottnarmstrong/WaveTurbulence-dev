/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Mass
public import WaveTurbulence.Foundations.Flower.FiltSrc.Density
public import WaveTurbulence.Foundations.Incoh.RootDensityLp

/-! # D5b-2 FILT-PROD: the root density (twins of `NormalizedIntegrand`, `RootDensityL1`, `LocalRootDensity`)

The definitions `normalizedLinkIntegrandFilt`, `RootCoordinates.linkDensityFilt`, `RootCoordinates.localLinkDensityFilt`
are D5b-1's (`FiltSrc.Density`); the analytic lemmas are here. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc

/-! ### `NormalizedIntegrand` -/

theorem integrable_normalizedLinkIntegrandFilt {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    Integrable (normalizedLinkIntegrandFilt L γ δ Q φ I) :=
  ((integrableOn_linkProductFilt hL γ δ Q φ hbox).integrable_indicator hI).const_mul _

theorem integral_normalizedLinkIntegrandFilt {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    (∫ t, normalizedLinkIntegrandFilt L γ δ Q φ I t) = normalizedLinkIntegralFilt L γ δ Q φ I := by
  unfold normalizedLinkIntegrandFilt normalizedLinkIntegralFilt
  rw [integral_const_mul, integral_indicator hI]

theorem lintegral_normalizedLinkIntegrandFilt_eq {d n : ℕ} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : MeasurableSet I) :
    (∫⁻ t, ‖normalizedLinkIntegrandFilt L γ δ Q φ I t‖ₑ) =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ∫⁻ t in I, ‖∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)‖ₑ := by
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖((((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ))‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) := by
    rw [← ofReal_norm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  simp_rw [normalizedLinkIntegrandFilt, enorm_mul, hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [← lintegral_indicator hI]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ I
  · rw [Set.indicator_of_mem (s := I) ht, Set.indicator_of_mem (s := I) ht]
  · rw [Set.indicator_of_notMem (s := I) ht, Set.indicator_of_notMem (s := I) ht, enorm_zero]

theorem exists_normalizedLinkIntegrandFilt_L1_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        (∫⁻ t, ‖normalizedLinkIntegrandFilt L γ δ Q φ I t‖ₑ) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absolute_filtLinkProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ I hI hbox
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  rw [lintegral_normalizedLinkIntegrandFilt_eq hLp hδ γ Q φ hI]
  have hKC : 0 ≤ K * C₀ := mul_nonneg hK hC₀.le
  calc
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ENNReal.ofReal ((K * (C₀ * kineticLinkScale d γ δ L)) ^ n *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) :=
      mul_le_mul' le_rfl (hb L hL n Q hspan K hK φ hφ I hbox)
    _ = ENNReal.ofReal (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (K * C₀ * kineticLinkScale d γ δ L) ^ n) *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
      rw [← ENNReal.ofReal_mul hc, mul_assoc K C₀, mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (coupling_scale_le hLp hδ hKC γ) (Real.rpow_nonneg hLp.le _)

/-! ### `RootDensityL1` -/

theorem RootCoordinates.integrable_linkDensityFilt {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    Integrable (RootCoordinates.linkDensityFilt R L γ δ Q φ I) :=
  R.integrable_density (integrable_normalizedLinkIntegrandFilt hL γ δ Q φ hI hbox)

theorem exists_rootDensityFilt_L1_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        eLpNorm (RootCoordinates.linkDensityFilt R L γ δ Q φ I) 1 ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedLinkIntegrandFilt_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ I hI hbox R
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hF := integrable_normalizedLinkIntegrandFilt hLp γ δ Q φ hI hbox
  rw [eLpNorm_one_eq_lintegral_enorm
    (RootCoordinates.integrable_linkDensityFilt R hLp γ δ Q φ hI hbox).aestronglyMeasurable]
  exact (R.lintegral_density_le hF).trans (hb L hL n Q hspan K hK φ hφ I hI hbox)

/-! ### `LocalRootDensity` -/

theorem RootCoordinates.integrable_localLinkDensityFilt {d n r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    Integrable (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I) :=
  (RootCoordinates.integrable_linkDensityFilt R hL γ δ Q φ hI hbox).comp_add_right (R.baseRootTimes Q)

theorem RootCoordinates.eLpNorm_localLinkDensityFilt {d n r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (p : ℝ≥0∞) :
    eLpNorm (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I) p =
      eLpNorm (RootCoordinates.linkDensityFilt R L γ δ Q φ I) p := by
  have hmp : MeasurePreserving (fun t : Fin r → ℝ => t + R.baseRootTimes Q) :=
    measurePreserving_add_right volume (R.baseRootTimes Q)
  exact eLpNorm_comp_measurePreserving
    (RootCoordinates.integrable_linkDensityFilt R hL γ δ Q φ hI hbox).aestronglyMeasurable hmp

theorem RootCoordinates.linkDensityFilt_eq_zero_of_notMem_rootBox {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin r → ℝ} (ht : t ∉ R.rootBox Q) :
    RootCoordinates.linkDensityFilt R L γ δ Q φ I t = 0 := by
  change (∫ u : Fin R.restCount → ℝ, normalizedLinkIntegrandFilt L γ δ Q φ I (R.equiv.symm (t, u))) = 0
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro u
  dsimp only
  have hnot : R.equiv.symm (t, u) ∉ I := by
    intro h
    exact ht ((R.equiv_symm_mem_linkBoxes Q t u).mp (hbox h)).1
  rw [normalizedLinkIntegrandFilt, Set.indicator_of_notMem (s := I) hnot, mul_zero]
  simp only [Pi.zero_apply]

end WaveTurbulence.Flower.FiltProd
