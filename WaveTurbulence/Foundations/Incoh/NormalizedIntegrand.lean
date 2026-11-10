/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.AbsorbedProductDecay
public import WaveTurbulence.Foundations.Incoh.CouplingScale

/-!
# The normalized localized time integrand

TARGET (incohproof9), (incohproof17)–(incohproof18). The time-order
indicator is retained literally, so root densities are actual marginals
rather than functions supplied with assumed endpoint estimates.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The complete localized product, including its source coupling and time-order indicator. -/
@[expose] def normalizedLinkIntegrand {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
    I.indicator (fun t => ∏ i, linkTimeFactor L γ δ (Q i) (t i)) t

/-- The literal source integrand is integrable on every measurable time-order subdomain. -/
theorem integrable_normalizedLinkIntegrand {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    Integrable (normalizedLinkIntegrand L γ δ Q I) :=
  ((integrableOn_linkProduct hL γ δ Q hbox).integrable_indicator hI).const_mul _

/-- Integrating the full normalized integrand recovers the original localized kernel. -/
theorem integral_normalizedLinkIntegrand {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    (∫ t, normalizedLinkIntegrand L γ δ Q I t) = normalizedLinkIntegral L γ δ Q I := by
  unfold normalizedLinkIntegrand normalizedLinkIntegral
  rw [integral_const_mul, integral_indicator hI]

/-- The exact absolute mass of the normalized source integrand. -/
theorem lintegral_normalizedLinkIntegrand_eq {d n : ℕ} {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ : ℝ) (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    (∫⁻ t, ‖normalizedLinkIntegrand L γ δ Q I t‖ₑ) =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ∫⁻ t in I, ‖∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ := by
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖((((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ))‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) := by
    rw [← ofReal_norm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  simp_rw [normalizedLinkIntegrand, enorm_mul, hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [← lintegral_indicator hI]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ I
  · rw [Set.indicator_of_mem (s := I) ht, Set.indicator_of_mem (s := I) ht]
  · rw [Set.indicator_of_notMem (s := I) ht, Set.indicator_of_notMem (s := I) ht, enorm_zero]

/-- TARGET (incohproof18): the actual normalized time integrand has the stated L¹ decay. -/
theorem exists_normalizedLinkIntegrand_L1_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        (∫⁻ t, ‖normalizedLinkIntegrand L γ δ Q I t‖ₑ) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absolute_linkProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan I hI hbox
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  rw [lintegral_normalizedLinkIntegrand_eq hLp hδ γ Q hI]
  calc
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) :=
      mul_le_mul' le_rfl (hb L hL n Q hspan I hbox)
    _ = ENNReal.ofReal (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (C₀ * kineticLinkScale d γ δ L) ^ n) *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
      rw [← ENNReal.ofReal_mul hc, mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (coupling_scale_le hLp hδ hC₀.le γ) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.Incoh
