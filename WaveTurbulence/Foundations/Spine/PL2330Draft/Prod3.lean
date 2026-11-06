/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Prod2

/-!
# The product estimate `𝔛^{θ,Λ,a+b}(FG) ≤ 2^θ (2d)^Λ 𝔛^{θ,Λ,a}(F) 𝔛^{θ,Λ,b}(G)` (PL23-30D)
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ} {Λ : ℕ} {F G : (Fin r → ℝ) → Mom d → ℂ}

theorem lintegral_w_dsup_le {θ : ℝ} {Λ₂ : ℕ} {H : (Fin r → ℝ) → Mom d → ℂ} (Gd : Good Λ H)
    (hadm : MixedFourierAdmissible Λ H) {m : ℕ} (hm : m ≤ Λ) :
    ∫⁻ ξ, timeWeight θ ξ * dsup Λ₂ m (Gd.Φ ξ) ≤ (d : ℝ≥0∞) ^ m * mixedFourierNorm θ Λ Λ₂ H := by
  refine le_trans (lintegral_mono fun ξ => mul_le_mul_right (dsup_le_sum_words Λ₂ m _) _) ?_
  exact lintegral_envSum_le Gd hadm hm

/-- **The product estimate** (`G` continuous in time). -/
theorem mixedFourierNorm_mul_le (hΛ : Λ ≠ 0) (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) (a b : ℕ)
    (hGc : ∀ k, Continuous fun t => G t k) (hF : mixedFourierNorm θ Λ a F < ⊤)
    (hG : mixedFourierNorm θ Λ b G < ⊤) :
    mixedFourierNorm θ Λ (a + b) (fun t k => F t k * G t k) ≤
      ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (cLeib d Λ) * mixedFourierNorm θ Λ a F *
        mixedFourierNorm θ Λ b G := by
  obtain ⟨GF⟩ := exists_good hΛ hF
  obtain ⟨GG⟩ := exists_good hΛ hG
  have hadF := admissible_of_lt_top hF
  have hadG := admissible_of_lt_top hG
  have hiF := hadF.1
  have hiG := hadG.1
  have hhG : ∀ k, Integrable (timeFourier fun t => G t k) := fun k =>
    integrable_timeFourier_of_norm_lt_top hθ
      ((timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := b) G k).trans_lt hG)
  have hbd : ∀ k t, ‖G t k‖ ≤ ∫ η, ‖timeFourier (fun t => G t k) η‖ := by
    intro k t
    rw [← timeFourier_inversion (hiG k) (hhG k) (hGc k) t]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hiS : ∀ k, Integrable fun t => F t k * G t k := fun k =>
    (hiF k).mul_bdd (hGc k).aestronglyMeasurable (ae_of_all _ (hbd k))
  have hEnv := ae_envFinite hθ hF hG GF GG
  have hFT := mixedTimeFourier_mul GF GG hiF hiG hhG hGc
  have hadS : MixedFourierAdmissible Λ (fun t k => F t k * G t k) := by
    refine ⟨hiS, Or.inr ?_⟩
    filter_upwards [hEnv] with ξ hξ
    rw [hFT ξ]
    exact (conv_deriv GF GG hξ).1
  refine mixedFourierNorm_le_of_bound (θ := θ) (Λ₂ := a + b) hadS
    (fun n ρ ξ => ∫⁻ η, levMaj GF GG a b n ξ η) ?_ ?_
  · intro n hn ρ
    filter_upwards [hEnv] with ξ hξ
    rw [hFT ξ]
    exact momentumSupNorm_conv_le GF GG hξ a b hn ρ
  · intro n hn ρ
    have hmi : ∀ i ∈ range (n + 1), i ≤ Λ := fun i hi => (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
    have hmni : ∀ i ∈ range (n + 1), n - i ≤ Λ := fun i _ => (Nat.sub_le _ _).trans hn
    -- the inner integral as a sum of convolutions
    have hinner : ∀ ξ, ∫⁻ η, levMaj GF GG a b n ξ η = ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) *
        ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η) := by
      intro ξ
      unfold levMaj
      rw [lintegral_finsetSum _ (fun i hi => ?_)]
      swap
      · exact (measurable_const.mul
          ((measurable_dsup a GF.smooth GF.meas (hmi i hi)).comp (measurable_const.sub measurable_id))).mul
          ((measurable_dsup b GG.smooth GG.meas (hmni i hi)))
      refine Finset.sum_congr rfl fun i hi => ?_
      have e : (fun η => (n.choose i : ℝ≥0∞) * dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)) =
          fun η => (n.choose i : ℝ≥0∞) * (dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)) := by
        funext η; ring
      rw [e, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
    have hmeasC : ∀ i ∈ range (n + 1), Measurable fun ξ => timeWeight θ ξ * ((n.choose i : ℝ≥0∞) *
        ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)) := by
      intro i hi
      exact (timeWeight_measurable θ).mul (Measurable.const_mul
        (measurable_conv (measurable_dsup a GF.smooth GF.meas (hmi i hi))
          (measurable_dsup b GG.smooth GG.meas (hmni i hi))) _)
    simp only [hinner]
    have hsplit : ∫⁻ ξ, timeWeight θ ξ * ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) *
        ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η) =
        ∑ i ∈ range (n + 1), ∫⁻ ξ, timeWeight θ ξ * ((n.choose i : ℝ≥0∞) *
        ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)) := by
      simp only [Finset.mul_sum]
      exact lintegral_finsetSum _ hmeasC
    rw [hsplit]
    have hterm : ∀ i ∈ range (n + 1), ∫⁻ ξ, timeWeight θ ξ * ((n.choose i : ℝ≥0∞) *
        ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)) ≤
        (n.choose i : ℝ≥0∞) * (ENNReal.ofReal (2 ^ θ) * ((d : ℝ≥0∞) ^ i * mixedFourierNorm θ Λ a F) *
          ((d : ℝ≥0∞) ^ (n - i) * mixedFourierNorm θ Λ b G)) := by
      intro i hi
      have h1 := measurable_dsup a GF.smooth GF.meas (hmi i hi)
      have h2 := measurable_dsup b GG.smooth GG.meas (hmni i hi)
      have hc := lintegral_conv_weight_le hθ h1 h2
      have hF' := lintegral_w_dsup_le (θ := θ) (Λ₂ := a) GF hadF (hmi i hi)
      have hG' := lintegral_w_dsup_le (θ := θ) (Λ₂ := b) GG hadG (hmni i hi)
      calc ∫⁻ ξ, timeWeight θ ξ * ((n.choose i : ℝ≥0∞) *
            ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η))
          = (n.choose i : ℝ≥0∞) * ∫⁻ ξ, timeWeight θ ξ *
            ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η) := by
            have hm : Measurable fun ξ => timeWeight θ ξ *
                ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η) :=
              (timeWeight_measurable θ).mul (measurable_conv h1 h2)
            rw [← lintegral_const_mul (f := fun ξ => timeWeight θ ξ *
              ∫⁻ η, dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)) _ hm]
            refine lintegral_congr fun ξ => ?_
            ring
        _ ≤ _ := by
            gcongr
            refine hc.trans ?_
            gcongr
    refine (Finset.sum_le_sum hterm).trans ?_
    have hbin : ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) * (ENNReal.ofReal (2 ^ θ) *
        ((d : ℝ≥0∞) ^ i * mixedFourierNorm θ Λ a F) * ((d : ℝ≥0∞) ^ (n - i) * mixedFourierNorm θ Λ b G)) =
        ENNReal.ofReal (2 ^ θ) * ((d : ℝ≥0∞) + d) ^ n * mixedFourierNorm θ Λ a F * mixedFourierNorm θ Λ b G := by
      rw [add_pow, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hbin]
    gcongr
    exact pow_le_ofReal_cLeib hd hn

end WaveTurbulence.PL2330
