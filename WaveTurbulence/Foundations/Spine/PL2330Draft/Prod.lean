/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Conv

/-!
# Time products in `𝔛^{θ,Λ,a+b}` with momentum derivatives (PL23-30D)

`(F G)^(ξ,k) = ∫ F̂(ξ-η,k) Ĝ(η,k) dη` for `G` continuous in time. Differentiating under the `η`-integral
(`ParamDerivFin`, dominated by the operator envelopes `dsup`, finite almost everywhere by Young's inequality) and
the Leibniz rule give `𝔛^{θ,Λ,a+b}(FG) ≤ 2^θ (2d)^Λ 𝔛^{θ,Λ,a}(F) 𝔛^{θ,Λ,b}(G)`.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

theorem one_le_momentumBracket (k : Mom d) : 1 ≤ momentumBracket k := by
  unfold momentumBracket
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖k‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖k‖])

theorem momentumSupNorm_mono_weight {a b : ℕ} (h : a ≤ b) (f : Mom d → ℂ) :
    momentumSupNorm a f ≤ momentumSupNorm b f := by
  unfold momentumSupNorm
  refine iSup_mono fun k => mul_le_mul_left ?_ _
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (one_le_momentumBracket k) h)

/-- The slices of a family of finite norm have finite scalar norms. -/
theorem timeFourierNorm_slice_le {θ : ℝ} {Λ Λ₂ : ℕ} (G : (Fin r → ℝ) → Mom d → ℂ) (k : Mom d) :
    timeFourierNorm θ (fun t => G t k) ≤ mixedFourierNorm θ Λ Λ₂ G := by
  by_cases hadm : MixedFourierAdmissible Λ G
  · rw [mixedFourierNorm_eq_iSup hadm, timeFourierNorm_eq_lintegral (hadm.1 k)]
    refine le_iSup₂_of_le 0 (Nat.zero_le _) (le_iSup_of_le Fin.elim0 (lintegral_mono fun ξ => ?_))
    refine mul_le_mul_right ?_ _
    rw [momentumDerivative_zero]
    unfold momentumSupNorm
    refine le_iSup_of_le k ?_
    have hb : (1 : ℝ) ≤ momentumBracket k ^ Λ₂ := one_le_pow₀ (one_le_momentumBracket k)
    calc ‖mixedTimeFourier G ξ k‖ₑ = 1 * ‖mixedTimeFourier G ξ k‖ₑ := (one_mul _).symm
      _ ≤ ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖mixedTimeFourier G ξ k‖ₑ := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hb
  · rw [mixedFourierNorm_of_not_admissible hadm]
    exact le_top

variable {Λ : ℕ} {F G : (Fin r → ℝ) → Mom d → ℂ}

/-- The Fourier-side convolution of two regularizations. -/
noncomputable def convΨ (GF : Good Λ F) (GG : Good Λ G) (ξ : Fin r → ℝ) (k : Mom d) : ℂ :=
  ∫ η, GF.Φ (ξ - η) k * GG.Φ η k

theorem ae_Phi_sub (GF : Good Λ F) (ξ : Fin r → ℝ) :
    ∀ᵐ η : Fin r → ℝ, GF.Φ (ξ - η) = mixedTimeFourier F (ξ - η) :=
  (Measure.measurePreserving_sub_left (volume : Measure (Fin r → ℝ)) ξ).quasiMeasurePreserving.ae GF.ae

/-- **The transform of a product** is the convolution of the regularized transforms. -/
theorem mixedTimeFourier_mul (GF : Good Λ F) (GG : Good Λ G) (hiF : ∀ k, Integrable fun t => F t k)
    (hiG : ∀ k, Integrable fun t => G t k) (hhG : ∀ k, Integrable (timeFourier fun t => G t k))
    (hGc : ∀ k, Continuous fun t => G t k) (ξ : Fin r → ℝ) :
    mixedTimeFourier (fun t k => F t k * G t k) ξ = convΨ GF GG ξ := by
  funext k
  unfold mixedTimeFourier convΨ
  rw [timeFourier_mul_eq (hiF k) (hiG k) (hhG k) (hGc k) ξ]
  refine integral_congr_ae ?_
  filter_upwards [ae_Phi_sub GF ξ, GG.ae] with η h1 h2
  rw [h1, h2]
  rfl

section Deriv

variable (GF : Good Λ F) (GG : Good Λ G)

/-- The integrand of `convΨ`. -/
noncomputable def convF (ξ η : Fin r → ℝ) (k : Mom d) : ℂ := GF.Φ (ξ - η) k * GG.Φ η k

theorem convF_smooth (ξ η : Fin r → ℝ) : ContDiff ℝ Λ (convF GF GG ξ η) :=
  (GF.smooth _).mul (GG.smooth _)

theorem convF_meas (ξ : Fin r → ℝ) (k : Mom d) : StronglyMeasurable fun η => convF GF GG ξ η k :=
  ((GF.meas k).comp_measurable (measurable_const.sub measurable_id)).mul (GG.meas k)

/-- The finiteness set of the convolutions of the operator envelopes. -/
def EnvFinite (GF : Good Λ F) (GG : Good Λ G) (ξ : Fin r → ℝ) : Prop :=
  ∀ i j : ℕ, i ≤ Λ → j ≤ Λ →
    ∫⁻ η, dsup 0 i (GF.Φ (ξ - η)) * dsup 0 j (GG.Φ η) < ⊤

theorem ae_envFinite {θ : ℝ} (hθ : 0 ≤ θ) {a b : ℕ} (hF : mixedFourierNorm θ Λ a F < ⊤)
    (hG : mixedFourierNorm θ Λ b G < ⊤) (GF : Good Λ F) (GG : Good Λ G) :
    ∀ᵐ ξ : Fin r → ℝ, EnvFinite GF GG ξ := by
  have hadF := admissible_of_lt_top hF
  have hadG := admissible_of_lt_top hG
  have h1 : ∀ i j : ℕ, i ≤ Λ → j ≤ Λ → ∀ᵐ ξ : Fin r → ℝ,
      ∫⁻ η, dsup 0 i (GF.Φ (ξ - η)) * dsup 0 j (GG.Φ η) < ⊤ := by
    intro i j hi hj
    have mF := measurable_dsup 0 GF.smooth GF.meas hi
    have mG := measurable_dsup 0 GG.smooth GG.meas hj
    have fin : ∀ (H : (Fin r → ℝ) → Mom d → ℂ) (Gd : Good Λ H) (c m : ℕ), m ≤ Λ →
        mixedFourierNorm θ Λ c H < ⊤ → ∫⁻ ξ, dsup 0 m (Gd.Φ ξ) ≠ ⊤ := by
      intro H Gd c m hm hH
      have hadH := admissible_of_lt_top hH
      have h3 : ∫⁻ ξ, dsup 0 m (Gd.Φ ξ) ≤ (d : ℝ≥0∞) ^ m * mixedFourierNorm θ Λ c H := by
        calc ∫⁻ ξ, dsup 0 m (Gd.Φ ξ) ≤ ∫⁻ ξ, timeWeight θ ξ *
              ∑ w : Fin m → Fin d, momentumSupNorm c (momentumDerivative w (Gd.Φ ξ)) := by
              refine lintegral_mono fun ξ => ?_
              have hw : (1 : ℝ≥0∞) ≤ timeWeight θ ξ := by
                simpa only [timeWeight, ENNReal.ofReal_one] using
                  ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)
              calc dsup 0 m (Gd.Φ ξ) ≤ ∑ w : Fin m → Fin d, momentumSupNorm 0 (momentumDerivative w (Gd.Φ ξ)) :=
                    dsup_le_sum_words 0 m _
                _ ≤ ∑ w : Fin m → Fin d, momentumSupNorm c (momentumDerivative w (Gd.Φ ξ)) :=
                    Finset.sum_le_sum fun w _ => momentumSupNorm_mono_weight (Nat.zero_le c) _
                _ = 1 * ∑ w : Fin m → Fin d, momentumSupNorm c (momentumDerivative w (Gd.Φ ξ)) := (one_mul _).symm
                _ ≤ _ := mul_le_mul_left hw _
          _ ≤ _ := lintegral_envSum_le Gd hadH hm
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top d))
        hH.ne) h3
    exact ae_lintegral_conv_lt_top mF mG (fin F GF a i hi hF) (fin G GG b j hj hG)
  have h2 : ∀ i : ℕ, ∀ᵐ ξ : Fin r → ℝ, ∀ j : ℕ, i ≤ Λ → j ≤ Λ →
      ∫⁻ η, dsup 0 i (GF.Φ (ξ - η)) * dsup 0 j (GG.Φ η) < ⊤ := by
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hi : i ≤ Λ
    · by_cases hj : j ≤ Λ
      · filter_upwards [h1 i j hi hj] with ξ h using fun _ _ => h
      · exact Eventually.of_forall fun ξ hh hh' => absurd hh' hj
    · exact Eventually.of_forall fun ξ hh hh' => absurd hh hi
  rw [← ae_all_iff] at h2
  filter_upwards [h2] with ξ hξ i j hi hj using hξ i j hi hj

end Deriv

end WaveTurbulence.PL2330
