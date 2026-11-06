/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Regref.TraceDeriv

/-!
# Regularized Fourier transforms for the derivative norms `𝔛^{θ,Λ,Λ₂}` (PL23-30D)

For `F` of finite norm `mixedFourierNorm θ Λ Λ₂ F` (`Λ ≥ 1`) the transform `ξ ↦ F̂(ξ, ·)` is `C^Λ` in `k` only
for almost every `ξ`. `Good Λ F` is a regularization `Φ`: smooth in `k` for every `ξ`, measurable in `ξ` for
every `k`, and almost everywhere equal to `F̂`. Its weighted word envelopes are measurable, so that the
integrals `∫⁻ w · env` are genuine integrals and are subadditive. This is the measurability of F80 for the
snapshot-9 `XNorm`.

* `Good`, `Good.exists`;
* `measurable_envW`: the envelopes `ξ ↦ ‖⟨k⟩^{Λ₂} ∂^ρ Φ(ξ,k)‖_{L^∞_k}` are measurable;
* `mixedFourierNorm_le_of_bound`: a bound of the norm by a.e. pointwise bounds of the envelopes of `F̂`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

/-- The integral `∫⁻ w_θ(ξ) · ‖⟨k⟩^{Λ₂} ∂^ρ Φ(ξ,k)‖_{L^∞_k}`. -/
noncomputable def nInt (θ : ℝ) (Λ₂ : ℕ) {n : ℕ} (ρ : Fin n → Fin d)
    (Φ : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm Λ₂ (momentumDerivative ρ (Φ ξ))

theorem continuous_momentumBracket : Continuous fun k : Mom d => momentumBracket k := by
  unfold momentumBracket
  fun_prop

theorem momentumBracket_nonneg (k : Mom d) : 0 ≤ momentumBracket k := Real.sqrt_nonneg _

/-- The weighted word envelope of a family `C^Λ` in `k` and measurable in `ξ` is measurable in `ξ`. -/
theorem measurable_envW {Λ : ℕ} {Φ : (Fin r → ℝ) → Mom d → ℂ} (Λ₂ : ℕ)
    (hs : ∀ ξ, ContDiff ℝ Λ (Φ ξ)) (hm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k)
    {n : ℕ} (hn : n ≤ Λ) (ρ : Fin n → Fin d) :
    Measurable fun ξ => momentumSupNorm Λ₂ (momentumDerivative ρ (Φ ξ)) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (Mom d)
  have : Countable D := hDc.to_subtype
  have he : (fun ξ => momentumSupNorm Λ₂ (momentumDerivative ρ (Φ ξ))) =
      fun ξ => ⨆ q : D, ENNReal.ofReal (momentumBracket q.1 ^ Λ₂) *
        ‖momentumDerivative ρ (Φ ξ) q.1‖ₑ := by
    funext ξ
    unfold momentumSupNorm
    have hco : Continuous fun k : Mom d => ENNReal.ofReal (momentumBracket k ^ Λ₂) *
        ‖momentumDerivative ρ (Φ ξ) k‖ₑ := by
      have h1 : (fun k : Mom d => ENNReal.ofReal (momentumBracket k ^ Λ₂) *
          ‖momentumDerivative ρ (Φ ξ) k‖ₑ) =
          fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂ * ‖momentumDerivative ρ (Φ ξ) k‖) := by
        funext k
        rw [ENNReal.ofReal_mul (pow_nonneg (momentumBracket_nonneg k) _), ofReal_norm]
      rw [h1]
      exact ENNReal.continuous_ofReal.comp
        ((continuous_momentumBracket.pow Λ₂).mul
          (continuous_norm.comp (continuous_momentumDerivative hn ρ (hs ξ))))
    exact iSup_eq_iSup_dense hD hco
  rw [he]
  refine Measurable.iSup fun q => ?_
  have hsm := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => Φ ξ k) hs hm n hn q.1
  exact measurable_const.mul
    (((continuous_eval_const (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))).comp_stronglyMeasurable
      hsm).measurable).enorm

/-- A regularization of the Fourier transform of `F`: `C^Λ` in `k` for every `ξ`, strongly measurable in `ξ`,
and almost everywhere equal to `ξ ↦ F̂(ξ, ·)`. -/
structure Good (Λ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) where
  Φ : (Fin r → ℝ) → Mom d → ℂ
  smooth : ∀ ξ, ContDiff ℝ Λ (Φ ξ)
  meas : ∀ k, StronglyMeasurable fun ξ => Φ ξ k
  ae : ∀ᵐ ξ, Φ ξ = mixedTimeFourier F ξ

/-- Admissible families with `C^Λ` transforms almost everywhere have a regularization. -/
theorem Good.exists {Λ : ℕ} {F : (Fin r → ℝ) → Mom d → ℂ} (hiF : ∀ k, Integrable fun t => F t k)
    (hsm : ∀ᵐ ξ, ContDiff ℝ Λ (mixedTimeFourier F ξ)) : Nonempty (Good Λ F) := by
  classical
  obtain ⟨N, hNsup, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hsm)
  set S := Nᶜ with hS
  have hSm : MeasurableSet S := hNm.compl
  have haeS : ∀ᵐ ξ ∂(volume : Measure (Fin r → ℝ)), ξ ∈ S :=
    measure_mono_null (fun ξ hξ => by simpa [hS] using hξ) hN0
  have hSsm : ∀ ξ ∈ S, ContDiff ℝ Λ (mixedTimeFourier F ξ) := fun ξ hξ => by
    by_contra h
    exact hξ (hNsup h)
  refine ⟨⟨fun ξ => if ξ ∈ S then mixedTimeFourier F ξ else fun _ => 0, fun ξ => ?_, fun k => ?_, ?_⟩⟩
  · by_cases hξ : ξ ∈ S
    · simp only [hξ, ite_true]; exact hSsm ξ hξ
    · simp only [hξ, ite_false]; exact contDiff_const
  · have : (fun ξ => (if ξ ∈ S then mixedTimeFourier F ξ else fun _ => (0 : ℂ)) k) =
        S.indicator (fun ξ => mixedTimeFourier F ξ k) := by
      funext ξ
      by_cases hξ : ξ ∈ S <;> simp [hξ]
    rw [this]
    exact ((timeFourier_continuous (hiF k)).stronglyMeasurable).indicator hSm
  · filter_upwards [haeS] with ξ hξ
    simp [hξ]

namespace Good

variable {Λ : ℕ} {F : (Fin r → ℝ) → Mom d → ℂ} (G : Good Λ F)

theorem env_meas (Λ₂ : ℕ) {n : ℕ} (hn : n ≤ Λ) (ρ : Fin n → Fin d) :
    Measurable fun ξ => momentumSupNorm Λ₂ (momentumDerivative ρ (G.Φ ξ)) :=
  measurable_envW Λ₂ G.smooth G.meas hn ρ

theorem env_ae (Λ₂ : ℕ) {n : ℕ} (ρ : Fin n → Fin d) :
    ∀ᵐ ξ, momentumSupNorm Λ₂ (momentumDerivative ρ (G.Φ ξ)) =
      momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier F ξ)) := by
  filter_upwards [G.ae] with ξ hξ
  rw [hξ]

theorem nInt_eq (θ : ℝ) (Λ₂ : ℕ) {n : ℕ} (ρ : Fin n → Fin d) :
    nInt θ Λ₂ ρ G.Φ = ∫⁻ ξ, timeWeight θ ξ *
      momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier F ξ)) := by
  unfold nInt
  refine lintegral_congr_ae ?_
  filter_upwards [G.env_ae Λ₂ ρ] with ξ hξ
  rw [hξ]

end Good

/-- **A bound of the norm by almost-everywhere bounds of the envelopes of `F̂`.** -/
theorem mixedFourierNorm_le_of_bound {θ : ℝ} {Λ Λ₂ : ℕ} {H : (Fin r → ℝ) → Mom d → ℂ}
    (hadm : MixedFourierAdmissible Λ H) (B : (n : ℕ) → (Fin n → Fin d) → (Fin r → ℝ) → ℝ≥0∞)
    (hB : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∀ᵐ ξ,
      momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier H ξ)) ≤ B n ρ ξ) {M : ℝ≥0∞}
    (hM : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, timeWeight θ ξ * B n ρ ξ ≤ M) :
    mixedFourierNorm θ Λ Λ₂ H ≤ M := by
  rw [mixedFourierNorm_eq_iSup hadm]
  refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
  refine le_trans ?_ (hM n hn ρ)
  refine lintegral_mono_ae ?_
  filter_upwards [hB n hn ρ] with ξ hξ
  exact mul_le_mul_right hξ _

/-- Finite norm gives admissibility. -/
theorem admissible_of_lt_top {θ : ℝ} {Λ Λ₂ : ℕ} {H : (Fin r → ℝ) → Mom d → ℂ}
    (h : mixedFourierNorm θ Λ Λ₂ H < ⊤) : MixedFourierAdmissible Λ H :=
  mixedFourierAdmissible_of_lt_top h

/-- The word integrals of the regularization are bounded by the norm. -/
theorem Good.nInt_le {θ : ℝ} {Λ Λ₂ : ℕ} {H : (Fin r → ℝ) → Mom d → ℂ}
    (G : Good Λ H) (hadm : MixedFourierAdmissible Λ H) {n : ℕ} (hn : n ≤ Λ) (ρ : Fin n → Fin d) :
    nInt θ Λ₂ ρ G.Φ ≤ mixedFourierNorm θ Λ Λ₂ H := by
  rw [G.nInt_eq, mixedFourierNorm_eq_iSup hadm]
  exact le_iSup₂_of_le n hn (le_iSup (fun ρ : Fin n → Fin d =>
    ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier H ξ))) ρ)

/-- A finite-norm family has a regularization (`Λ ≥ 1`). -/
theorem exists_good {θ : ℝ} {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) {H : (Fin r → ℝ) → Mom d → ℂ}
    (h : mixedFourierNorm θ Λ Λ₂ H < ⊤) : Nonempty (Good Λ H) := by
  have hadm := admissible_of_lt_top h
  exact Good.exists hadm.1 (hadm.2.resolve_left hΛ)

end WaveTurbulence.PL2330
