/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.KinkW
public import WaveTurbulence.Foundations.Fourier.TimeFourier

/-! # W2-KIND2 Lemma A (5): the transform and the weighted norm of a product of two one-variable functions

`timeFourier_prod2`: `\hat{F₀ ⊗ F₁}(λ) = fT F₀ (λ₀) · fT F₁ (λ₁)`.
`prod_norm_le`: `‖F₀ ⊗ F₁‖_{𝔛^θ} ≤ N_θ(F₀) N_0(F₁) + N_0(F₀) N_θ(F₁)` for `0 ≤ θ ≤ 1`, with `N_α(F) = ∫⁻ (1+|l|)^α ‖fT F l‖`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology WaveTurbulence.Fourier
open scoped ENNReal

theorem continuous_fT {g : ℝ → ℂ} (hg : Integrable g) : Continuous (fT g) := by
  unfold fT
  refine continuous_of_dominated (bound := fun x => ‖g x‖) (fun l => ?_) (fun l => ?_) hg.norm ?_
  · exact hg.1.mul (continuous_ex l).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by rw [norm_mul, norm_ex, mul_one]
  · exact Eventually.of_forall fun x => by
      unfold ex; fun_prop


theorem fourierChar_pairing2 (t l : Fin 2 → ℝ) :
    ((Real.fourierChar (-(timePairing 2 t l)) : Circle) : ℂ) = ex (l 0) (t 0) * ex (l 1) (t 1) := by
  rw [Real.fourierChar_apply]
  unfold ex
  rw [← Complex.exp_add]
  congr 1
  simp only [timePairing, dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fin.sum_univ_two]
  push_cast
  ring

theorem timeFourier_prod2 {F0 F1 : ℝ → ℂ} (l : Fin 2 → ℝ) :
    timeFourier (fun t : Fin 2 → ℝ => F0 (t 0) * F1 (t 1)) l = fT F0 (l 0) * fT F1 (l 1) := by
  unfold timeFourier VectorFourier.fourierIntegral fT
  have e : ∀ t : Fin 2 → ℝ, (Real.fourierChar (-(timePairing 2 t l)) : Circle) • (F0 (t 0) * F1 (t 1)) =
      (fun z : ℝ × ℝ => (F0 z.1 * ex (l 0) z.1) * (F1 z.2 * ex (l 1) z.2)) ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) t) := by
    intro t
    rw [Circle.smul_def, smul_eq_mul, fourierChar_pairing2]
    have h0 : ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) t).1 = t 0 := rfl
    have h1 : ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) t).2 = t 1 := rfl
    simp only [h0, h1]
    ring
  simp_rw [e]
  rw [(volume_preserving_finTwoArrow ℝ).integral_comp' (g := fun z : ℝ × ℝ => (F0 z.1 * ex (l 0) z.1) * (F1 z.2 * ex (l 1) z.2))]
  exact integral_prod_mul (μ := volume) (ν := volume) (fun x => F0 x * ex (l 0) x) (fun y => F1 y * ex (l 1) y)


/-- The weighted `L¹` norm of the transform of a function of one variable. -/
noncomputable def NN (α : ℝ) (F : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ l, ENNReal.ofReal ((1 + |l|) ^ α) * ‖fT F l‖ₑ

theorem timeBracket_le_two (l : Fin 2 → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    timeBracket l ^ θ ≤ (1 + |l 0|) ^ θ + (1 + |l 1|) ^ θ := by
  have hb : timeBracket l ≤ max (1 + |l 0|) (1 + |l 1|) := by
    unfold timeBracket
    refine Finset.sup'_le _ _ fun i _ => ?_
    rcases i with _ | j
    · exact le_trans (by linarith [abs_nonneg (l 0)]) (le_max_left _ _)
    · have hj : Real.sqrt (1 + l j ^ 2) ≤ 1 + |l j| := by
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        nlinarith [abs_nonneg (l j), sq_abs (l j)]
      fin_cases j
      · exact hj.trans (le_max_left _ _)
      · exact hj.trans (le_max_right _ _)
  have h1 : 0 < timeBracket l := lt_of_lt_of_le one_pos (by
    unfold timeBracket
    exact Finset.le_sup' (fun i : Option (Fin 2) => match i with | none => (1 : ℝ) | some j => Real.sqrt (1 + l j ^ 2)) (Finset.mem_univ none))
  calc timeBracket l ^ θ ≤ (max (1 + |l 0|) (1 + |l 1|)) ^ θ := Real.rpow_le_rpow h1.le hb hθ
    _ ≤ _ := by
        rcases le_total (1 + |l 0|) (1 + |l 1|) with h | h
        · rw [max_eq_right h]; have : 0 ≤ (1 + |l 0|) ^ θ := by positivity
          linarith
        · rw [max_eq_left h]; have : 0 ≤ (1 + |l 1|) ^ θ := by positivity
          linarith


theorem integrable_prod2 {F0 F1 : ℝ → ℂ} (h0 : Integrable F0) (h1 : Integrable F1) :
    Integrable (fun t : Fin 2 → ℝ => F0 (t 0) * F1 (t 1)) := by
  have h := h0.mul_prod h1
  have := (volume_preserving_finTwoArrow ℝ).integrable_comp_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding)
    (g := fun z : ℝ × ℝ => F0 z.1 * F1 z.2)
  exact this.2 h

/-- **The weighted norm of a product.** -/
theorem prod_norm_le {F0 F1 : ℝ → ℂ} (h0 : Integrable F0) (h1 : Integrable F1) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    timeFourierNorm θ (fun t : Fin 2 → ℝ => F0 (t 0) * F1 (t 1)) ≤ NN θ F0 * NN 0 F1 + NN 0 F0 * NN θ F1 := by
  rw [timeFourierNorm_eq_lintegral (integrable_prod2 h0 h1)]
  have hc0 := continuous_fT h0
  have hc1 := continuous_fT h1
  set a0 : ℝ → ℝ≥0∞ := fun x => ‖fT F0 x‖ₑ with ha0
  set a1 : ℝ → ℝ≥0∞ := fun x => ‖fT F1 x‖ₑ with ha1
  have hm0 : Measurable a0 := hc0.measurable.enorm
  have hm1 : Measurable a1 := hc1.measurable.enorm
  have hpt : ∀ l : Fin 2 → ℝ, timeWeight θ l * ‖timeFourier (fun t : Fin 2 → ℝ => F0 (t 0) * F1 (t 1)) l‖ₑ ≤
      (fun z : ℝ × ℝ => (ENNReal.ofReal ((1 + |z.1|) ^ θ) * a0 z.1) * a1 z.2 + a0 z.1 * (ENNReal.ofReal ((1 + |z.2|) ^ θ) * a1 z.2))
        ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) l) := by
    intro l
    rw [timeFourier_prod2, enorm_mul]
    have hw : timeWeight θ l ≤ ENNReal.ofReal ((1 + |l 0|) ^ θ) + ENNReal.ofReal ((1 + |l 1|) ^ θ) := by
      unfold timeWeight
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (timeBracket_le_two l hθ0)
    show timeWeight θ l * (a0 (l 0) * a1 (l 1)) ≤ _
    calc timeWeight θ l * (a0 (l 0) * a1 (l 1)) ≤ (ENNReal.ofReal ((1 + |l 0|) ^ θ) + ENNReal.ofReal ((1 + |l 1|) ^ θ)) * (a0 (l 0) * a1 (l 1)) :=
          mul_le_mul' hw le_rfl
      _ = _ := by
          show _ = (ENNReal.ofReal ((1 + |l 0|) ^ θ) * a0 (l 0)) * a1 (l 1) + a0 (l 0) * (ENNReal.ofReal ((1 + |l 1|) ^ θ) * a1 (l 1))
          ring
  refine (lintegral_mono hpt).trans ?_
  rw [(volume_preserving_finTwoArrow ℝ).lintegral_comp_emb MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun z : ℝ × ℝ => (ENNReal.ofReal ((1 + |z.1|) ^ θ) * a0 z.1) * a1 z.2 + a0 z.1 * (ENNReal.ofReal ((1 + |z.2|) ^ θ) * a1 z.2))]
  have mw0 : Measurable fun x : ℝ => ENNReal.ofReal ((1 + |x|) ^ θ) * a0 x :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun x : ℝ => (1 + |x|) ^ θ)).mul hm0
  have mw1 : Measurable fun x : ℝ => ENNReal.ofReal ((1 + |x|) ^ θ) * a1 x :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun x : ℝ => (1 + |x|) ^ θ)).mul hm1
  rw [Measure.volume_eq_prod, lintegral_add_left]
  · rw [lintegral_prod_mul mw0.aemeasurable hm1.aemeasurable, lintegral_prod_mul hm0.aemeasurable mw1.aemeasurable]
    simp only [NN, ha0, ha1, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    exact le_rfl
  · exact (mw0.comp measurable_fst).mul (hm1.comp measurable_snd)

end WaveTurbulence.VineEstS5C.P4.W2.K2
