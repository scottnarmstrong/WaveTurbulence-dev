/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermLift

/-! # D3-MIRROR: one time tensored with the others, and the three-time kernel of the root trace

* `timeFourierNorm_insert_le`: `‖f(x_i) g(x_{≠i})‖_{A^θ(ℝ^{n+1})} ≤ ‖f‖_{A^θ(ℝ)} ‖g‖_{A^θ(ℝ^n)}` for `θ ≥ 0` and integrable
  factors (Fubini through `MeasurableEquiv.piFinSuccAbove`; `⟨ξ⟩_max ≤ ⟨ξ_i⟩ ⟨ξ_{≠i}⟩_max`).
* `kerH p K W (t,u,s) = χ(t) K(u,s) · W(t,u) χ(s)` (`χ = cut1 p`): the three-time extension of the integrand of the root
  trace (o104 Lemma 7.1(2), (P8)), with `‖kerH‖ ≤ 2^θ ‖χ‖² ‖K‖ ‖W‖` (`kerH_norm_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal FourierTransform

namespace WaveTurbulence.Flower.ProtPin

theorem timeBracket_insert_le {n : ℕ} (i : Fin (n + 1)) (ξ : Fin (n + 1) → ℝ) :
    timeBracket ξ ≤ Sumint.scalarBracket (ξ i) * timeBracket (fun j => ξ (i.succAbove j)) := by
  have h1 := Sumint.one_le_scalarBracket (ξ i)
  have h2 := one_le_timeBracket (fun j => ξ (i.succAbove j))
  apply timeBracket_le (by nlinarith)
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · show Sumint.scalarBracket (ξ j) ≤ _
    nlinarith
  · have := bracket_le_timeBracket (fun j => ξ (i.succAbove j)) k
    nlinarith

theorem timeFourier_insert {n : ℕ} (i : Fin (n + 1)) (φ : ℝ → ℂ) (g : (Fin n → ℝ) → ℂ)
    (ξ : Fin (n + 1) → ℝ) :
    timeFourier (fun x : Fin (n + 1) → ℝ => φ (x i) * g (fun j => x (i.succAbove j))) ξ =
      𝓕 φ (ξ i) * timeFourier g (fun j => ξ (i.succAbove j)) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set η : Fin n → ℝ := fun j => ξ (i.succAbove j) with hη
  unfold timeFourier VectorFourier.fourierIntegral timePairing
  change (∫ x : Fin (n + 1) → ℝ, Real.fourierChar (-(∑ j, x j * ξ j)) •
      (φ (x i) * g (fun j => x (i.succAbove j)))) =
    𝓕 φ (ξ i) * ∫ y : Fin n → ℝ, Real.fourierChar (-(∑ j, y j * η j)) • g y
  rw [Real.fourier_real_eq]
  have key : ∀ x : Fin (n + 1) → ℝ, Real.fourierChar (-(∑ j, x j * ξ j)) •
      (φ (x i) * g (fun j => x (i.succAbove j))) =
      (fun z : ℝ × (Fin n → ℝ) => (Real.fourierChar (-(z.1 * ξ i)) • φ z.1) *
        (Real.fourierChar (-(∑ j, z.2 j * η j)) • g z.2)) (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i x) := by
    intro x
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply, hη]
    rw [show i.removeNth x = fun j => x (i.succAbove j) from rfl]
    rw [Fin.sum_univ_succAbove _ i, neg_add, AddChar.map_add_eq_mul]
    simp only [Circle.smul_def, smul_eq_mul, Circle.coe_mul]
    ring
  simp_rw [key]
  rw [hmp.integral_comp' (fun z : ℝ × (Fin n → ℝ) => (Real.fourierChar (-(z.1 * ξ i)) • φ z.1) *
        (Real.fourierChar (-(∑ j, z.2 j * η j)) • g z.2))]
  exact integral_prod_mul (fun a : ℝ => Real.fourierChar (-(a * ξ i)) • φ a)
    (fun y : Fin n → ℝ => Real.fourierChar (-(∑ j, y j * η j)) • g y)

theorem timeWeight_insert_le {θ : ℝ} (hθ : 0 ≤ θ) {n : ℕ} (i : Fin (n + 1)) (ξ : Fin (n + 1) → ℝ) :
    timeWeight θ ξ ≤ ENNReal.ofReal (Sumint.scalarBracket (ξ i) ^ θ) *
      timeWeight θ (fun j => ξ (i.succAbove j)) := by
  have h0 : 0 ≤ Sumint.scalarBracket (ξ i) := zero_le_one.trans (Sumint.one_le_scalarBracket _)
  have h1 : 0 ≤ timeBracket (fun j => ξ (i.succAbove j)) :=
    zero_le_one.trans (one_le_timeBracket _)
  unfold timeWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h0 _), ← Real.mul_rpow h0 h1]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (zero_le_one.trans (one_le_timeBracket ξ)) (timeBracket_insert_le i ξ) hθ)

/-- **A one-time function tensored with a function of the other times.** -/
theorem timeFourierNorm_insert_le {θ : ℝ} (hθ : 0 ≤ θ) {n : ℕ} (i : Fin (n + 1))
    {f : (Fin 1 → ℝ) → ℂ} {g : (Fin n → ℝ) → ℂ} (hf : Integrable f) (hg : Integrable g) :
    timeFourierNorm θ (fun x : Fin (n + 1) → ℝ => f (fun _ => x i) * g (fun j => x (i.succAbove j))) ≤
      timeFourierNorm θ f * timeFourierNorm θ g := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set φ : ℝ → ℂ := fun y => f (fun _ => y) with hφ
  have hφi : Integrable φ := integrable_lift_one hf
  have hint : Integrable (fun x : Fin (n + 1) → ℝ => φ (x i) * g (fun j => x (i.succAbove j))) := by
    have h2 : Integrable (fun z : ℝ × (Fin n → ℝ) => φ z.1 * g z.2) (volume.prod volume) :=
      hφi.mul_prod hg
    exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h2
  change timeFourierNorm θ (fun x : Fin (n + 1) → ℝ => φ (x i) * g (fun j => x (i.succAbove j))) ≤ _
  rw [timeFourierNorm_eq_lintegral hint, timeFourierNorm_one_eq hf, timeFourierNorm_eq_lintegral hg]
  simp_rw [timeFourier_insert]
  have hb : Measurable (fun x : ℝ => ENNReal.ofReal (Sumint.scalarBracket x ^ θ)) := by
    have : Continuous Sumint.scalarBracket := by unfold Sumint.scalarBracket; fun_prop
    exact (this.measurable.pow_const θ).ennreal_ofReal
  rw [← hφ, ← lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖𝓕 φ x‖ₑ)
    (g := fun y : Fin n → ℝ => timeWeight θ y * ‖timeFourier g y‖ₑ)
    (hb.mul (measurable_fourier_real hφi).enorm).aemeasurable
    ((timeWeight_measurable θ).mul (timeFourier_continuous hg).measurable.enorm).aemeasurable,
    ← Measure.volume_eq_prod, ← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  refine lintegral_mono fun ξ => ?_
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
  rw [show i.removeNth ξ = fun j => ξ (i.succAbove j) from rfl, enorm_mul]
  calc timeWeight θ ξ * (‖𝓕 φ (ξ i)‖ₑ * ‖timeFourier g (fun j => ξ (i.succAbove j))‖ₑ)
      ≤ (ENNReal.ofReal (Sumint.scalarBracket (ξ i) ^ θ) * timeWeight θ (fun j => ξ (i.succAbove j))) *
          (‖𝓕 φ (ξ i)‖ₑ * ‖timeFourier g (fun j => ξ (i.succAbove j))‖ₑ) := by
        gcongr
        exact timeWeight_insert_le hθ i ξ
    _ = _ := by ring


theorem timeFourierNorm_lift_first {θ : ℝ} (hθ : 0 ≤ θ) {f : (Fin 1 → ℝ) → ℂ} {g : (Fin 2 → ℝ) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    timeFourierNorm θ (fun x : Fin 3 → ℝ => f (fun _ => x 0) * g ![x 1, x 2]) ≤
      timeFourierNorm θ f * timeFourierNorm θ g := by
  have e : (fun x : Fin 3 → ℝ => f (fun _ => x 0) * g ![x 1, x 2]) =
      fun x => f (fun _ => x 0) * g (fun j => x ((0 : Fin 3).succAbove j)) := by
    funext x
    congr 2
    funext j
    fin_cases j <;> rfl
  rw [e]
  exact timeFourierNorm_insert_le hθ 0 hf hg

theorem timeFourierNorm_lift_last {θ : ℝ} (hθ : 0 ≤ θ) {f : (Fin 1 → ℝ) → ℂ} {g : (Fin 2 → ℝ) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    timeFourierNorm θ (fun x : Fin 3 → ℝ => g ![x 0, x 1] * f (fun _ => x 2)) ≤
      timeFourierNorm θ g * timeFourierNorm θ f := by
  have e : (fun x : Fin 3 → ℝ => g ![x 0, x 1] * f (fun _ => x 2)) =
      fun x => f (fun _ => x 2) * g (fun j => x ((2 : Fin 3).succAbove j)) := by
    funext x
    rw [mul_comm]
    congr 2
    funext j
    fin_cases j <;> rfl
  rw [e, mul_comm (timeFourierNorm θ g)]
  exact timeFourierNorm_insert_le hθ 2 hf hg

theorem continuous_cut1 (a : ℝ) : Continuous (cut1 a) := by
  unfold cut1
  exact (coordinateCutoff_contDiff Layered.chiUnit_contDiff).continuous.comp (by fun_prop)

theorem integrable_cut1 (θ a : ℝ) : Integrable (cut1 a) :=
  integrable_of_timeFourierNorm_lt_top (θ := θ) (by rw [cut1_norm]; exact cutNorm_lt_top θ)

/-- The three-time kernel `H(t, u, s) = χ(t) K(u, s) · W(t, u) χ(s)` of the root trace. -/
def kerH (p : ℝ) (K W : (Fin 2 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  (cut1 p (fun _ => x 0) * K ![x 1, x 2]) * (W ![x 0, x 1] * cut1 p (fun _ => x 2))

/-- **The norm of the three-time kernel.** -/
theorem kerH_norm_le {θ : ℝ} (hθ : 0 ≤ θ) (p : ℝ) {K W : (Fin 2 → ℝ) → ℂ} (hW : Continuous W)
    (hK : timeFourierNorm θ K < ⊤) (hWn : timeFourierNorm θ W < ⊤) :
    timeFourierNorm θ (kerH p K W) ≤
      ENNReal.ofReal (2 ^ θ) * cutNorm θ ^ 2 * timeFourierNorm θ K * timeFourierNorm θ W := by
  have hc1 := integrable_cut1 θ p
  have h1 := timeFourierNorm_lift_first hθ hc1 (integrable_of_timeFourierNorm_lt_top hK)
  have h2 := timeFourierNorm_lift_last hθ hc1 (integrable_of_timeFourierNorm_lt_top hWn)
  rw [cut1_norm] at h1 h2
  have h1f := h1.trans_lt (ENNReal.mul_lt_top (cutNorm_lt_top θ) hK)
  have h2f := h2.trans_lt (ENNReal.mul_lt_top hWn (cutNorm_lt_top θ))
  have hc : Continuous (fun x : Fin 3 → ℝ => W ![x 0, x 1] * cut1 p (fun _ => x 2)) :=
    (hW.comp (by fun_prop)).mul ((continuous_cut1 p).comp (by fun_prop))
  refine (timeFourierNorm_mul_le (f := fun x : Fin 3 → ℝ => cut1 p (fun _ => x 0) * K ![x 1, x 2])
    (g := fun x : Fin 3 → ℝ => W ![x 0, x 1] * cut1 p (fun _ => x 2)) hθ hc h1f h2f).trans ?_
  calc ENNReal.ofReal (2 ^ θ) *
        timeFourierNorm θ (fun x : Fin 3 → ℝ => cut1 p (fun _ => x 0) * K ![x 1, x 2]) *
        timeFourierNorm θ (fun x : Fin 3 → ℝ => W ![x 0, x 1] * cut1 p (fun _ => x 2))
      ≤ ENNReal.ofReal (2 ^ θ) * (cutNorm θ * timeFourierNorm θ K) * (timeFourierNorm θ W * cutNorm θ) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
