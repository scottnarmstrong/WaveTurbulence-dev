/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Kink
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication
public import WaveTurbulence.Foundations.Fourier.LinearChange

/-! # D1b-F FOLD 2: two-dimensional kink tensors

`tensor2 u v (x) = u (x 0) v (x 1)` has the transform `oneFT u (ξ 0) · oneFT v (ξ 1)`; with the splitting
`⟨ξ⟩_max^s ≤ (1+|ξ₀|)^s + (1+|ξ₁|)^s` (o82 §17: `⟨(ξ,ζ)⟩^σ ≤ C(⟨ξ⟩^σ + ⟨ζ⟩^σ)`) the tensor of two kink atoms has
`𝔛^s` norm `≤ 2 C_{s,ε} C_{0,ε} R^{s+2ε}` when all four parameters are `≤ R - 1` in size. The shear
`(t,s) ↦ (t - s, s)` (determinant one) changes the norm by at most `2^s`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal Real Matrix

namespace WaveTurbulence.Flower.ProtOpsFold

/-- `u ⊗ v` on `Fin 2 → ℝ`. -/
def tensor2 (u v : ℝ → ℂ) (x : Fin 2 → ℝ) : ℂ := u (x 0) * v (x 1)

theorem integrable_tensor2 {u v : ℝ → ℂ} (hu : Integrable u) (hv : Integrable v) :
    Integrable (tensor2 u v) := by
  have h := Integrable.fintype_prod (f := ![u, v]) (μ := fun _ => (volume : Measure ℝ))
    (fun i => by fin_cases i <;> simpa)
  have he : (fun x : Fin 2 → ℝ => ∏ i, ![u, v] i (x i)) = tensor2 u v := by
    funext x; simp [tensor2, Fin.prod_univ_two]
  rw [← he]; exact h

theorem continuous_tensor2 {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v) :
    Continuous (tensor2 u v) := by
  unfold tensor2; fun_prop

theorem oneFT_eq_vector (g : ℝ → ℂ) :
    oneFT g = VectorFourier.fourierIntegral Real.fourierChar volume (LinearMap.mul ℝ ℝ) g := by
  funext z
  unfold oneFT VectorFourier.fourierIntegral
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [Circle.smul_def]

theorem oneFT_continuous {g : ℝ → ℂ} (hg : Integrable g) : Continuous (oneFT g) := by
  rw [oneFT_eq_vector]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp only [LinearMap.mul_apply']; fun_prop) hg

/-- **Fubini factorization** of the transform of a tensor. -/
theorem timeFourier_tensor2 (u v : ℝ → ℂ) (ξ : Fin 2 → ℝ) :
    timeFourier (tensor2 u v) ξ = oneFT u (ξ 0) * oneFT v (ξ 1) := by
  let F : Fin 2 → ℝ → ℂ := ![fun y => (Real.fourierChar (-(y * ξ 0)) : ℂ) * u y,
    fun y => (Real.fourierChar (-(y * ξ 1)) : ℂ) * v y]
  have h := integral_fin_nat_prod_volume_eq_prod (E := fun _ => ℝ) F
  simp only [Fin.prod_univ_two] at h
  unfold timeFourier VectorFourier.fourierIntegral
  rw [show oneFT u (ξ 0) * oneFT v (ξ 1) = (∫ x, F 0 x) * ∫ x, F 1 x from rfl, ← h]
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  have hp : timePairing 2 t ξ = t 0 * ξ 0 + t 1 * ξ 1 := by
    change t ⬝ᵥ ξ = _
    simp [dotProduct, Fin.sum_univ_two]
  simp only [F, Matrix.cons_val_zero, Matrix.cons_val_one, tensor2, Circle.smul_def, smul_eq_mul]
  rw [hp, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem lintegral_fin2_mul {a b : ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ ξ : Fin 2 → ℝ, a (ξ 0) * b (ξ 1) = (∫⁻ x, a x) * ∫⁻ y, b y := by
  rw [← lintegral_prod_mul ha.aemeasurable hb.aemeasurable, ← Measure.volume_eq_prod]
  exact (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
    (MeasurableEquiv.finTwoArrow).measurableEmbedding (fun p => a p.1 * b p.2)

theorem sqrt_one_add_sq_le (x : ℝ) : Real.sqrt (1 + x ^ 2) ≤ 1 + |x| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs x, abs_nonneg x]

theorem one_add_abs_le_two_sqrt (x : ℝ) : 1 + |x| ≤ 2 * Real.sqrt (1 + x ^ 2) := by
  have h : (1 + |x|) / 2 ≤ Real.sqrt (1 + x ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs x, abs_nonneg x]
  linarith

theorem timeBracket_two_le (ξ : Fin 2 → ℝ) : timeBracket ξ ≤ max (1 + |ξ 0|) (1 + |ξ 1|) := by
  apply timeBracket_le (le_max_of_le_left (by linarith [abs_nonneg (ξ 0)]))
  intro j
  fin_cases j
  · exact (sqrt_one_add_sq_le _).trans (le_max_left _ _)
  · exact (sqrt_one_add_sq_le _).trans (le_max_right _ _)

theorem timeWeight_two_le {s : ℝ} (hs : 0 ≤ s) (ξ : Fin 2 → ℝ) :
    timeWeight s ξ ≤ ENNReal.ofReal ((1 + |ξ 0|) ^ s) + ENNReal.ofReal ((1 + |ξ 1|) ^ s) := by
  unfold timeWeight
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h0 : 0 ≤ (1 + |ξ 0|) ^ s := by positivity
  have h1 : 0 ≤ (1 + |ξ 1|) ^ s := by positivity
  calc timeBracket ξ ^ s ≤ max (1 + |ξ 0|) (1 + |ξ 1|) ^ s :=
        Real.rpow_le_rpow (timeBracket_pos ξ).le (timeBracket_two_le ξ) hs
    _ ≤ (1 + |ξ 0|) ^ s + (1 + |ξ 1|) ^ s := by
        rcases le_total (1 + |ξ 0|) (1 + |ξ 1|) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith

/-- **The tensor norm splitting.** -/
theorem timeFourierNorm_tensor2_le {s : ℝ} (hs : 0 ≤ s) {u v : ℝ → ℂ} (hu : Integrable u)
    (hv : Integrable v) :
    timeFourierNorm s (tensor2 u v) ≤
      (∫⁻ z, ENNReal.ofReal ((1 + |z|) ^ s) * ‖oneFT u z‖ₑ) * (∫⁻ z, ‖oneFT v z‖ₑ) +
      (∫⁻ z, ‖oneFT u z‖ₑ) * (∫⁻ z, ENNReal.ofReal ((1 + |z|) ^ s) * ‖oneFT v z‖ₑ) := by
  rw [timeFourierNorm_eq_lintegral (integrable_tensor2 hu hv)]
  have hmu : Measurable (fun z => ‖oneFT u z‖ₑ) := (oneFT_continuous hu).measurable.enorm
  have hmv : Measurable (fun z => ‖oneFT v z‖ₑ) := (oneFT_continuous hv).measurable.enorm
  have hw : Measurable (fun z : ℝ => ENNReal.ofReal ((1 + |z|) ^ s)) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.add measurable_id.abs).pow_const s)
  calc ∫⁻ ξ, timeWeight s ξ * ‖timeFourier (tensor2 u v) ξ‖ₑ
      ≤ ∫⁻ ξ : Fin 2 → ℝ, (ENNReal.ofReal ((1 + |ξ 0|) ^ s) * ‖oneFT u (ξ 0)‖ₑ) * ‖oneFT v (ξ 1)‖ₑ +
          ‖oneFT u (ξ 0)‖ₑ * (ENNReal.ofReal ((1 + |ξ 1|) ^ s) * ‖oneFT v (ξ 1)‖ₑ) := by
        refine lintegral_mono fun ξ => ?_
        rw [timeFourier_tensor2, enorm_mul]
        calc timeWeight s ξ * (‖oneFT u (ξ 0)‖ₑ * ‖oneFT v (ξ 1)‖ₑ)
            ≤ (ENNReal.ofReal ((1 + |ξ 0|) ^ s) + ENNReal.ofReal ((1 + |ξ 1|) ^ s)) *
                (‖oneFT u (ξ 0)‖ₑ * ‖oneFT v (ξ 1)‖ₑ) := by
              gcongr; exact timeWeight_two_le hs ξ
          _ = _ := by ring
    _ = _ := by
        rw [lintegral_add_left]
        · have e1 := lintegral_fin2_mul (a := fun z => ENNReal.ofReal ((1 + |z|) ^ s) * ‖oneFT u z‖ₑ)
            (b := fun z => ‖oneFT v z‖ₑ) (hw.mul hmu) hmv
          have e2 := lintegral_fin2_mul (a := fun z => ‖oneFT u z‖ₑ)
            (b := fun z => ENNReal.ofReal ((1 + |z|) ^ s) * ‖oneFT v z‖ₑ) hmu (hw.mul hmv)
          beta_reduce at e1 e2
          rw [e1, e2]
        · exact ((hw.mul hmu).comp (measurable_pi_apply 0)).mul (hmv.comp (measurable_pi_apply 1))

theorem exp_neg_abs_le (y : ℝ) : Real.exp (-|y|) ≤ 2 * (1 + |y|) ^ (-(1 + (1 : ℝ))) := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg y)
  have hpos : 0 < 1 + |y| := by positivity
  rw [show -(1 + (1 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_two,
    Real.exp_neg]
  rw [← div_eq_mul_inv, ← one_div]
  rw [div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith [abs_nonneg y]

theorem integrable_kinkAtom (c α β : ℝ) : Integrable (kinkAtom c α β) := by
  refine ((integrable_kinkTail (ε := 1) one_pos c).const_mul 2).mono'
    (kinkAtom_continuous c α β).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_kinkAtom]
  exact exp_neg_abs_le (x - c)

theorem enorm_oneFT_kinkAtom (c α β z : ℝ) :
    ‖oneFT (kinkAtom c α β) z‖ₑ = ‖kinkHat β (z - α)‖ₑ := by
  rw [oneFT_kinkAtom, enorm_mul]
  have : (2 * π * Complex.I * ((α - z) * c) : ℂ) = ((2 * π * ((α - z) * c) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.enorm_exp_ofReal_mul_I, one_mul]

theorem kink_weighted_le' {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hse : s + ε ≤ 1) (c α β R : ℝ)
    (hα : 1 + |α| ≤ R) (hβ : 1 + |β| ≤ R) :
    ∫⁻ z, ENNReal.ofReal ((1 + |z|) ^ s) * ‖oneFT (kinkAtom c α β) z‖ₑ ≤
      ENNReal.ofReal (kinkC s ε * R ^ (s + ε)) := by
  simp_rw [enorm_oneFT_kinkAtom]
  refine (kink_weighted_le hs hε hse α β).trans (ENNReal.ofReal_le_ofReal ?_)
  have := kinkC_nonneg s ε
  gcongr
  exact max_le hα hβ

theorem kink_l1_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c α β R : ℝ)
    (hα : 1 + |α| ≤ R) (hβ : 1 + |β| ≤ R) :
    ∫⁻ z, ‖oneFT (kinkAtom c α β) z‖ₑ ≤ ENNReal.ofReal (kinkC 0 ε * R ^ ε) := by
  have h := kink_weighted_le' (s := 0) le_rfl hε (by linarith) c α β R hα hβ
  simp only [Real.rpow_zero, ENNReal.ofReal_one, one_mul, zero_add] at h
  exact h

/-- The constant of the tensor-kink bound. -/
def kinkKC (s ε : ℝ) : ℝ := 2 * kinkC s ε * kinkC 0 ε

theorem kinkKC_nonneg (s ε : ℝ) : 0 ≤ kinkKC s ε := by
  unfold kinkKC; have := kinkC_nonneg s ε; have := kinkC_nonneg 0 ε; positivity

/-- **The tensor of two kink atoms** has `𝔛^s` norm `≤ C R^{s+2ε}`. -/
theorem tensorKink_norm_le {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hse : s + ε ≤ 1)
    (a0 α0 β0 a1 α1 β1 R : ℝ) (h0 : 1 + |α0| ≤ R) (h1 : 1 + |β0| ≤ R) (h2 : 1 + |α1| ≤ R)
    (h3 : 1 + |β1| ≤ R) :
    timeFourierNorm s (tensor2 (kinkAtom a0 α0 β0) (kinkAtom a1 α1 β1)) ≤
      ENNReal.ofReal (kinkKC s ε * R ^ (s + 2 * ε)) := by
  have hR : 1 ≤ R := le_trans (by linarith [abs_nonneg α0]) h0
  have hε1 : ε ≤ 1 := by linarith
  refine (timeFourierNorm_tensor2_le hs (integrable_kinkAtom _ _ _) (integrable_kinkAtom _ _ _)).trans ?_
  have A0 := kink_weighted_le' hs hε hse a0 α0 β0 R h0 h1
  have A1 := kink_weighted_le' hs hε hse a1 α1 β1 R h2 h3
  have B0 := kink_l1_le hε hε1 a0 α0 β0 R h0 h1
  have B1 := kink_l1_le hε hε1 a1 α1 β1 R h2 h3
  have hC := kinkC_nonneg s ε
  have hC0 := kinkC_nonneg 0 ε
  have hRp : 0 < R := by linarith
  calc _ ≤ ENNReal.ofReal (kinkC s ε * R ^ (s + ε)) * ENNReal.ofReal (kinkC 0 ε * R ^ ε) +
        ENNReal.ofReal (kinkC 0 ε * R ^ ε) * ENNReal.ofReal (kinkC s ε * R ^ (s + ε)) := by
        gcongr
    _ = ENNReal.ofReal (kinkKC s ε * R ^ (s + 2 * ε)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have : R ^ (s + 2 * ε) = R ^ (s + ε) * R ^ ε := by
          rw [← Real.rpow_add hRp]; ring_nf
        rw [this]; unfold kinkKC; ring

/-! ## The shear `(t, s) ↦ (t - s, s)` -/

/-- The shear matrix. -/
def shearM : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 1]

/-- The shear. -/
def shear (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0 - x 1, x 1]

theorem shearM_mulVec (x : Fin 2 → ℝ) : shearM *ᵥ x = shear x := by
  ext i; fin_cases i <;> simp [shearM, shear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

theorem shearM_det : |shearM.det| = 1 := by simp [shearM, Matrix.det_fin_two]

theorem shearMT_det : |shearMᵀ.det| = 1 := by rw [Matrix.det_transpose]; exact shearM_det

theorem matrix_measurePreserving' {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : |A.det| = 1) :
    MeasurePreserving (Matrix.toLin' A) := by
  have hne : A.det ≠ 0 := by intro h; simp [h] at hA
  refine ⟨(Matrix.toLin' A).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hne]
  simp only [abs_inv, hA, inv_one, ENNReal.ofReal_one, one_smul]

theorem matrix_measurableEmbedding' {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : |A.det| = 1) :
    MeasurableEmbedding (Matrix.toLin' A) := by
  have hne : A.det ≠ 0 := by intro h; simp [h] at hA
  let e := A.toLinearEquiv' (A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hne))
  exact e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

theorem timeBracket_shearT_le (ξ : Fin 2 → ℝ) : timeBracket (shearMᵀ *ᵥ ξ) ≤ 2 * timeBracket ξ := by
  have he : shearMᵀ *ᵥ ξ = ξ + ![0, -ξ 0] := by
    ext i; fin_cases i <;> simp [shearM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [he]
  refine (timeBracket_add_le _ _).trans ?_
  have : timeBracket (![0, -ξ 0] : Fin 2 → ℝ) ≤ timeBracket ξ := by
    apply timeBracket_le (one_le_timeBracket ξ)
    intro j; fin_cases j
    · simpa using one_le_timeBracket ξ
    · simpa using bracket_le_timeBracket ξ 0
  linarith

/-- **The shear costs at most `2^s`.** -/
theorem timeFourierNorm_shear_le {s : ℝ} (hs : 0 ≤ s) (f : (Fin 2 → ℝ) → ℂ) :
    timeFourierNorm s (fun x => f (shear x)) ≤ ENNReal.ofReal (2 ^ s) * timeFourierNorm s f := by
  by_cases hf : Integrable f
  · have hcomp : (fun x => f (shear x)) = fun t => f (shearM *ᵥ t) := by
      funext t; rw [shearM_mulVec]
    have hfi : Integrable (fun t => f (shearM *ᵥ t)) := by
      have := ((matrix_measurePreserving' shearM_det).integrable_comp_emb
        (matrix_measurableEmbedding' shearM_det) (g := f)).mpr hf
      simpa [Function.comp_def, Matrix.toLin'_apply] using this
    rw [hcomp, timeFourierNorm_eq_lintegral hfi, timeFourierNorm_eq_lintegral hf]
    rw [← (matrix_measurePreserving' shearMT_det).lintegral_comp_emb
      (matrix_measurableEmbedding' shearMT_det)]
    simp only [Matrix.toLin'_apply, timeFourier_comp_matrix shearM_det]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ => ?_
    rw [← mul_assoc]
    gcongr
    unfold timeWeight
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.mul_rpow (by norm_num) (timeBracket_pos ξ).le]
    exact Real.rpow_le_rpow (timeBracket_pos _).le (timeBracket_shearT_le ξ) hs
  · rw [timeFourierNorm_of_not_integrable hf, ENNReal.mul_top (by simp; positivity)]
    exact le_top

end WaveTurbulence.Flower.ProtOpsFold
