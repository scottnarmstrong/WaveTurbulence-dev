/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.TermBounds
public import WaveTurbulence.Foundations.NTSP.SingularInt
public import WaveTurbulence.Foundations.WKE.Hyperplane

/-!
# Hyperplane slices of the localized amplitude (DH23 Lemma 6.7)

For `x ≠ 0` write `y = t x/|x| + w`, `w ⊥ x` (`WKE.sliceEquiv`), so `⟨x, y⟩ = t |x|`. For the
amplitude `F(x,y) = χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y)` the slice integrals
`S_x(t) = ∫_{x^⊥} F(x, t x/|x| + w) dw` satisfy (`norm_slice_le`, `norm_slice_sub_le`)

  `|S_x(t)| ≤ C D λ^d |χ₀((x-a)/λ)|`, `|S_x(t) - S_x(t')| ≤ C D (1 + |ζ|) λ^d |χ₀((x-a)/λ)| |t - t'|`,

using only `|Φ| ≤ D`, `|∇_y Φ| ≤ D` and the support of the cutoffs.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped InnerProductSpace

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- The amplitude of DH23 Lemma 6.7: `χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y)`. -/
@[expose] def amp (lam : ℝ) (Φ : Mom d → Mom d → ℂ) (a b ξ ζ : Mom d) (x y : Mom d) : ℂ :=
  chiScaled lam (x - a) * chiScaled lam (y - b) * Φ x y *
    (Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ) : ℂ)

theorem norm_fourierChar_sub_le (s s' : ℝ) :
    ‖(Real.fourierChar s : ℂ) - Real.fourierChar s'‖ ≤ 2 * Real.pi * |s - s'| := by
  have h : (Real.fourierChar s : ℂ) - Real.fourierChar s' =
      Real.fourierChar s' * (Real.fourierChar (s - s') - 1) := by
    rw [mul_sub, mul_one, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_sub_cancel]
  rw [h, norm_mul, Circle.norm_coe, one_mul, Real.fourierChar_apply, mul_comm _ Complex.I]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem norm_chiScaled_sub_le {lam : ℝ} (hlam : 1 ≤ lam) (b y y' : Mom d) :
    ‖chiScaled lam (y - b) - chiScaled lam (y' - b)‖ ≤ chiDerivConst d 1 * ‖y - y'‖ := by
  have hdiff : Differentiable ℝ (fun y => chiScaled lam (y - b)) :=
    ((contDiff_chiScaled lam).comp (contDiff_id.sub contDiff_const)).differentiable (by simp)
  refine convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
    (fun z _ => ?_) (Set.mem_univ y') (Set.mem_univ y)
  rw [← norm_iteratedFDeriv_one]
  exact norm_iteratedFDeriv_chiScaled_le hlam b 1 z

theorem norm_amp_le {N : ℕ} {D lam : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ)
    (a b ξ ζ x y : Mom d) :
    ‖amp lam Φ a b ξ ζ x y‖ ≤ D * ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖ := by
  rw [amp, norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one]
  have := hΦ.norm_le x y
  calc ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖ * ‖Φ x y‖
      ≤ ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖ * D := by gcongr
    _ = _ := by ring

/-- The Lipschitz constant of `y ↦ F(x,y)/χ₀((x-a)/λ)`. -/
@[expose] def ampLip (d : ℕ) (D : ℝ) (ζ : Mom d) : ℝ :=
  D * (chiDerivConst d 1 + 1 + 2 * Real.pi * ‖ζ‖)

theorem ampLip_nonneg (d : ℕ) {D : ℝ} (hD : 0 ≤ D) (ζ : Mom d) : 0 ≤ ampLip d D ζ := by
  unfold ampLip; have := chiDerivConst_nonneg d 1; positivity

theorem norm_amp_sub_le {N : ℕ} (hN : 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ x y y' : Mom d) :
    ‖amp lam Φ a b ξ ζ x y - amp lam Φ a b ξ ζ x y'‖ ≤
      ‖chiScaled lam (x - a)‖ * ampLip d D ζ * ‖y - y'‖ := by
  have hD := hΦ.nonneg
  set cx := chiScaled lam (x - a)
  set ex : ℂ := ((Real.fourierChar (inner ℝ x ξ) : Circle) : ℂ)
  have hex : ‖ex‖ = 1 := Circle.norm_coe _
  have he : ∀ y, amp lam Φ a b ξ ζ x y = cx * ex *
      (chiScaled lam (y - b) * Φ x y * (Real.fourierChar (inner ℝ y ζ) : ℂ)) := fun y => by
    simp only [amp, cx, ex, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  rw [he, he, ← mul_sub, norm_mul, norm_mul, hex, mul_one, mul_assoc ‖cx‖ (ampLip d D ζ)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg cx)
  set c := chiScaled lam (y - b)
  set c' := chiScaled lam (y' - b)
  set e : ℂ := ((Real.fourierChar (inner ℝ y ζ) : Circle) : ℂ)
  set e' : ℂ := ((Real.fourierChar (inner ℝ y' ζ) : Circle) : ℂ)
  have hc' : ‖c'‖ ≤ 1 := norm_chiScaled_le_one lam _
  have he' : ‖e‖ = 1 := Circle.norm_coe _
  have h1 := norm_chiScaled_sub_le hlam b y y'
  have h2 := hΦ.norm_sub_le_right hN x y y'
  have h3 : ‖e - e'‖ ≤ 2 * Real.pi * ‖ζ‖ * ‖y - y'‖ := by
    refine (norm_fourierChar_sub_le _ _).trans ?_
    have hi : |inner ℝ y ζ - inner ℝ y' ζ| ≤ ‖ζ‖ * ‖y - y'‖ := by
      rw [← inner_sub_left]
      exact (abs_real_inner_le_norm (y - y') ζ).trans_eq (mul_comm _ _)
    calc 2 * Real.pi * |inner ℝ y ζ - inner ℝ y' ζ| ≤ 2 * Real.pi * (‖ζ‖ * ‖y - y'‖) := by
          gcongr
      _ = 2 * Real.pi * ‖ζ‖ * ‖y - y'‖ := by ring
  have hΦy := hΦ.norm_le x y'
  have hΦy' := hΦ.norm_le x y
  have hkey : c * Φ x y * e - c' * Φ x y' * e' =
      (c - c') * Φ x y * e + c' * (Φ x y - Φ x y') * e + c' * Φ x y' * (e - e') := by ring
  rw [hkey]
  calc ‖(c - c') * Φ x y * e + c' * (Φ x y - Φ x y') * e + c' * Φ x y' * (e - e')‖
      ≤ ‖(c - c') * Φ x y * e‖ + ‖c' * (Φ x y - Φ x y') * e‖ + ‖c' * Φ x y' * (e - e')‖ :=
        norm_add₃_le
    _ ≤ chiDerivConst d 1 * ‖y - y'‖ * D * 1 + 1 * (D * ‖y - y'‖) * 1 +
          1 * D * (2 * Real.pi * ‖ζ‖ * ‖y - y'‖) := by
        have hcd := chiDerivConst_nonneg d 1
        simp only [norm_mul, he']
        gcongr
    _ = ampLip d D ζ * ‖y - y'‖ := by unfold ampLip; ring

/-! ### Slicing -/

/-- Slicing formula for complex integrands: `∫ g = ∫_ℝ ∫_{ℓ^⊥} g(t ℓ/|ℓ| + w) dw dt`. -/
theorem integral_eq_integral_slice_complex {ℓ : Mom d} (hℓ : ℓ ≠ 0) {g : Mom d → ℂ}
    (hg : Integrable g) :
    ∫ x, g x = ∫ t : ℝ, ∫ w : ↥(ℝ ∙ ℓ)ᗮ, g (t • unitVec ℓ + w) := by
  have hmp := measurePreserving_sliceEquiv hℓ
  rw [← hmp.integral_comp' g]
  have hint : Integrable (g ∘ sliceEquiv hℓ) (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) :=
    hmp.integrable_comp_emb (sliceEquiv hℓ).measurableEmbedding |>.mpr hg
  rw [show (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) = volume.prod volume from rfl] at hint ⊢
  have h := integral_prod _ hint
  simp only [Function.comp_def, sliceEquiv_apply] at h
  simp only [sliceEquiv_apply]
  exact h

theorem lintegral_eq_lintegral_slice {ℓ : Mom d} (hℓ : ℓ ≠ 0) {g : Mom d → ENNReal}
    (hg : Measurable g) :
    ∫⁻ x, g x = ∫⁻ t : ℝ, ∫⁻ w : ↥(ℝ ∙ ℓ)ᗮ, g (t • unitVec ℓ + w) := by
  have hmp := measurePreserving_sliceEquiv hℓ
  rw [← hmp.lintegral_comp_emb (sliceEquiv hℓ).measurableEmbedding g]
  rw [show (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) = volume.prod volume from rfl,
    lintegral_prod (fun p => g (sliceEquiv hℓ p)) (hg.comp (sliceEquiv hℓ).measurable).aemeasurable]
  simp only [sliceEquiv_apply]

theorem inner_slice {ℓ : Mom d} (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    inner ℝ ℓ (t • unitVec ℓ + (w : Mom d)) = t * ‖ℓ‖ := by
  rw [inner_add_right, inner_smul_right, inner_unitVec_self, inner_eq_zero_of_mem_perp w, add_zero]

/-! ### Slice bounds -/

theorem norm_chiScaled_le_decay {lam : ℝ} (hlam : 0 < lam) (b y : Mom d) :
    ‖chiScaled lam (y - b)‖ ≤
      (1 + lam * Real.sqrt d) ^ (d : ℝ) * (1 + ‖y - b‖) ^ (-(d : ℝ)) := by
  by_cases hy : chiScaled lam (y - b) = 0
  · rw [hy, norm_zero]; positivity
  · have h1 := norm_le_of_chiScaled_ne_zero hlam hy
    have h2 : 1 ≤ (1 + lam * Real.sqrt d) ^ (d : ℝ) * (1 + ‖y - b‖) ^ (-(d : ℝ)) := by
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, one_le_div (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    exact (norm_chiScaled_le_one lam _).trans h2

/-- The slice integral `S_x(t) = ∫_{x^⊥} F(x, t x/|x| + w) dw`. -/
@[expose] def sliceAmp (lam : ℝ) (Φ : Mom d → Mom d → ℂ) (a b ξ ζ x : Mom d) (t : ℝ) : ℂ :=
  ∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x (t • unitVec x + w)

/-- The slice constant `(1 + λ√d)^d ∫_{ℝ^{d-1}} (1+|w|)^{-d}`. -/
@[expose] def sliceConst (d : ℕ) (lam : ℝ) : ℝ :=
  (1 + lam * Real.sqrt d) ^ (d : ℝ) * hypConst d d

theorem sliceConst_nonneg (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ sliceConst d lam := by
  unfold sliceConst; have := hypConst_nonneg d d; positivity

theorem integrable_decay_slice {x : Mom d} (hx : x ≠ 0) (b : Mom d) (t : ℝ) :
    Integrable (fun w : ↥(ℝ ∙ x)ᗮ => (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) := by
  have h := integrable_one_add_norm_slice hx (M := d) (by linarith) (by positivity) (-b) t
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only
  congr 3
  abel

theorem integral_decay_slice_le {x : Mom d} (hx : x ≠ 0) (b : Mom d) (t : ℝ) :
    ∫ w : ↥(ℝ ∙ x)ᗮ, (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ)) ≤ hypConst d d := by
  have h := integral_one_add_norm_slice_le hx (M := d) (by linarith) (by positivity) (-b) t
  refine le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)) h
  simp only
  congr 3
  abel

theorem continuous_amp {N : ℕ} (hN : 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (a b ξ ζ : Mom d) :
    Continuous (fun p : Mom d × Mom d => amp lam Φ a b ξ ζ p.1 p.2) := by
  have h1 := (contDiff_chiScaled (d := d) lam).continuous
  have hfst : Continuous fun p : Mom d × Mom d => p.1 := continuous_fst
  have hsnd : Continuous fun p : Mom d × Mom d => p.2 := continuous_snd
  exact (((h1.comp (hfst.sub continuous_const)).mul (h1.comp (hsnd.sub continuous_const))).mul
    (hΦ.continuous hN)).mul (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      ((hfst.inner continuous_const).add (hsnd.inner continuous_const))))

theorem integrable_slice_amp {N : ℕ} (hN : 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 0 < lam) (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0) (t : ℝ) :
    Integrable (fun w : ↥(ℝ ∙ x)ᗮ => amp lam Φ a b ξ ζ x (t • unitVec x + w)) := by
  have hD := hΦ.nonneg
  refine ((integrable_decay_slice hx b t).const_mul
    (D * ‖chiScaled lam (x - a)‖ * (1 + lam * Real.sqrt d) ^ (d : ℝ))).mono' ?_
    (Filter.Eventually.of_forall fun w => ?_)
  · exact ((continuous_amp hN hΦ a b ξ ζ).comp (continuous_const.prodMk
      (continuous_const.add continuous_subtype_val))).aestronglyMeasurable
  · refine (norm_amp_le hΦ a b ξ ζ x _).trans ?_
    have := norm_chiScaled_le_decay hlam b (t • unitVec x + (w : Mom d))
    calc D * ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (t • unitVec x + (w : Mom d) - b)‖
        ≤ D * ‖chiScaled lam (x - a)‖ * ((1 + lam * Real.sqrt d) ^ (d : ℝ) *
            (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) := by gcongr
      _ = _ := by ring

/-- `|S_x(t)| ≤ D |χ₀((x-a)/λ)| sliceConst`. -/
theorem norm_sliceAmp_le {N : ℕ} {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 0 < lam) (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0) (t : ℝ) :
    ‖sliceAmp lam Φ a b ξ ζ x t‖ ≤ D * ‖chiScaled lam (x - a)‖ * sliceConst d lam := by
  have hD := hΦ.nonneg
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint := (integrable_decay_slice hx b t).const_mul
    (D * ‖chiScaled lam (x - a)‖ * (1 + lam * Real.sqrt d) ^ (d : ℝ))
  calc ∫ w : ↥(ℝ ∙ x)ᗮ, ‖amp lam Φ a b ξ ζ x (t • unitVec x + w)‖
      ≤ ∫ w : ↥(ℝ ∙ x)ᗮ, D * ‖chiScaled lam (x - a)‖ * (1 + lam * Real.sqrt d) ^ (d : ℝ) *
          (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall fun w => ?_)
        refine (norm_amp_le hΦ a b ξ ζ x _).trans ?_
        have := norm_chiScaled_le_decay hlam b (t • unitVec x + (w : Mom d))
        calc D * ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (t • unitVec x + (w : Mom d) - b)‖
            ≤ D * ‖chiScaled lam (x - a)‖ * ((1 + lam * Real.sqrt d) ^ (d : ℝ) *
                (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) := by gcongr
          _ = _ := by ring
    _ = D * ‖chiScaled lam (x - a)‖ * (1 + lam * Real.sqrt d) ^ (d : ℝ) *
          ∫ w : ↥(ℝ ∙ x)ᗮ, (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ)) :=
        integral_const_mul _ _
    _ ≤ D * ‖chiScaled lam (x - a)‖ * (1 + lam * Real.sqrt d) ^ (d : ℝ) * hypConst d d := by
        gcongr
        exact integral_decay_slice_le hx b t
    _ = _ := by unfold sliceConst; ring

/-- The support-refined Lipschitz bound of the amplitude in `y`. -/
theorem norm_amp_sub_le_decay {N : ℕ} (hN : 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ x y y' : Mom d) :
    ‖amp lam Φ a b ξ ζ x y - amp lam Φ a b ξ ζ x y'‖ ≤
      ‖chiScaled lam (x - a)‖ * ampLip d D ζ * ‖y - y'‖ * ((1 + lam * Real.sqrt d) ^ (d : ℝ) *
        ((1 + ‖y - b‖) ^ (-(d : ℝ)) + (1 + ‖y' - b‖) ^ (-(d : ℝ)))) := by
  have h0 : 0 < lam := by linarith
  have hD := hΦ.nonneg
  have hK : 0 ≤ ‖chiScaled lam (x - a)‖ * ampLip d D ζ * ‖y - y'‖ := by
    have := ampLip_nonneg d hD ζ; positivity
  by_cases hy : chiScaled lam (y - b) = 0 ∧ chiScaled lam (y' - b) = 0
  · have e1 : amp lam Φ a b ξ ζ x y = 0 := by simp [amp, hy.1]
    have e2 : amp lam Φ a b ξ ζ x y' = 0 := by simp [amp, hy.2]
    rw [e1, e2, sub_zero, norm_zero]
    positivity
  · refine (norm_amp_sub_le hN hΦ hlam a b ξ ζ x y y').trans (le_mul_of_one_le_right hK ?_)
    have hm : ∀ z, chiScaled lam (z - b) ≠ 0 →
        1 ≤ (1 + lam * Real.sqrt d) ^ (d : ℝ) * (1 + ‖z - b‖) ^ (-(d : ℝ)) := fun z hz => by
      have h1 := norm_le_of_chiScaled_ne_zero h0 hz
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, one_le_div (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    rw [mul_add]
    rcases not_and_or.1 hy with h | h
    · have := hm y h
      have : 0 ≤ (1 + lam * Real.sqrt d) ^ (d : ℝ) * (1 + ‖y' - b‖) ^ (-(d : ℝ)) := by positivity
      linarith
    · have := hm y' h
      have : 0 ≤ (1 + lam * Real.sqrt d) ^ (d : ℝ) * (1 + ‖y - b‖) ^ (-(d : ℝ)) := by positivity
      linarith

/-- `|S_x(t) - S_x(t')| ≤ 2 |χ₀((x-a)/λ)| Lip sliceConst |t - t'|`. -/
theorem norm_sliceAmp_sub_le {N : ℕ} (hN : 1 ≤ N) {D lam : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0)
    (t t' : ℝ) :
    ‖sliceAmp lam Φ a b ξ ζ x t - sliceAmp lam Φ a b ξ ζ x t'‖ ≤
      2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam * |t - t'| := by
  have h0 : 0 < lam := by linarith
  have hD := hΦ.nonneg
  have hu : ‖unitVec x‖ = 1 := norm_unitVec hx
  rw [sliceAmp, sliceAmp, ← integral_sub (integrable_slice_amp hN hΦ h0 a b ξ ζ hx t)
    (integrable_slice_amp hN hΦ h0 a b ξ ζ hx t')]
  refine (norm_integral_le_integral_norm _).trans ?_
  set K := ‖chiScaled lam (x - a)‖ * ampLip d D ζ * |t - t'| * (1 + lam * Real.sqrt d) ^ (d : ℝ)
  have hK : 0 ≤ K := by have := ampLip_nonneg d hD ζ; positivity
  have hint := ((integrable_decay_slice hx b t).add (integrable_decay_slice hx b t')).const_mul K
  calc ∫ w : ↥(ℝ ∙ x)ᗮ, ‖amp lam Φ a b ξ ζ x (t • unitVec x + w) -
        amp lam Φ a b ξ ζ x (t' • unitVec x + w)‖
      ≤ ∫ w : ↥(ℝ ∙ x)ᗮ, K * ((1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ)) +
          (1 + ‖t' • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall fun w => ?_)
        refine (norm_amp_sub_le_decay hN hΦ hlam a b ξ ζ x _ _).trans (le_of_eq ?_)
        have : ‖t • unitVec x + (w : Mom d) - (t' • unitVec x + (w : Mom d))‖ = |t - t'| := by
          rw [add_sub_add_right_eq_sub, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs]
        rw [this]
        simp only [K]
        ring
    _ = K * ((∫ w : ↥(ℝ ∙ x)ᗮ, (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) +
          ∫ w : ↥(ℝ ∙ x)ᗮ, (1 + ‖t' • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) := by
        rw [integral_const_mul, integral_add (integrable_decay_slice hx b t)
          (integrable_decay_slice hx b t')]
    _ ≤ K * (hypConst d d + hypConst d d) := by
        gcongr
        · exact integral_decay_slice_le hx b t
        · exact integral_decay_slice_le hx b t'
    _ = _ := by simp only [K, sliceConst]; ring

end WaveTurbulence.NTSP
