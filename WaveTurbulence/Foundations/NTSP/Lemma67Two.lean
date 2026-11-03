/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Lemma67One
public import WaveTurbulence.Foundations.WKE.DeltaReading

/-!
# DH23 Lemma 6.7 (2): per-slice analysis

`δ(⟨x,y⟩)` is read on hyperplanes as in ruling D6 (the reading of the frozen `collisionOp`):
`∫∫ δ(⟨x,y⟩) F(x,y) dx dy = ∫ |x|^{-1} ∫_{x^⊥} F(x, w) dw dx` (`deltaInner`; for real `F` it is
`2 · WKE.deltaInt F`, `deltaInner_ofReal`, since `deltaInt` reads `δ(2⟨·,·⟩)`).

For `x ≠ 0` (`psi_amp_eq`):
`μ ∫ ψ(μ⟨x,y⟩) F(x,y) dy = |x|^{-1} ∫ ψ(u) S_x(u/(μ|x|)) du`, `S_x(t) = ∫_{x^⊥} F(x, t x/|x| + w) dw`,
so the error against `(∫ψ) |x|^{-1} S_x(0)` is controlled by the Lipschitz bound of `S_x`
(`norm_psi_amp_sub_le`).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- `∫∫ δ(⟨x,y⟩) F(x,y) dx dy`, read as `∫ |x|^{-1} ∫_{x^⊥} F(x, w) dw dx` (ruling D6). -/
@[expose] def deltaInner (F : Mom d → Mom d → ℂ) : ℂ :=
  ∫ x, ((‖x‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ x)ᗮ, F x w

theorem deltaInner_ofReal (F : Mom d → Mom d → ℝ) :
    deltaInner (fun x y => (F x y : ℂ)) = ((2 * deltaInt F : ℝ) : ℂ) := by
  rw [deltaInner, deltaInt, ← integral_const_mul, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_complex_ofReal, ← Complex.ofReal_mul]
  congr 1
  rw [mul_inv]
  ring

variable {N : ℕ} {D lam μ : ℝ} {Φ : Mom d → Mom d → ℂ} {ψ : ℝ → ℂ}

theorem sliceAmp_zero (lam : ℝ) (Φ : Mom d → Mom d → ℂ) (a b ξ ζ x : Mom d) :
    sliceAmp lam Φ a b ξ ζ x 0 = ∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w := by
  simp [sliceAmp]

theorem integrable_psi_amp (hN : 1 ≤ N) (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (hμ : 0 < μ)
    (hψm : Measurable ψ) (hψ : Integrable ψ) (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0) :
    Integrable (fun y => ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) := by
  have h0 : 0 < lam := by linarith
  have hD := hΦ.nonneg
  refine ⟨?_, ?_⟩
  · exact ((hψm.comp (measurable_const.mul (measurable_const.inner measurable_id))).mul
      ((continuous_amp hN hΦ a b ξ ζ).comp (continuous_const.prodMk continuous_id)).measurable
      ).aestronglyMeasurable
  · have hM : Integrable (fun u => D * ‖ψ u‖) := hψ.norm.const_mul D
    have h := lintegral_majorant_le h0 hμ (M := fun u => D * ‖ψ u‖)
      (measurable_const.mul hψm.norm) hM (fun u => by positivity) a b hx
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (h.trans_lt ENNReal.ofReal_lt_top)
    rw [← ofReal_norm, norm_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have := norm_amp_le (lam := lam) hΦ a b ξ ζ x y
    calc ‖ψ (μ * inner ℝ x y)‖ * ‖amp lam Φ a b ξ ζ x y‖
        ≤ ‖ψ (μ * inner ℝ x y)‖ * (D * ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖) := by
          gcongr
      _ = _ := by ring

theorem lipschitz_sliceAmp (hN : 1 ≤ N) (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam)
    (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0) :
    Continuous (sliceAmp lam Φ a b ξ ζ x) := by
  have hD := hΦ.nonneg
  have hL : 0 ≤ 2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam := by
    have := ampLip_nonneg d hD ζ; have := sliceConst_nonneg d (by linarith : (0 : ℝ) ≤ lam)
    positivity
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal
    (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam)) fun t t' => ?_).continuous
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hL]
  exact norm_sliceAmp_sub_le hN hΦ hlam a b ξ ζ hx t t'

/-- The per-slice identity: `μ ∫ ψ(μ⟨x,y⟩) F(x,y) dy = |x|^{-1} ∫ ψ(u) S_x(u/(μ|x|)) du`. -/
theorem psi_amp_eq (hN : 1 ≤ N) (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (hμ : 0 < μ)
    (hψm : Measurable ψ) (hψ : Integrable ψ) (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0) :
    (μ : ℂ) * ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y =
      ((‖x‖⁻¹ : ℝ) : ℂ) * ∫ u, ψ u * sliceAmp lam Φ a b ξ ζ x (u / (μ * ‖x‖)) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hc : 0 < μ * ‖x‖ := by positivity
  rw [integral_eq_integral_slice_complex hx (integrable_psi_amp hN hΦ hlam hμ hψm hψ a b ξ ζ hx)]
  have h1 : ∀ t : ℝ, ∫ w : ↥(ℝ ∙ x)ᗮ, ψ (μ * inner ℝ x (t • unitVec x + (w : Mom d))) *
      amp lam Φ a b ξ ζ x (t • unitVec x + w) =
      ψ ((μ * ‖x‖) * t) * sliceAmp lam Φ a b ξ ζ x t := fun t => by
    simp_rw [inner_slice]
    rw [sliceAmp, ← integral_const_mul]
    congr 1
    funext w
    ring_nf
  simp_rw [h1]
  have h2 := Measure.integral_comp_mul_left
    (fun u : ℝ => ψ u * sliceAmp lam Φ a b ξ ζ x (u / (μ * ‖x‖))) (μ * ‖x‖)
  have h3 : ∀ t : ℝ, (μ * ‖x‖) * t / (μ * ‖x‖) = t := fun t => by field_simp
  simp only [h3] at h2
  rw [h2, abs_of_pos (inv_pos.2 hc), Complex.real_smul, ← mul_assoc]
  congr 1
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hxc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hxn.ne'
  push_cast
  field_simp

/-- The per-slice error. -/
theorem norm_psi_amp_sub_le (hN : 1 ≤ N) (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (hμ : 0 < μ)
    (hψm : Measurable ψ) (hψ : Integrable ψ) (a b ξ ζ : Mom d) {x : Mom d} (hx : x ≠ 0) :
    ‖(μ : ℂ) * (∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) -
        (∫ u, ψ u) * (((‖x‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w)‖ ≤
      ‖x‖⁻¹ * ∫ u, ‖ψ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * sliceConst d lam))
        (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam * (|u| / (μ * ‖x‖))) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h0 : 0 < lam := by linarith
  have hD := hΦ.nonneg
  set S := sliceAmp lam Φ a b ξ ζ x
  set Sb := D * ‖chiScaled lam (x - a)‖ * sliceConst d lam
  set Lb := 2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam
  have hS : Continuous S := lipschitz_sliceAmp hN hΦ hlam a b ξ ζ hx
  have hSb : ∀ t, ‖S t‖ ≤ Sb := fun t => norm_sliceAmp_le hΦ h0 a b ξ ζ hx t
  have hint1 : Integrable (fun u => ψ u * S (u / (μ * ‖x‖))) :=
    hψ.mul_bdd (hS.comp (continuous_id.div_const _)).aestronglyMeasurable
      (Eventually.of_forall fun u => hSb _)
  have hkey : (μ : ℂ) * (∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) -
      (∫ u, ψ u) * (((‖x‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w) =
      ((‖x‖⁻¹ : ℝ) : ℂ) * ∫ u, ψ u * (S (u / (μ * ‖x‖)) - S 0) := by
    rw [psi_amp_eq hN hΦ hlam hμ hψm hψ a b ξ ζ hx, ← sliceAmp_zero]
    simp_rw [mul_sub]
    rw [integral_sub hint1 (hψ.mul_const _), integral_mul_const]
    ring
  rw [hkey, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbnd : Integrable (fun u => ‖ψ u‖ * min (2 * Sb) (Lb * (|u| / (μ * ‖x‖)))) :=
    hψ.norm.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun u => by
        have hS0 : 0 ≤ Sb := by
          have := sliceConst_nonneg d h0.le; simp only [Sb]; positivity
        have hL0 : 0 ≤ Lb * (|u| / (μ * ‖x‖)) := by
          have := ampLip_nonneg d hD ζ; have := sliceConst_nonneg d h0.le
          simp only [Lb]; positivity
        rw [Real.norm_of_nonneg (le_min (by linarith) hL0)]
        exact min_le_left _ _)
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hbnd
    (Eventually.of_forall fun u => ?_)
  simp only
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) (norm_nonneg _)
  · calc ‖S (u / (μ * ‖x‖)) - S 0‖ ≤ ‖S (u / (μ * ‖x‖))‖ + ‖S 0‖ := norm_sub_le _ _
      _ ≤ Sb + Sb := add_le_add (hSb _) (hSb _)
      _ = 2 * Sb := by ring
  · refine (norm_sliceAmp_sub_le hN hΦ hlam a b ξ ζ hx _ 0).trans (le_of_eq ?_)
    rw [sub_zero, abs_div, abs_of_pos (by positivity : 0 < μ * ‖x‖)]

end WaveTurbulence.NTSP
