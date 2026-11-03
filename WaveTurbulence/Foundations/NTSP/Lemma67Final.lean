/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Lemma67Two

/-!
# DH23 Lemma 6.7 (2)

For `d ≥ 2`, `0 < η < 1`, `λ ≥ 1`, `μ > 0`, `Φ` with `|Φ| ≤ D`, `|∇_y Φ| ≤ D` and
`W = ∫ |ψ(u)| (1+|u|)^{1-η} du < ∞` (`ntintlem_two_gen`):

  `|μ ∫∫ ψ(μ⟨x,y⟩) F(x,y) dx dy - (∫ψ) ∫∫ δ(⟨x,y⟩) F(x,y) dx dy| ≤ C D λ^{2d} (1 + |ζ|) μ^{-(1-η)} W`,

`F(x,y) = χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y)`, `δ(⟨x,y⟩)` read on hyperplanes
(`deltaInner`). Per slice the error is `|x|^{-1} ∫ |ψ(u)| min(2 S_b, L_b |u|/(μ|x|)) du` with
`min(A, B t) ≤ (A + B) t^{1-η}`, and `∫_{B(a, λ√d)} |x|^{-(2-η)} dx ≲ λ^{d-2+η}`. The integrand of
`deltaInner` is measurable as the a.e. limit of the mollified integrals with `ψ₀ = 1_{[0,1]}`.

The source form (`ntintlem_two`, DH23 L1151–L1155) follows for `μ ≥ 1`: the error is
`≲ D λ^{2d} μ^{-(1-2η)} (1 + |ξ| + |ζ|) ‖⟨u⟩^{1-η} ψ‖_{L¹}` (DH23 prints `μ^{1-2η}`; the
exponent is negative, as in DH21 Lemma 6.5 (2), erratum).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

theorem min_le_add_mul_rpow {A B t η : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (hη0 : 0 ≤ η)
    (hη1 : η < 1) : min A (B * t) ≤ (A + B) * t ^ (1 - η) := by
  rcases le_total 1 t with h | h
  · have h1 : 1 ≤ t ^ (1 - η) := Real.one_le_rpow h (by linarith)
    calc min A (B * t) ≤ A := min_le_left _ _
      _ ≤ A * t ^ (1 - η) := le_mul_of_one_le_right hA h1
      _ ≤ (A + B) * t ^ (1 - η) := by gcongr; linarith
  · rcases ht.eq_or_lt with h0 | h0
    · subst h0
      rw [mul_zero, min_eq_right hA]
      positivity
    have h1 : t ≤ t ^ (1 - η) := by
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ (1 - η) := Real.rpow_le_rpow_of_exponent_ge h0 h (by linarith)
    calc min A (B * t) ≤ B * t := min_le_right _ _
      _ ≤ B * t ^ (1 - η) := by gcongr
      _ ≤ (A + B) * t ^ (1 - η) := by gcongr; linarith

variable {N : ℕ} {D lam μ : ℝ} {Φ : Mom d → Mom d → ℂ} {ψ : ℝ → ℂ}

theorem stronglyMeasurable_psi_amp (hN : 1 ≤ N) (hΦ : NTBounds N D Φ) (μ : ℝ)
    (hψm : Measurable ψ) (a b ξ ζ : Mom d) :
    StronglyMeasurable (fun x => ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) := by
  have h : StronglyMeasurable (fun p : Mom d × Mom d =>
      ψ (μ * inner ℝ p.1 p.2) * amp lam Φ a b ξ ζ p.1 p.2) :=
    ((hψm.comp (measurable_const.mul (measurable_fst.inner measurable_snd))).mul
      (continuous_amp hN hΦ a b ξ ζ).measurable).stronglyMeasurable
  exact h.integral_prod_right'

/-- The integrand of `deltaInner` is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_delta (hd : 1 ≤ d) (hN : 1 ≤ N) (hΦ : NTBounds N D Φ)
    (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) :
    AEStronglyMeasurable (fun x : Mom d =>
      ((‖x‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w) := by
  have h0 : 0 < lam := by linarith
  have hD := hΦ.nonneg
  set ψ₀ : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hψ₀m : Measurable ψ₀ := measurable_const.indicator measurableSet_Icc
  have hψ₀ : Integrable ψ₀ := (integrableOn_const (C := (1 : ℂ)) (by simp)).integrable_indicator
    measurableSet_Icc
  have hint0 : ∫ u, ψ₀ u = 1 := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc]
    simp
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n : ℕ => fun x => ((n + 1 : ℝ) : ℂ) *
      ∫ y, ψ₀ ((n + 1 : ℝ) * inner ℝ x y) * amp lam Φ a b ξ ζ x y)
    (fun n => ((stronglyMeasurable_const.mul
      (stronglyMeasurable_psi_amp hN hΦ (n + 1 : ℝ) hψ₀m a b ξ ζ))).aestronglyMeasurable) ?_
  filter_upwards [ae_ne_zero_mom (by omega)] with x hx
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set Lb := 2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam
  have hLb : 0 ≤ Lb := by
    have := ampLip_nonneg d hD ζ; have := sliceConst_nonneg d h0.le
    simp only [Lb]; positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (g := fun n : ℕ => ‖x‖⁻¹ * (Lb / (((n : ℝ) + 1) * ‖x‖))) ?_
  · have hμ : (0 : ℝ) < n + 1 := by positivity
    have h := norm_psi_amp_sub_le hN hΦ hlam hμ hψ₀m hψ₀ a b ξ ζ hx
    rw [hint0, one_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hb : ∀ u, ‖ψ₀ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * sliceConst d lam))
        (Lb * (|u| / (((n : ℝ) + 1) * ‖x‖))) ≤
        (Icc (0 : ℝ) 1).indicator (fun _ => Lb / (((n : ℝ) + 1) * ‖x‖)) u := fun u => by
      by_cases hu : u ∈ Icc (0 : ℝ) 1
      · simp only [ψ₀, Set.indicator_of_mem hu, norm_one, one_mul]
        refine (min_le_right _ _).trans ?_
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
        have : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
        nlinarith
      · simp only [ψ₀, Set.indicator_of_notMem hu, norm_zero, zero_mul, le_refl]
    calc ∫ u, ‖ψ₀ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * sliceConst d lam))
          (Lb * (|u| / (((n : ℝ) + 1) * ‖x‖)))
        ≤ ∫ u, (Icc (0 : ℝ) 1).indicator (fun _ => Lb / (((n : ℝ) + 1) * ‖x‖)) u :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => by
            have : 0 ≤ min (2 * (D * ‖chiScaled lam (x - a)‖ * sliceConst d lam))
                (Lb * (|u| / (((n : ℝ) + 1) * ‖x‖))) := le_min (by
                  have := sliceConst_nonneg d h0.le; positivity) (by positivity)
            positivity)
            ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
            (Eventually.of_forall hb)
      _ = Lb / (((n : ℝ) + 1) * ‖x‖) := by
          rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc]
          simp
  · have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 := (h1.const_mul (‖x‖⁻¹ * (Lb / ‖x‖)))
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    field_simp

/-- The constant of DH23 Lemma 6.7 (2). -/
@[expose] def ntConst (d : ℕ) (η : ℝ) : ℝ :=
  2 * ((1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d) * (2 + chiDerivConst d 1 + 2 * Real.pi) *
    (singConst d (2 - η) * (Real.sqrt d) ^ ((d : ℝ) - (2 - η)))

/-- The inner bound, for `x ≠ 0`. -/
theorem integral_min_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hD : 0 ≤ D) (hlam : 1 ≤ lam)
    (hμ : 0 < μ) (hW : Integrable (fun u => ‖ψ u‖ * (1 + |u|) ^ (1 - η)))
    (a ζ : Mom d) {x : Mom d} (hx : x ≠ 0) :
    ∫ u, ‖ψ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * sliceConst d lam))
        (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * sliceConst d lam * (|u| / (μ * ‖x‖))) ≤
      (closedBall a (lam * Real.sqrt d)).indicator (fun _ => (1 : ℝ)) x *
        (2 * sliceConst d lam * (D + ampLip d D ζ)) * (μ * ‖x‖) ^ (-(1 - η)) *
          ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η) := by
  have h0 : 0 < lam := by linarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hc : 0 < μ * ‖x‖ := by positivity
  set K := sliceConst d lam
  have hK : 0 ≤ K := sliceConst_nonneg d h0.le
  have hAL := ampLip_nonneg d hD ζ
  set W := ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η)
  have hW0 : 0 ≤ W := integral_nonneg fun u => by positivity
  by_cases hxa : x ∈ closedBall a (lam * Real.sqrt d)
  · rw [Set.indicator_of_mem hxa, one_mul]
    have hc1 := norm_chiScaled_le_one lam (x - a)
    have hpt : ∀ u, ‖ψ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * K))
        (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * K * (|u| / (μ * ‖x‖))) ≤
        (2 * K * (D + ampLip d D ζ) * (μ * ‖x‖) ^ (-(1 - η))) *
          (‖ψ u‖ * (1 + |u|) ^ (1 - η)) := fun u => by
      have ht : 0 ≤ |u| / (μ * ‖x‖) := by positivity
      have hm1 : min (2 * (D * ‖chiScaled lam (x - a)‖ * K))
          (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * K * (|u| / (μ * ‖x‖))) ≤
          min (2 * (D * K)) ((2 * ampLip d D ζ * K) * (|u| / (μ * ‖x‖))) := by
        refine min_le_min ?_ ?_
        · have : D * ‖chiScaled lam (x - a)‖ * K ≤ D * 1 * K := by gcongr
          linarith
        · have : 2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * K ≤ 2 * 1 * ampLip d D ζ * K := by
            gcongr
          nlinarith
      have hm2 := min_le_add_mul_rpow (A := 2 * (D * K)) (B := 2 * ampLip d D ζ * K)
        (by positivity) (by positivity) ht hη0 hη1
      have ht2 : (|u| / (μ * ‖x‖)) ^ (1 - η) ≤ (1 + |u|) ^ (1 - η) * (μ * ‖x‖) ^ (-(1 - η)) := by
        rw [Real.div_rpow (abs_nonneg u) hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]
        gcongr
        linarith [abs_nonneg u]
      calc ‖ψ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * K))
            (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * K * (|u| / (μ * ‖x‖)))
          ≤ ‖ψ u‖ * ((2 * (D * K) + 2 * ampLip d D ζ * K) *
              ((1 + |u|) ^ (1 - η) * (μ * ‖x‖) ^ (-(1 - η)))) := by
            gcongr
            exact hm1.trans (hm2.trans (by gcongr))
        _ = _ := by ring
    calc ∫ u, ‖ψ u‖ * min (2 * (D * ‖chiScaled lam (x - a)‖ * K))
          (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * K * (|u| / (μ * ‖x‖)))
        ≤ ∫ u, (2 * K * (D + ampLip d D ζ) * (μ * ‖x‖) ^ (-(1 - η))) *
            (‖ψ u‖ * (1 + |u|) ^ (1 - η)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => by
            have : 0 ≤ min (2 * (D * ‖chiScaled lam (x - a)‖ * K))
                (2 * ‖chiScaled lam (x - a)‖ * ampLip d D ζ * K * (|u| / (μ * ‖x‖))) :=
              le_min (by positivity) (by positivity)
            positivity) (hW.const_mul _) (Eventually.of_forall hpt)
      _ = _ := by rw [integral_const_mul]
  · rw [Set.indicator_of_notMem hxa, zero_mul, zero_mul, zero_mul]
    have hc0 : chiScaled lam (x - a) = 0 := by
      by_contra h
      exact hxa (by rw [mem_closedBall, dist_eq_norm]; exact norm_le_of_chiScaled_ne_zero h0 h)
    simp [hc0]

/-- **DH23 Lemma 6.7 (2)** (`NTintlem`, (NTintlem2), explicit form): for `d ≥ 2`, `0 < η < 1`,
`λ ≥ 1`, `μ > 0`, `Φ` with (NTphibounds) through order `N ≥ 1` and constant `D`, and `ψ`
measurable with `W = ∫ |ψ(u)| (1+|u|)^{1-η} du < ∞`, uniformly in `(a, b, ξ)`:
`|μ ∫∫ ψ(μ⟨x,y⟩) F dx dy - (∫ψ) ∫∫ δ(⟨x,y⟩) F dx dy| ≤ C D λ^{2d} (1 + |ζ|) μ^{-(1-η)} W`,
`F(x,y) = χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y)`, `δ` read on hyperplanes (`deltaInner`). -/
theorem ntintlem_two_gen (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hN : 1 ≤ N)
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (hμ : 0 < μ) (hψm : Measurable ψ)
    (hW : Integrable (fun u => ‖ψ u‖ * (1 + |u|) ^ (1 - η))) (a b ξ ζ : Mom d) :
    ‖(μ : ℂ) * (∫ x, ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) -
        (∫ u, ψ u) * deltaInner (amp lam Φ a b ξ ζ)‖ ≤
      ntConst d η * D * lam ^ (2 * d) * (1 + ‖ζ‖) * μ ^ (-(1 - η)) *
        ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η) := by
  have h0 : 0 < lam := by linarith
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD := hΦ.nonneg
  have hψ : Integrable ψ := hW.mono' hψm.aestronglyMeasurable (Eventually.of_forall fun u => by
    have : 1 ≤ (1 + |u|) ^ (1 - η) := Real.one_le_rpow (by linarith [abs_nonneg u]) (by linarith)
    calc ‖ψ u‖ = ‖ψ u‖ * 1 := (mul_one _).symm
      _ ≤ ‖ψ u‖ * (1 + |u|) ^ (1 - η) := by gcongr)
  set K := sliceConst d lam
  have hK : 0 ≤ K := sliceConst_nonneg d h0.le
  have hAL := ampLip_nonneg d hD ζ
  set W := ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η)
  have hW0 : 0 ≤ W := integral_nonneg fun u => by positivity
  set r := lam * Real.sqrt d
  have hr : 0 < r := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd0)
    positivity
  set I : Mom d → ℂ := fun x => ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y
  set δx : Mom d → ℂ := fun x => ((‖x‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w
  have hp1 : (0 : ℝ) ≤ 1 := zero_le_one
  have hp1d : (1 : ℝ) < d := by linarith
  have hsint1 := integrable_indicator_norm_rpow (d := d) (p := 1) hp1 hp1d hr a
  -- integrability of `I` and `δ`
  have hIint : Integrable I := by
    refine ((hsint1.const_mul (μ⁻¹ * (∫ u, ‖ψ u‖) * (D * K)))).mono'
      (stronglyMeasurable_psi_amp hN hΦ μ hψm a b ξ ζ).aestronglyMeasurable ?_
    filter_upwards [ae_ne_zero_mom hd0] with x hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have he := psi_amp_eq hN hΦ hlam hμ hψm hψ a b ξ ζ hx
    have hSb : ∀ t, ‖sliceAmp lam Φ a b ξ ζ x t‖ ≤ D * ‖chiScaled lam (x - a)‖ * K :=
      fun t => norm_sliceAmp_le hΦ h0 a b ξ ζ hx t
    have hn : ‖I x‖ ≤ μ⁻¹ * (‖x‖⁻¹ * ((∫ u, ‖ψ u‖) * (D * ‖chiScaled lam (x - a)‖ * K))) := by
      have h1 : ‖(μ : ℂ) * I x‖ ≤ ‖x‖⁻¹ * ((∫ u, ‖ψ u‖) * (D * ‖chiScaled lam (x - a)‖ * K)) := by
        simp only [I]
        rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_)
          (by positivity)
        rw [← integral_mul_const]
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hψ.norm.mul_const _) (Eventually.of_forall fun u => ?_)
        simp only
        rw [norm_mul]
        gcongr
        exact hSb _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ.le] at h1
      rw [le_inv_mul_iff₀ hμ]
      exact h1
    refine hn.trans ?_
    have hc := norm_chiScaled_le_indicator h0 a x
    have hψ0 : 0 ≤ ∫ u, ‖ψ u‖ := integral_nonneg fun _ => norm_nonneg _
    by_cases hxa : x ∈ closedBall a r
    · rw [Set.indicator_of_mem hxa] at hc ⊢
      rw [Real.rpow_neg_one]
      calc μ⁻¹ * (‖x‖⁻¹ * ((∫ u, ‖ψ u‖) * (D * ‖chiScaled lam (x - a)‖ * K)))
          ≤ μ⁻¹ * (‖x‖⁻¹ * ((∫ u, ‖ψ u‖) * (D * 1 * K))) := by gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hxa] at hc ⊢
      have : ‖chiScaled lam (x - a)‖ = 0 := le_antisymm hc (norm_nonneg _)
      rw [this]; simp
  have hδint : Integrable δx := by
    refine ((hsint1.const_mul (D * K))).mono'
      (aestronglyMeasurable_delta (by omega) hN hΦ hlam a b ξ ζ) ?_
    filter_upwards [ae_ne_zero_mom hd0] with x hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 := norm_sliceAmp_le hΦ h0 a b ξ ζ hx 0
    rw [sliceAmp_zero] at h1
    simp only [δx]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hc := norm_chiScaled_le_indicator h0 a x
    by_cases hxa : x ∈ closedBall a r
    · rw [Set.indicator_of_mem hxa, Real.rpow_neg_one]
      rw [Set.indicator_of_mem hxa] at hc
      calc ‖x‖⁻¹ * ‖∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w‖
          ≤ ‖x‖⁻¹ * (D * 1 * K) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = D * K * ‖x‖⁻¹ := by ring
    · rw [Set.indicator_of_notMem hxa, mul_zero]
      rw [Set.indicator_of_notMem hxa] at hc
      have : ‖chiScaled lam (x - a)‖ = 0 := le_antisymm hc (norm_nonneg _)
      have h2 : ‖∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w‖ ≤ 0 := by
        refine h1.trans (le_of_eq ?_); rw [this]; ring
      nlinarith [norm_nonneg (∫ w : ↥(ℝ ∙ x)ᗮ, amp lam Φ a b ξ ζ x w), inv_nonneg.2 hxn.le]
  -- the main estimate
  have hsplit : (μ : ℂ) * (∫ x, I x) - (∫ u, ψ u) * deltaInner (amp lam Φ a b ξ ζ) =
      ∫ x, ((μ : ℂ) * I x - (∫ u, ψ u) * δx x) := by
    rw [integral_sub (hIint.const_mul _) (hδint.const_mul _), integral_const_mul,
      integral_const_mul]
    rfl
  have hp2 : 0 ≤ 2 - η := by linarith
  have hp2d : 2 - η < d := by linarith
  have hsint2 := integrable_indicator_norm_rpow (d := d) (p := 2 - η) hp2 hp2d hr a
  set Cx := 2 * K * (D + ampLip d D ζ) * μ ^ (-(1 - η)) * W
  have hCx : 0 ≤ Cx := by positivity
  have hpt : ∀ᵐ x : Mom d, ‖(μ : ℂ) * I x - (∫ u, ψ u) * δx x‖ ≤
      Cx * (closedBall a r).indicator (fun x => ‖x‖ ^ (-(2 - η))) x := by
    filter_upwards [ae_ne_zero_mom hd0] with x hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine (norm_psi_amp_sub_le hN hΦ hlam hμ hψm hψ a b ξ ζ hx).trans ?_
    refine (mul_le_mul_of_nonneg_left (integral_min_le hη0.le hη1 hD hlam hμ hW a ζ hx)
      (by positivity)).trans (le_of_eq ?_)
    have e1 : ‖x‖⁻¹ * (μ * ‖x‖) ^ (-(1 - η)) = μ ^ (-(1 - η)) * ‖x‖ ^ (-(2 - η)) := by
      rw [Real.mul_rpow hμ.le hxn.le, ← Real.rpow_neg_one, mul_left_comm,
        ← Real.rpow_add hxn]
      ring_nf
    by_cases hxa : x ∈ closedBall a r
    · rw [Set.indicator_of_mem hxa, Set.indicator_of_mem hxa, one_mul]
      simp only [Cx]
      calc ‖x‖⁻¹ * (2 * K * (D + ampLip d D ζ) * (μ * ‖x‖) ^ (-(1 - η)) * W)
          = 2 * K * (D + ampLip d D ζ) * W * (‖x‖⁻¹ * (μ * ‖x‖) ^ (-(1 - η))) := by ring
        _ = _ := by rw [e1]; ring
    · rw [Set.indicator_of_notMem hxa, Set.indicator_of_notMem hxa]; simp
  have hsing := integral_indicator_norm_rpow_le (d := d) (p := 2 - η) hp2 hp2d hr a
  rw [hsplit]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ x, ‖(μ : ℂ) * I x - (∫ u, ψ u) * δx x‖
      ≤ ∫ x, Cx * (closedBall a r).indicator (fun x => ‖x‖ ^ (-(2 - η))) x :=
        integral_mono_ae (((hIint.const_mul _).sub (hδint.const_mul _)).norm)
          (hsint2.const_mul _) hpt
    _ = Cx * ∫ x, (closedBall a r).indicator (fun x => ‖x‖ ^ (-(2 - η))) x := integral_const_mul _ _
    _ ≤ Cx * (singConst d (2 - η) * r ^ ((d : ℝ) - (2 - η))) := by gcongr
    _ ≤ ntConst d η * D * lam ^ (2 * d) * (1 + ‖ζ‖) * μ ^ (-(1 - η)) * W := by
        have hsd := Real.sqrt_nonneg d
        have hc1 := chiDerivConst_nonneg d 1
        have hs := singConst_nonneg d hp2d
        have hH := hypConst_nonneg d d
        have hK' : K ≤ lam ^ d * ((1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d) := by
          simp only [K, sliceConst]
          have h1 : 1 + lam * Real.sqrt d ≤ lam * (1 + Real.sqrt d) := by nlinarith
          calc (1 + lam * Real.sqrt d) ^ (d : ℝ) * hypConst d d
              ≤ (lam * (1 + Real.sqrt d)) ^ (d : ℝ) * hypConst d d := by gcongr
            _ = _ := by rw [Real.mul_rpow h0.le (by positivity), Real.rpow_natCast]; ring
        have hr' : r ^ ((d : ℝ) - (2 - η)) ≤ lam ^ d * (Real.sqrt d) ^ ((d : ℝ) - (2 - η)) := by
          simp only [r]
          rw [Real.mul_rpow h0.le hsd]
          gcongr
          calc lam ^ ((d : ℝ) - (2 - η)) ≤ lam ^ (d : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hlam (by linarith)
            _ = lam ^ d := Real.rpow_natCast _ _
        have hAL' : D + ampLip d D ζ ≤ D * (2 + chiDerivConst d 1 + 2 * Real.pi) * (1 + ‖ζ‖) := by
          simp only [ampLip]
          have hz := norm_nonneg ζ
          have hpi := Real.pi_pos
          nlinarith [mul_nonneg hD hc1, mul_nonneg hD hz, mul_nonneg (mul_nonneg hD hc1) hz,
            mul_nonneg (mul_nonneg hD hpi.le) hz]
        have hμη : 0 ≤ μ ^ (-(1 - η)) := by positivity
        simp only [Cx]
        calc 2 * K * (D + ampLip d D ζ) * μ ^ (-(1 - η)) * W *
              (singConst d (2 - η) * r ^ ((d : ℝ) - (2 - η)))
            ≤ 2 * (lam ^ d * ((1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d)) *
                (D * (2 + chiDerivConst d 1 + 2 * Real.pi) * (1 + ‖ζ‖)) * μ ^ (-(1 - η)) * W *
                (singConst d (2 - η) * (lam ^ d * (Real.sqrt d) ^ ((d : ℝ) - (2 - η)))) := by
              gcongr
          _ = ntConst d η * D * lam ^ (2 * d) * (1 + ‖ζ‖) * μ ^ (-(1 - η)) * W := by
              rw [ntConst, two_mul d, pow_add]; ring

theorem one_add_abs_rpow_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ) :
    (1 + |u|) ^ (1 - η) ≤ 2 * Real.sqrt (1 + u ^ 2) ^ (1 - η) := by
  have h1 : 1 + |u| ≤ 2 * Real.sqrt (1 + u ^ 2) := by
    have hs : |u| ≤ Real.sqrt (1 + u ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have h1 : 1 ≤ Real.sqrt (1 + u ^ 2) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + u ^ 2 by nlinarith)
      rwa [Real.sqrt_one] at this
    linarith
  calc (1 + |u|) ^ (1 - η) ≤ (2 * Real.sqrt (1 + u ^ 2)) ^ (1 - η) :=
        Real.rpow_le_rpow (by positivity) h1 (by linarith)
    _ = 2 ^ (1 - η) * Real.sqrt (1 + u ^ 2) ^ (1 - η) := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * Real.sqrt (1 + u ^ 2) ^ (1 - η) := by
        gcongr
        calc (2 : ℝ) ^ (1 - η) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2

/-- **DH23 Lemma 6.7 (2)** (`NTintlem`, (NTintlem2), L1151–L1155), source form: for `d ≥ 2`,
`0 < η < 1`, `λ ≥ 1`, `μ ≥ 1`, `Φ` with (NTphibounds) through order `N ≥ 1` with constant `D`,
and `ψ` measurable with `‖⟨u⟩^{1-η} ψ‖_{L¹} < ∞` (`⟨u⟩ = (1+u²)^{1/2}`), uniformly in `(a, b)`:
`|μ ∫∫ ψ(μ⟨x,y⟩) F dx dy - (∫ψ) ∫∫ δ(⟨x,y⟩) F dx dy|
  ≤ C D λ^{2d} μ^{-(1-2η)} (1 + |ξ| + |ζ|) ‖⟨u⟩^{1-η} ψ‖_{L¹}`,
`F(x,y) = χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y)`, `δ(⟨x,y⟩)` read on hyperplanes. DH23 prints
`μ^{-1} ∫ ψ(μΩ)` and `μ^{1-2η}`; we use `μ ∫ ψ(μΩ)` and `μ^{-(1-2η)}` (errata; cf. DH21
Lemma 6.5). -/
theorem ntintlem_two (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hN : 1 ≤ N)
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (hμ : 1 ≤ μ) (hψm : Measurable ψ)
    (hW : Integrable (fun u => ‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - η))) (a b ξ ζ : Mom d) :
    ‖(μ : ℂ) * (∫ x, ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) -
        (∫ u, ψ u) * deltaInner (amp lam Φ a b ξ ζ)‖ ≤
      2 * ntConst d η * D * lam ^ (2 * d) * μ ^ (-(1 - 2 * η)) * (1 + ‖ξ‖ + ‖ζ‖) *
        ∫ u, ‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - η) := by
  have hμ0 : 0 < μ := by linarith
  have hD := hΦ.nonneg
  have hpt : ∀ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η) ≤ 2 * (‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - η)) :=
    fun u => by
      have := one_add_abs_rpow_le hη0.le hη1 u
      calc ‖ψ u‖ * (1 + |u|) ^ (1 - η) ≤ ‖ψ u‖ * (2 * Real.sqrt (1 + u ^ 2) ^ (1 - η)) := by
            gcongr
        _ = _ := by ring
  have hW1 : Integrable (fun u => ‖ψ u‖ * (1 + |u|) ^ (1 - η)) :=
    (hW.const_mul 2).mono' ((hψm.norm.mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt u)
  have hint : ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η) ≤
      2 * ∫ u, ‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - η) := by
    rw [← integral_const_mul]
    exact integral_mono hW1 (hW.const_mul 2) hpt
  refine (ntintlem_two_gen hd hη0 hη1 hN hΦ hlam hμ0 hψm hW1 a b ξ ζ).trans ?_
  have hC : 0 ≤ ntConst d η := by
    unfold ntConst
    have := hypConst_nonneg d d; have := chiDerivConst_nonneg d 1
    have := singConst_nonneg d (p := 2 - η) (by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
    have := Real.pi_pos
    positivity
  have hμη : μ ^ (-(1 - η)) ≤ μ ^ (-(1 - 2 * η)) :=
    Real.rpow_le_rpow_of_exponent_le hμ (by linarith)
  have hz : 1 + ‖ζ‖ ≤ 1 + ‖ξ‖ + ‖ζ‖ := by linarith [norm_nonneg ξ]
  have hW0 : 0 ≤ ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η) := integral_nonneg fun u => by positivity
  have hl : 0 ≤ lam ^ (2 * d) := by have : 0 ≤ lam := by linarith
                                    positivity
  calc ntConst d η * D * lam ^ (2 * d) * (1 + ‖ζ‖) * μ ^ (-(1 - η)) *
        ∫ u, ‖ψ u‖ * (1 + |u|) ^ (1 - η)
      ≤ ntConst d η * D * lam ^ (2 * d) * (1 + ‖ξ‖ + ‖ζ‖) * μ ^ (-(1 - 2 * η)) *
          (2 * ∫ u, ‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - η)) := by gcongr
    _ = _ := by ring

end WaveTurbulence.NTSP
