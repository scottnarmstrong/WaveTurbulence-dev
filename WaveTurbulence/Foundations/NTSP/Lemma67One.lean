/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Lemma67Slices
public import WaveTurbulence.Foundations.NTSP.NearTerms

/-!
# DH23 Lemma 6.7 (1)

For `μ > 0`, `λ ≥ 1`, `Ψ(u, x, y)` with `|Ψ(u, x, y)| ≤ M(u)`, `M ∈ L¹`:

  `|μ ∫∫ Ψ(μ⟨x,y⟩, x, y) χ₀((x-a)/λ) χ₀((y-b)/λ) e(ξ·x + ζ·y) dx dy| ≤ C ‖M‖_{L¹} λ^{2d}`

(`ntintlem_one_gen`, `d ≥ 2`). Proof: slicing `y = t x/|x| + w` gives, for each `x ≠ 0`,
`μ ∫ |…| dy ≤ |x|^{-1} |χ₀((x-a)/λ)| ‖M‖_{L¹} (1 + λ√d)^d ∫_{ℝ^{d-1}} (1+|w|)^{-d}`, and
`∫_{B(a, λ√d)} |x|^{-1} dx ≲ λ^{d-1}` (`integral_indicator_norm_rpow_le`). With
`Ψ(u, x, y) = ψ(u) Φ(x, y)` this is (NTintlem1) (`ntintlem_one`).

DH23 writes `μ^{-1} ∫ ψ(μΩ) …`; the normalization that makes `μ ψ(μ ·)` an approximate identity is
`μ ∫ ψ(μΩ) …`, as in DH21 Lemma 6.5 (L1475), which we follow (erratum).
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

theorem ae_ne_zero_mom (hd : 0 < d) : ∀ᵐ x : Mom d, x ≠ 0 := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Mom d))] with x hx
  simpa using hx

theorem norm_chiScaled_le_indicator {lam : ℝ} (hlam : 0 < lam) (a x : Mom d) :
    ‖chiScaled lam (x - a)‖ ≤ (closedBall a (lam * Real.sqrt d)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : chiScaled lam (x - a) = 0
  · rw [hx, norm_zero]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [Set.indicator_of_mem]
    · exact norm_chiScaled_le_one lam _
    · rw [mem_closedBall, dist_eq_norm]; exact norm_le_of_chiScaled_ne_zero hlam hx

theorem lintegral_slice_chi_le {lam : ℝ} (hlam : 0 < lam) (b : Mom d) {x : Mom d} (hx : x ≠ 0)
    (t : ℝ) :
    ∫⁻ w : ↥(ℝ ∙ x)ᗮ, ENNReal.ofReal ‖chiScaled lam (t • unitVec x + (w : Mom d) - b)‖ ≤
      ENNReal.ofReal (sliceConst d lam) := by
  calc ∫⁻ w : ↥(ℝ ∙ x)ᗮ, ENNReal.ofReal ‖chiScaled lam (t • unitVec x + (w : Mom d) - b)‖
      ≤ ∫⁻ w : ↥(ℝ ∙ x)ᗮ, ENNReal.ofReal ((1 + lam * Real.sqrt d) ^ (d : ℝ) *
          (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) :=
        lintegral_mono fun w => ENNReal.ofReal_le_ofReal (norm_chiScaled_le_decay hlam b _)
    _ = ENNReal.ofReal (∫ w : ↥(ℝ ∙ x)ᗮ, (1 + lam * Real.sqrt d) ^ (d : ℝ) *
          (1 + ‖t • unitVec x + (w : Mom d) - b‖) ^ (-(d : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrable_decay_slice hx b t).const_mul _)
          (Filter.Eventually.of_forall fun w => by positivity)).symm
    _ ≤ ENNReal.ofReal (sliceConst d lam) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, sliceConst]
        gcongr
        exact integral_decay_slice_le hx b t

/-- The sliced majorant: for `x ≠ 0`,
`∫ M(μ⟨x,y⟩) |χ₀((x-a)/λ)| |χ₀((y-b)/λ)| dy ≤ |χ₀((x-a)/λ)| sliceConst (μ|x|)^{-1} ‖M‖_{L¹}`. -/
theorem lintegral_majorant_le {lam μ : ℝ} (h0 : 0 < lam) (hμ : 0 < μ) {M : ℝ → ℝ}
    (hMm : Measurable M) (hM : Integrable M) (hM0 : ∀ u, 0 ≤ M u) (a b : Mom d) {x : Mom d}
    (hx : x ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (M (μ * inner ℝ x y) * ‖chiScaled lam (x - a)‖ *
      ‖chiScaled lam (y - b)‖) ≤
      ENNReal.ofReal (‖chiScaled lam (x - a)‖ * sliceConst d lam * ((μ * ‖x‖)⁻¹ * ∫ u, M u)) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set K := sliceConst d lam
  have hK : 0 ≤ K := sliceConst_nonneg d h0.le
  set IM := ∫ u, M u
  set g : Mom d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (M (μ * inner ℝ x y) * ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖)
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp
    (((hMm.comp (measurable_const.mul (measurable_const.inner measurable_id))).mul
      measurable_const).mul
      ((contDiff_chiScaled lam).continuous.comp (continuous_id.sub continuous_const)).norm.measurable)
  show ∫⁻ y, g y ≤ _
  calc ∫⁻ y, g y
    _ = ∫⁻ t : ℝ, ∫⁻ w : ↥(ℝ ∙ x)ᗮ, g (t • unitVec x + w) := lintegral_eq_lintegral_slice hx hgm
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (M (μ * ‖x‖ * t) * ‖chiScaled lam (x - a)‖) *
          ∫⁻ w : ↥(ℝ ∙ x)ᗮ, ENNReal.ofReal ‖chiScaled lam (t • unitVec x + (w : Mom d) - b)‖ := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun w => ?_
        simp only [g, inner_slice]
        rw [← ENNReal.ofReal_mul (mul_nonneg (hM0 _) (norm_nonneg _))]
        congr 2
        ring_nf
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (M (μ * ‖x‖ * t) * ‖chiScaled lam (x - a)‖) *
          ENNReal.ofReal K := by
        gcongr with t
        exact lintegral_slice_chi_le h0 b hx t
    _ = ENNReal.ofReal (‖chiScaled lam (x - a)‖ * K) *
          ∫⁻ t : ℝ, ENNReal.ofReal (M (0 + t * (μ * ‖x‖))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun t => ?_
        rw [← ENNReal.ofReal_mul (mul_nonneg (hM0 _) (norm_nonneg _)),
          ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) hK)]
        congr 1
        rw [zero_add]
        ring_nf
    _ = ENNReal.ofReal (‖chiScaled lam (x - a)‖ * K) *
          (ENNReal.ofReal |μ * ‖x‖|⁻¹ * ENNReal.ofReal IM) := by
        have haff := lintegral_comp_affine (f := fun v => ENNReal.ofReal (M v))
          (β := μ * ‖x‖) (by positivity) 0 (ENNReal.measurable_ofReal.comp hMm)
        rw [haff,
          ← ofReal_integral_eq_lintegral_ofReal hM (Filter.Eventually.of_forall hM0)]
    _ = ENNReal.ofReal (‖chiScaled lam (x - a)‖ * K * ((μ * ‖x‖)⁻¹ * IM)) := by
        rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/-- The constant of DH23 Lemma 6.7 (1). -/
@[expose] def intConst (d : ℕ) : ℝ :=
  (1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d * singConst d 1 * (Real.sqrt d) ^ ((d : ℝ) - 1)

theorem intConst_nonneg (d : ℕ) (hd : 2 ≤ d) : 0 ≤ intConst d := by
  unfold intConst
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := hypConst_nonneg d d
  have h2 := singConst_nonneg d (p := 1) (by linarith)
  have h3 : 0 ≤ (1 + Real.sqrt d) ^ (d : ℝ) := by positivity
  have h4 : 0 ≤ (Real.sqrt d) ^ ((d : ℝ) - 1) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg h3 h1) h2) h4

/-- **DH23 Lemma 6.7 (1), general form** (`NTintlem`, L1147–L1151, the version with `Ψ(μΩ, x, y)`):
for `d ≥ 2`, `λ ≥ 1`, `μ > 0` and `|Ψ(u, x, y)| ≤ M(u)` with `M` integrable,
`|μ ∫∫ Ψ(μ⟨x,y⟩, x, y) χ₀((x-a)/λ) χ₀((y-b)/λ) e(ξ·x + ζ·y) dx dy| ≤ C ‖M‖_{L¹} λ^{2d}`
uniformly in `(a, b, ξ, ζ)`. -/
theorem ntintlem_one_gen (hd : 2 ≤ d) {lam μ : ℝ} (hlam : 1 ≤ lam) (hμ : 0 < μ)
    {Ψ : ℝ → Mom d → Mom d → ℂ} {M : ℝ → ℝ} (hMm : Measurable M) (hM : Integrable M)
    (hΨ : ∀ u x y, ‖Ψ u x y‖ ≤ M u) (a b ξ ζ : Mom d) :
    ‖μ * ∫ x, ∫ y, Ψ (μ * inner ℝ x y) x y * (chiScaled lam (x - a) * chiScaled lam (y - b) *
        (Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ) : ℂ))‖ ≤
      intConst d * (∫ u, M u) * lam ^ (2 * d) := by
  have h0 : 0 < lam := by linarith
  have hM0 : ∀ u, 0 ≤ M u := fun u => (norm_nonneg _).trans (hΨ u 0 0)
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set K := sliceConst d lam
  have hK : 0 ≤ K := sliceConst_nonneg d h0.le
  set IM := ∫ u, M u
  have hIM : 0 ≤ IM := integral_nonneg hM0
  set r := lam * Real.sqrt d
  have hr : 0 < r := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd0)
    positivity
  set f : Mom d → Mom d → ℂ := fun x y => Ψ (μ * inner ℝ x y) x y *
    (chiScaled lam (x - a) * chiScaled lam (y - b) *
      (Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ) : ℂ))
  -- the inner bound, for `x ≠ 0`
  have hinner : ∀ x : Mom d, x ≠ 0 → ∫⁻ y, ‖f x y‖ₑ ≤
      ENNReal.ofReal (‖chiScaled lam (x - a)‖ * K * ((μ * ‖x‖)⁻¹ * IM)) := fun x hx => by
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    set g : Mom d → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (M (μ * inner ℝ x y) * ‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖)
    have hgm : Measurable g := ENNReal.measurable_ofReal.comp
      (((hMm.comp (measurable_const.mul (measurable_const.inner measurable_id))).mul
        measurable_const).mul
        ((contDiff_chiScaled lam).continuous.comp (continuous_id.sub continuous_const)).norm.measurable)
    have hfg : ∀ y, ‖f x y‖ₑ ≤ g y := fun y => by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [f, norm_mul, Circle.norm_coe, mul_one]
      have := hΨ (μ * inner ℝ x y) x y
      calc ‖Ψ (μ * inner ℝ x y) x y‖ * (‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖)
          ≤ M (μ * inner ℝ x y) * (‖chiScaled lam (x - a)‖ * ‖chiScaled lam (y - b)‖) := by gcongr
        _ = _ := by ring
    refine (lintegral_mono hfg).trans ?_
    exact lintegral_majorant_le h0 hμ hMm hM hM0 a b hx
  -- the outer integral
  have hsing := integral_indicator_norm_rpow_le (d := d) (p := 1) zero_le_one
    (by linarith) hr a
  have hsint := integrable_indicator_norm_rpow (d := d) (p := 1) zero_le_one
    (by linarith) hr a
  have hbound : ‖μ * ∫ x, ∫ y, f x y‖ₑ ≤
      ENNReal.ofReal (K * IM * (singConst d 1 * r ^ ((d : ℝ) - 1))) := by
    have hμe : ‖(μ : ℂ)‖ₑ = ENNReal.ofReal μ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hμ.le]
    rw [enorm_mul, hμe]
    calc ENNReal.ofReal μ * ‖∫ x, ∫ y, f x y‖ₑ
        ≤ ENNReal.ofReal μ * ∫⁻ x, ∫⁻ y, ‖f x y‖ₑ := by
          gcongr
          exact (enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono fun x => enorm_integral_le_lintegral_enorm _)
      _ ≤ ENNReal.ofReal μ * ∫⁻ x, ENNReal.ofReal (μ⁻¹ * (K * IM *
            (closedBall a r).indicator (fun x => ‖x‖ ^ (-(1 : ℝ))) x)) := by
          refine mul_le_mul_right ?_ _
          refine lintegral_mono_ae ?_
          filter_upwards [ae_ne_zero_mom hd0] with x hx
          refine (hinner x hx).trans (ENNReal.ofReal_le_ofReal ?_)
          have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
          have hc := norm_chiScaled_le_indicator h0 a x
          by_cases hxa : x ∈ closedBall a r
          · rw [Set.indicator_of_mem hxa] at hc ⊢
            rw [Real.rpow_neg_one, mul_inv]
            calc ‖chiScaled lam (x - a)‖ * K * (μ⁻¹ * ‖x‖⁻¹ * IM)
                ≤ 1 * K * (μ⁻¹ * ‖x‖⁻¹ * IM) := by gcongr
              _ = _ := by ring
          · rw [Set.indicator_of_notMem hxa] at hc ⊢
            have : ‖chiScaled lam (x - a)‖ = 0 := le_antisymm hc (norm_nonneg _)
            rw [this]; simp
      _ = ENNReal.ofReal (K * IM * ∫ x, (closedBall a r).indicator
            (fun x => ‖x‖ ^ (-(1 : ℝ))) x) := by
          rw [← ofReal_integral_eq_lintegral_ofReal ((hsint.const_mul _).const_mul _)
            (Filter.Eventually.of_forall fun x => by
              have : 0 ≤ (closedBall a r).indicator (fun x => ‖x‖ ^ (-(1 : ℝ))) x :=
                Set.indicator_nonneg (fun _ _ => by positivity) _
              positivity),
            ← ENNReal.ofReal_mul hμ.le, integral_const_mul, integral_const_mul]
          congr 1
          field_simp
      _ ≤ _ := by gcongr
  have hval : 0 ≤ K * IM * (singConst d 1 * r ^ ((d : ℝ) - 1)) := by
    have := singConst_nonneg d (p := 1) (by linarith)
    positivity
  have hnorm : ‖μ * ∫ x, ∫ y, f x y‖ ≤ K * IM * (singConst d 1 * r ^ ((d : ℝ) - 1)) := by
    rw [← ofReal_norm] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff hval).1 hbound
  refine hnorm.trans ?_
  -- constants
  have hsd := Real.sqrt_nonneg d
  have hK' : K ≤ lam ^ d * ((1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d) := by
    simp only [K, sliceConst]
    have h1 : 1 + lam * Real.sqrt d ≤ lam * (1 + Real.sqrt d) := by nlinarith
    calc (1 + lam * Real.sqrt d) ^ (d : ℝ) * hypConst d d
        ≤ (lam * (1 + Real.sqrt d)) ^ (d : ℝ) * hypConst d d := by
          have := hypConst_nonneg d d
          gcongr
      _ = _ := by rw [Real.mul_rpow h0.le (by positivity), Real.rpow_natCast]; ring
  have hr' : r ^ ((d : ℝ) - 1) ≤ lam ^ d * (Real.sqrt d) ^ ((d : ℝ) - 1) := by
    simp only [r]
    rw [Real.mul_rpow h0.le hsd]
    gcongr
    calc lam ^ ((d : ℝ) - 1) ≤ lam ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlam (by linarith)
      _ = lam ^ d := Real.rpow_natCast _ _
  have hs1 := singConst_nonneg d (p := 1) (by linarith)
  have hX : 0 ≤ (1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d := by
    have := hypConst_nonneg d d; positivity
  calc K * IM * (singConst d 1 * r ^ ((d : ℝ) - 1))
      ≤ (lam ^ d * ((1 + Real.sqrt d) ^ (d : ℝ) * hypConst d d)) * IM *
          (singConst d 1 * (lam ^ d * (Real.sqrt d) ^ ((d : ℝ) - 1))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hK' hIM) (mul_le_mul_of_nonneg_left hr' hs1)
          (mul_nonneg hs1 (by positivity)) (mul_nonneg (mul_nonneg (by positivity) hX) hIM)
    _ = intConst d * IM * lam ^ (2 * d) := by
        rw [intConst, two_mul, pow_add]; ring

/-- **DH23 Lemma 6.7 (1)** (`NTintlem`, (NTintlem1), L1147–L1150): for `d ≥ 2`, `λ ≥ 1`, `μ > 0`,
`Φ` with `|Φ| ≤ D` (part of (NTphibounds)) and `ψ ∈ L¹`,
`|μ ∫∫ ψ(μ⟨x,y⟩) χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(x,y) e(ξ·x + ζ·y) dx dy| ≤ C D ‖ψ‖_{L¹} λ^{2d}`,
uniformly in `(a, b, ξ, ζ)`. -/
theorem ntintlem_one (hd : 2 ≤ d) {N : ℕ} {D lam μ : ℝ} (hlam : 1 ≤ lam) (hμ : 0 < μ)
    {Φ : Mom d → Mom d → ℂ} (hΦ : NTBounds N D Φ) {ψ : ℝ → ℂ} (hψm : Measurable ψ)
    (hψ : Integrable ψ) (a b ξ ζ : Mom d) :
    ‖μ * ∫ x, ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y‖ ≤
      intConst d * D * (∫ u, ‖ψ u‖) * lam ^ (2 * d) := by
  have hD := hΦ.nonneg
  have h := ntintlem_one_gen hd hlam hμ (Ψ := fun u x y => ψ u * Φ x y)
    (M := fun u => D * ‖ψ u‖) (measurable_const.mul hψm.norm) (hψ.norm.const_mul D)
    (fun u x y => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΦ.norm_le x y) (norm_nonneg _)) a b ξ ζ
  have he : (fun x => ∫ y, ψ (μ * inner ℝ x y) * amp lam Φ a b ξ ζ x y) =
      fun x => ∫ y, (fun u x y => ψ u * Φ x y) (μ * inner ℝ x y) x y *
        (chiScaled lam (x - a) * chiScaled lam (y - b) *
          (Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ) : ℂ)) := by
    funext x
    congr 1
    funext y
    simp only [amp]
    ring
  rw [he]
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

end WaveTurbulence.NTSP
