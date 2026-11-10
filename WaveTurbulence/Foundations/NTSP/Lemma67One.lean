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

end WaveTurbulence.NTSP
