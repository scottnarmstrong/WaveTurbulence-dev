/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearMeasurable
public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearScale
public import WaveTurbulence.Foundations.WeylSums.RefinedMomentPowers
public import WaveTurbulence.Foundations.WeylSums.WindowScaling

/-! # The bilinear minor-arc integral before substituting the time scale -/

public section
open MeasureTheory
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- Finite-order joint amplitudes satisfy the sharp bilinear interval
bound with the source width factor `width^(4d)`. Time measurability is the
only time regularity assumption. The positive lower support constant `c₀` is arbitrary and may enter `C`. -/
theorem exists_weighted_bilinear_minor_integral_bound_of_cutoff (d : ℕ) (hd : 3 ≤ d)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (ε : ℝ) (hε : 0 < ε) (hεd : ε < (d : ℝ)-2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L width B : ℝ, 2 ≤ L → 1 ≤ width → 0 < B →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ),
      (∀ x y, Measurable (fun s => Φ s x y)) →
      (∀ s, ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s))) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ s, ∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ D) →
      ∀ a b ξ ζ : Mom d,
      IntegrableOn (fun s : ℝ => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖)
        {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ B} ∧
      (∫ s : ℝ in {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ B}, ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ≤
        C * D * width^(4*d) * L^(2*(d : ℝ)) * (B/(4*L^2))^((d : ℝ)-1-ε) := by
  let Q := max (1 : ℝ) (1/c₀)
  have hQ : 1 ≤ Q := le_max_left _ _
  have hQp : 0 < Q := by linarith
  have hcQ : 1 ≤ c₀*Q := by
    have hh := (div_le_iff₀ hc₀).mp (le_max_right (1 : ℝ) (1/c₀))
    nlinarith only [hh]
  let p : ℝ := 2*(d : ℝ)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 4 < p := by dsimp [p]; linarith only [hdR]
  have hεp : ε < p/2-2 := by dsimp [p]; linarith only [hεd]
  obtain ⟨C₀,hC₀,hpoint⟩ := exists_weightedBilinearLatticeSum_pointwise_bound_at_scale d hd
  obtain ⟨C₁,hC₁,hint⟩ := exists_weylSupremum_refined_moment p ε hp hε hεp
  let C := C₀ * C₁ * (4*(12*Q)^(p-2))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro L width B hL hw hB Φ htime hΦ D hD hderiv a b ξ ζ
  have hwp : 0 < width := by linarith
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  let M := 12*Q*width*L
  let c := 4*L^2
  let T := B/c
  have hQwidth : 1 ≤ Q*width := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hw),hQ,hw]
  have hM : 2 ≤ M := by
    dsimp [M]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hQwidth) hLp.le,hL]
  have hMp : 0 < M := by dsimp [M]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hT : 0 < T := div_pos hB hc
  let f : ℝ → ℝ := fun t => weylSupremum M t ^ p
  obtain ⟨hi,hi_bound⟩ := hint M T hM hT
  have hf (t : ℝ) : 0 ≤ f t := Real.rpow_nonneg (weylSupremum_nonneg hMp t) _
  have hA : 1/M ≤ (c₀*L)/c := by
    apply (div_le_div_iff₀ hMp hc).mpr
    dsimp [M,c]
    have hcw : 1 ≤ c₀*Q*width := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hcQ) hwp.le,hw]
    have hh := mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hcw)
    nlinarith only [hh,sq_nonneg L]
  have hi_small : IntegrableOn f {t : ℝ | (c₀*L)/c ≤ |t| ∧ |t| ≤ B/c} :=
    hi.mono_set (fun t ht => ⟨hA.trans ht.1, ht.2⟩)
  have hi_comp := integrableOn_abs_window_div (c₀*L) B hc hi_small
  have hpt (s : ℝ) : ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖ ≤ (C₀*D*width^(2*d)) * f (s/c) := by
    have hh := hpoint Q hQ L width hL1 hw Φ s (hΦ s) D hD (hderiv s) a b ξ ζ
    have hpcast : p = ((2*d : ℕ) : ℝ) := by dsimp [p]; push_cast; ring
    simpa only [f, M, c, hpcast, Real.rpow_natCast] using hh
  have hfm : AEStronglyMeasurable (fun s : ℝ => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖)
      (volume.restrict {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ B}) :=
    (measurable_weightedBilinearLatticeSum hLp hwp Φ htime a b ξ ζ).norm.aestronglyMeasurable
  have hi_sum : IntegrableOn (fun s : ℝ => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖)
      {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ B} := by
    apply (hi_comp.const_mul (C₀*D*width^(2*d))).mono' hfm
    filter_upwards [] with s
    rw [norm_norm]
    exact hpt s
  refine ⟨hi_sum, ?_⟩
  have hscale : c * M^(p-2) = (4*(12*Q)^(p-2)) * width^(p-2) * L^p := by
    dsimp [c,M]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 12*Q*width) hLp.le,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 12*Q) hwp.le,
      Real.rpow_sub hLp, Real.rpow_two]
    field_simp [hLp.ne']
  have hwidth : width^(2*d) * width^(p-2) ≤ width^(4*d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hwp, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hw
    dsimp [p]
    push_cast
    linarith
  have hcoef : 0 ≤ C₀*D*width^(2*d) := by positivity
  calc
    _ ≤ ∫ s : ℝ in {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ B}, (C₀*D*width^(2*d))*f (s/c) :=
      integral_mono_ae hi_sum (hi_comp.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = (C₀*D*width^(2*d)) * ∫ s : ℝ in {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ B}, f (s/c) := integral_const_mul _ _
    _ ≤ (C₀*D*width^(2*d)) * (c * ∫ t : ℝ in {t : ℝ | 1/M ≤ |t| ∧ |t| ≤ T}, f t) :=
      mul_le_mul_of_nonneg_left (integral_abs_window_div_le hf (c₀*L) B (1/M) T hc hi hA le_rfl) hcoef
    _ ≤ (C₀*D*width^(2*d)) * (c * (C₁*M^(p-2)*T^(p/2-1-ε))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi_bound hc.le) hcoef
    _ = C*D*(width^(2*d)*width^(p-2))*L^p*T^(p/2-1-ε) := by
      calc
        _ = (C₀*D*width^(2*d)*C₁) * (c*M^(p-2)) * T^(p/2-1-ε) := by ring
        _ = _ := by rw [hscale]; dsimp [C]; ring
    _ ≤ C*D*width^(4*d)*L^p*T^(p/2-1-ε) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (mul_nonneg hC.le hD))
          (Real.rpow_nonneg hLp.le _)) (Real.rpow_nonneg hT.le _)
    _ = _ := by
      dsimp [p,T,c]
      congr 2
      ring

end WaveTurbulence.WeylSums
