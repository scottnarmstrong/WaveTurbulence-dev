/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearMeasurable
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetricMoment
public import WaveTurbulence.Foundations.WeylSums.WindowScaling

/-! # The global weighted bilinear integral on the square time scale -/

public section
open MeasureTheory
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- DH23 Lemma 6.6(1)'s analytic estimate, valid on the larger window
`|s|≤L²`. Only finite spatial regularity and time measurability are assumed. -/
theorem exists_weighted_bilinear_global_integral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L width : ℝ, 2 ≤ L → 1 ≤ width →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ),
      (∀ x y, Measurable (fun s => Φ s x y)) →
      (∀ s, ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s))) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ s, ∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ D) →
      ∀ a b ξ ζ : Mom d,
      IntegrableOn (fun s => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) {s : ℝ | |s| ≤ L^2} ∧
      (∫ s in {s : ℝ | |s| ≤ L^2}, ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ≤
        C*D*width^(4*d)*L^(2*(d : ℝ)) := by
  let p : ℝ := 2*(d : ℝ)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 4 < p := by dsimp [p]; linarith
  obtain ⟨C₀,hC₀,hpoint⟩ := exists_weightedBilinearLatticeSum_pointwise_bound d hd
  obtain ⟨C₁,hC₁,hglobal⟩ := exists_weyl_symmetric_moment_bound p hp
  let C := C₀*C₁*(4*(12 : ℝ)^(p-2))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro L width hL hw Φ htime hΦ D hD hderiv a b ξ ζ
  have hLp : 0 < L := by linarith
  have hwp : 0 < width := by linarith
  let M := 12*width*L
  let J := 4*L^2
  let f := fun t : ℝ => weylSupremum M t^p
  have hMp : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by
    have hh : 1 ≤ width*L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr (show 1 ≤ L by linarith)),hw,hL]
    dsimp [M]
    nlinarith only [hh]
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨hi,hb⟩ := hglobal M hM1
  have hi' : IntegrableOn f {t : ℝ | 0 ≤ |t| ∧ |t| ≤ 1/2} := by
    simpa only [abs_nonneg,true_and] using hi
  have hB : L^2/J ≤ 1/2 := by
    apply (div_le_iff₀ hJ).mpr
    dsimp [J]
    nlinarith only [sq_nonneg L]
  have hismall : IntegrableOn f {t : ℝ | 0/J ≤ |t| ∧ |t| ≤ L^2/J} :=
    hi'.mono_set (fun t ht => ⟨by simpa only [zero_div] using ht.1,ht.2.trans hB⟩)
  have hic₀ := integrableOn_abs_window_div 0 (L^2) hJ hismall
  have hic : IntegrableOn (fun s => f (s/J)) {s : ℝ | |s| ≤ L^2} := by
    simpa only [abs_nonneg,true_and] using hic₀
  have hpt (s : ℝ) : ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖ ≤ C₀*D*width^(2*d)*f (s/J) := by
    have hh := hpoint L width (by linarith) hw Φ s (hΦ s) D hD (hderiv s) a b ξ ζ
    have hpcast : p = ((2*d : ℕ) : ℝ) := by dsimp [p]; push_cast; ring
    simpa only [f,M,J,hpcast,Real.rpow_natCast] using hh
  have hiSum : IntegrableOn (fun s => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) {s : ℝ | |s| ≤ L^2} := by
    apply (hic.const_mul (C₀*D*width^(2*d))).mono'
      (measurable_weightedBilinearLatticeSum hLp hwp Φ htime a b ξ ζ).norm.aestronglyMeasurable
    filter_upwards [] with s
    rw [norm_norm]
    exact hpt s
  refine ⟨hiSum,?_⟩
  have hscale : J*M^(p-2) = (4*(12 : ℝ)^(p-2))*width^(p-2)*L^p := by
    dsimp [J,M]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 12*width) hLp.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hwp.le,Real.rpow_sub hLp,Real.rpow_two]
    field_simp [hLp.ne']
  have hwidth : width^(2*d)*width^(p-2) ≤ width^(4*d) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hwp,← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hw
    dsimp [p]
    push_cast
    linarith
  have hmass : (∫ s in {s : ℝ | |s| ≤ L^2}, f (s/J)) ≤ J*(C₁*M^(p-2)) := by
    have hh := integral_abs_window_div_le (fun t => Real.rpow_nonneg (weylSupremum_nonneg hMp t) p)
      0 (L^2) 0 (1/2) hJ hi' (by simp) hB
    have hh' : (∫ s in {s : ℝ | |s| ≤ L^2}, f (s/J)) ≤ J*∫ t in {t : ℝ | |t| ≤ 1/2}, f t := by
      simpa only [abs_nonneg,true_and] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hb hJ.le)
  calc
    _ ≤ ∫ s in {s : ℝ | |s| ≤ L^2}, C₀*D*width^(2*d)*f (s/J) :=
      integral_mono_ae hiSum (hic.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = (C₀*D*width^(2*d))*(∫ s in {s : ℝ | |s| ≤ L^2}, f (s/J)) := integral_const_mul _ _
    _ ≤ (C₀*D*width^(2*d))*(J*(C₁*M^(p-2))) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = C*D*(width^(2*d)*width^(p-2))*L^p := by
      calc
        _ = (C₀*D*width^(2*d)*C₁)*(J*M^(p-2)) := by ring
        _ = _ := by rw [hscale]; dsimp [C]; ring
    _ ≤ C*D*width^(4*d)*L^p := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwidth (by dsimp [C]; positivity)) (by positivity)

end WaveTurbulence.WeylSums
