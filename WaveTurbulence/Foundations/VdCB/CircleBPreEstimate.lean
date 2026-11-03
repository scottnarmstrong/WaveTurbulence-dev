/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSelectedMain
public import WaveTurbulence.Foundations.VdCB.BProcessNegative
public import WaveTurbulence.Foundations.VdCB.FrequencyNormalization
public import WaveTurbulence.Foundations.VdCB.CircleSourceScales

/-!
# The direct circle B-process estimate before radius optimization

Every critical equation, derivative identity, frequency comparison,
weighted A-estimate and endpoint count is proved. Only the positive
radius and first-derivative splitting threshold remain free numeric choices.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The actual translated-circle source sum has its B-after-A³ main scale
plus fully explicit analytic errors. There are no assumed sum estimates. -/
theorem norm_sum_circleColumnPhase_le_BScale_add_error {R h U c r t : ℝ}
    (hU : 1 ≤ U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hr : 0 < r) (ht : 0 < t)
    {a b : ℕ} (hab : a ≤ b)
    (ha : R + c - 2 * U ≤ a) (hb : (b : ℝ) ≤ R + c - U)
    (haOct : R + c - R * (1 - 1 / Real.sqrt 2) ≤ a)
    (hinner : (a : ℝ) + r ≤ b - r) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c))‖ ≤
      154618822665 * circleBScale R h U + circleBError R h U r t := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  let F := circleColumnExtension R h U hU0 c
  let μ := circleCurvatureLower R h U
  let Λ := circleCurvatureUpper R h U
  let M := circleThirdScale R h U
  have hμ : 0 < μ := by dsimp only [μ, circleCurvatureLower]; positivity
  have hΛ : 0 ≤ Λ := by dsimp only [Λ, circleCurvatureUpper]; positivity
  have hM0 : 0 ≤ M := by dsimp only [M, circleThirdScale]; positivity
  have hF : ContDiff ℝ 3 F := (contDiff_circleColumnExtension hU0 hUR h c).of_le (by simp)
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hF1 : ContDiff ℝ 1 (deriv F) := hF2.deriv'
  have hblock (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : R + c - x ∈ Icc U (2 * U) :=
    column_interval_reflection_mem ha hb hx
  have hcurv (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : μ ≤ -deriv (deriv F) x ∧ -deriv (deriv F) x ≤ Λ :=
    (circleColumnExtension_curvature_bounds hU0 hUR hh (hblock x hx)).1
  have hM (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : |iteratedDeriv 3 F x| ≤ M :=
    (circleColumnExtension_curvature_bounds hU0 hUR hh (hblock x hx)).2
  have hg1 : ContDiff ℝ 1 (fun x => -deriv F x) := hF1.neg
  have hmono : MonotoneOn (fun x => -deriv F x) (Icc (a : ℝ) b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hg1.continuous.continuousOn
      (hg1.differentiable (by norm_num)).differentiableOn
    intro x hx
    rw [deriv.fun_neg]
    exact hμ.le.trans (hcurv x (interior_subset hx)).1
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hAB := hmono (left_mem_Icc.mpr habR) (right_mem_Icc.mpr habR) habR
  obtain ⟨m, N, hm0, hm1, hN0, hN1, hNsize⟩ := exists_frequency_normalization hAB
  have hrange (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : 0 ≤ -deriv F x - m ∧ -deriv F x - m ≤ N := by
    have hl := hmono (left_mem_Icc.mpr habR) hx hx.1
    have hu := hmono hx (right_mem_Icc.mpr habR) hx.2
    constructor <;> linarith only [hl, hu, hm0, hN1]
  obtain ⟨z, hz, hbound⟩ := exists_BProcess_negative hF hab m N hr hμ hΛ hM0 ht hinner hrange
    (by linarith only [hm1]) (by linarith only [hN0]) hcurv hM
  have hmain := norm_circle_selected_main_le hU hUR hh hr ha hb haOct hinner m N z hrange hz
  have hupper := (convex_Icc (a : ℝ) b).image_sub_le_mul_sub_of_deriv_le hg1.continuous.continuousOn
    (hg1.differentiable (by norm_num)).differentiableOn
    (fun x hx => by rw [deriv.fun_neg]; exact (hcurv x (interior_subset hx)).2)
    a (left_mem_Icc.mpr habR) b (right_mem_Icc.mpr habR) habR
  have hlen : (b : ℝ) - a ≤ U := by linarith only [ha, hb]
  have hN : (N : ℝ) ≤ Λ * U + 2 := by
    have hh := mul_le_mul_of_nonneg_left hlen hΛ
    linarith only [hNsize, hupper, hh]
  let Q := Λ * U + 3
  have hQ : 1 ≤ Q := by dsimp only [Q]; nlinarith only [mul_nonneg hΛ hU0.le]
  have hNQ : (N : ℝ) + 1 ≤ Q := by dsimp only [Q]; linarith only [hN]
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogNp : Real.log ((N : ℝ) + 1) ≤ Real.log Q := Real.log_le_log (by positivity) hNQ
  have hlogN : Real.log N ≤ Real.log Q := by
    by_cases hzero : N = 0
    · simpa only [hzero, Nat.cast_zero, Real.log_zero] using hlogQ
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hzero) (by linarith only [hNQ])
  have hfreq : (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1 ≤
      (2 + 6 * Real.log Q) / (2 * Real.pi) + 1 := by
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith only [hlogNp, hlogN]
  have hstationary : ((N : ℝ) + 1) * (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r))) ≤
      Q * (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r))) :=
    mul_le_mul_of_nonneg_right hNQ (by positivity)
  have hsource : (∑ n ∈ Finset.Ico a b, expPhase (F ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Ico a b, expPhase (circleColumnPhase R h ((n : ℝ) + 1 - c)) := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ico.mp hn
    have hx : (n : ℝ) + 1 ∈ Icc (a : ℝ) b := by
      have h1 : a ≤ n + 1 := by omega
      have h2 : n + 1 ≤ b := by omega
      constructor <;> exact_mod_cast ‹_›
    dsimp only [F]
    rw [(circleColumnExtension_eventuallyEq (R := R) (h := h) (c := c) hU0 (hblock _ hx)).eq_of_nhds]
  let D := ∑ ν ∈ stationaryFrequencies (fun x => -F x - (m : ℝ) * x) a b r N,
    expPhase (F (z ν) + ((m : ℝ) + ν) * z ν - 1 / 8) /
      (Real.sqrt (-deriv (deriv F) (z ν)) : ℂ)
  rw [← hsource]
  calc
    _ = ‖((∑ n ∈ Finset.Ico a b, expPhase (F ((n : ℝ) + 1))) - D) + D‖ := by congr 1; ring
    _ ≤ ‖(∑ n ∈ Finset.Ico a b, expPhase (F ((n : ℝ) + 1))) - D‖ + ‖D‖ := norm_add_le _ _
    _ ≤ (((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        2 * (Λ * r + 3) * (2 * t / μ + 2 / (Real.pi * t)) +
        ((N : ℝ) + 1) * (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r)))) +
        154618822665 * circleBScale R h U := add_le_add hbound hmain
    _ ≤ (((2 + 6 * Real.log Q) / (2 * Real.pi) + 1) +
        2 * (Λ * r + 3) * (2 * t / μ + 2 / (Real.pi * t)) +
        Q * (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r)))) +
        154618822665 * circleBScale R h U :=
      add_le_add (add_le_add (add_le_add hfreq le_rfl) hstationary) le_rfl
    _ = _ := by dsimp only [circleBError, Q, μ, Λ, M]; ring

end WaveTurbulence.VdCB
