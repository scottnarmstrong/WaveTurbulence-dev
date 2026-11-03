/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Basic

/-!
# The singular integral `∫_{B(a,r)} |x|^{-p} dx`

For `0 ≤ p < d` and `r > 0`, `∫_{B(a,r)} |x|^{-p} dx ≤ (singConst d p) r^{d-p}` uniformly in the
center `a` (`integral_indicator_norm_rpow_le`): split into `B(0,r)`, computed in polar coordinates
(`integral_fun_norm_addHaar`), and the rest, where `|x|^{-p} ≤ r^{-p}`. This is the weight of the
hyperplane reading `δ(⟨x,y⟩) = |x|^{-1} δ_{x^⊥}` in DH23 Lemma 6.7.
-/

public section

noncomputable section

open MeasureTheory Metric Set

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- The constant of the singular integral. -/
@[expose] def singConst (d : ℕ) (p : ℝ) : ℝ :=
  d * ballVol d / ((d : ℝ) - p) + ballVol d

theorem singConst_nonneg (d : ℕ) {p : ℝ} (hp : p < d) : 0 ≤ singConst d p := by
  unfold singConst
  have := ballVol_nonneg d
  have : 0 < (d : ℝ) - p := by linarith
  positivity

theorem integral_ball_zero_norm_rpow {p r : ℝ} (hp0 : 0 ≤ p) (hp : p < d) (hr : 0 < r) :
    ∫ x : Mom d, (Iic r).indicator (fun t => t ^ (-p)) ‖x‖ =
      d * ballVol d * (r ^ ((d : ℝ) - p) / ((d : ℝ) - p)) := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hp; linarith
    · exact h
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  rw [integral_fun_norm_addHaar volume (fun t => (Iic r).indicator (fun t => t ^ (-p)) t)]
  simp only [finrank_euclideanSpace_fin, measureReal_def]
  rw [ballVol, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  congr 2
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (Iic r).indicator (fun t => t ^ (-p)) y =
      ∫ y in Ioc (0 : ℝ) r, y ^ ((d : ℝ) - p - 1) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext y
    by_cases hy : y ∈ Ioc (0 : ℝ) r
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy.1),
        Set.indicator_of_mem (show y ∈ Iic r from hy.2), smul_eq_mul,
        ← Real.rpow_natCast, ← Real.rpow_add hy.1]
      congr 1
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hy]
      by_cases hy0 : y ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hy0, Set.indicator_of_notMem, smul_zero]
        intro h; exact hy ⟨hy0, h⟩
      · rw [Set.indicator_of_notMem hy0]
  rw [h1, ← intervalIntegral.integral_of_le hr.le, integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith), sub_zero, show (d : ℝ) - p - 1 + 1 = (d : ℝ) - p by ring]

theorem integrable_ball_zero_norm_rpow {p r : ℝ} (hp0 : 0 ≤ p) (hp : p < d) (hr : 0 < r) :
    Integrable (fun x : Mom d => (Iic r).indicator (fun t => t ^ (-p)) ‖x‖) := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hp; linarith
    · exact h
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  rw [integrable_fun_norm_addHaar volume (f := fun t => (Iic r).indicator (fun t => t ^ (-p)) t)]
  simp only [finrank_euclideanSpace_fin]
  have hI : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - p - 1)) (Ioc 0 r) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := (d : ℝ) - p - 1) (a := 0) (b := r)
      (by linarith))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).1 this
  refine ((hI.integrable_indicator measurableSet_Ioc).integrableOn).congr_fun ?_ measurableSet_Ioi
  intro y hy
  simp only
  by_cases hyr : y ≤ r
  · rw [Set.indicator_of_mem (show y ∈ Ioc 0 r from ⟨hy, hyr⟩),
      Set.indicator_of_mem (show y ∈ Iic r from hyr), smul_eq_mul, ← Real.rpow_natCast,
      ← Real.rpow_add hy]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · rw [Set.indicator_of_notMem (show y ∉ Ioc 0 r from fun h => hyr h.2),
      Set.indicator_of_notMem (show y ∉ Iic r from hyr), smul_zero]

theorem indicator_norm_rpow_le {p r : ℝ} (hp0 : 0 ≤ p) (hr : 0 < r) (a x : Mom d) :
    (closedBall a r).indicator (fun x => ‖x‖ ^ (-p)) x ≤
      (Iic r).indicator (fun t => t ^ (-p)) ‖x‖ +
        r ^ (-p) * (closedBall a r).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ closedBall a r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    by_cases hxr : ‖x‖ ≤ r
    · rw [Set.indicator_of_mem (show ‖x‖ ∈ Iic r from hxr)]
      have := Real.rpow_nonneg hr.le (-p)
      linarith
    · rw [Set.indicator_of_notMem (show ‖x‖ ∉ Iic r from hxr), zero_add]
      exact Real.rpow_le_rpow_of_nonpos hr (not_le.1 hxr).le (by linarith)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, add_zero]
    by_cases hxr : ‖x‖ ∈ Iic r
    · rw [Set.indicator_of_mem hxr]; exact Real.rpow_nonneg (norm_nonneg _) _
    · rw [Set.indicator_of_notMem hxr]

theorem integrable_indicator_norm_rpow {p r : ℝ} (hp0 : 0 ≤ p) (hp : p < d) (hr : 0 < r)
    (a : Mom d) : Integrable (fun x : Mom d => (closedBall a r).indicator (fun x => ‖x‖ ^ (-p)) x) := by
  have hfin : volume (closedBall a r) ≠ ⊤ := measure_closedBall_lt_top.ne
  refine Integrable.mono' ((integrable_ball_zero_norm_rpow hp0 hp hr).add
    (((integrableOn_const (C := (1 : ℝ)) hfin).integrable_indicator
      measurableSet_closedBall).const_mul (r ^ (-p)))) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (((measurable_norm.pow_const (-p)).indicator measurableSet_closedBall)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)]
    exact indicator_norm_rpow_le hp0 hr a x

/-- `∫_{B(a,r)} |x|^{-p} dx ≤ C r^{d-p}` for `0 ≤ p < d`, uniformly in `a`. -/
theorem integral_indicator_norm_rpow_le {p r : ℝ} (hp0 : 0 ≤ p) (hp : p < d) (hr : 0 < r)
    (a : Mom d) :
    ∫ x : Mom d, (closedBall a r).indicator (fun x => ‖x‖ ^ (-p)) x ≤
      singConst d p * r ^ ((d : ℝ) - p) := by
  have hfin : volume (closedBall a r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hi2 : Integrable (fun x : Mom d => r ^ (-p) * (closedBall a r).indicator (fun _ => (1 : ℝ)) x) :=
    ((integrableOn_const (C := (1 : ℝ)) hfin).integrable_indicator
      measurableSet_closedBall).const_mul (r ^ (-p))
  calc ∫ x : Mom d, (closedBall a r).indicator (fun x => ‖x‖ ^ (-p)) x
      ≤ ∫ x : Mom d, ((Iic r).indicator (fun t => t ^ (-p)) ‖x‖ +
          r ^ (-p) * (closedBall a r).indicator (fun _ => (1 : ℝ)) x) :=
        integral_mono (integrable_indicator_norm_rpow hp0 hp hr a)
          ((integrable_ball_zero_norm_rpow hp0 hp hr).add hi2) (indicator_norm_rpow_le hp0 hr a)
    _ = d * ballVol d * (r ^ ((d : ℝ) - p) / ((d : ℝ) - p)) +
          r ^ (-p) * (r ^ d * ballVol d) := by
        rw [integral_add (integrable_ball_zero_norm_rpow hp0 hp hr) hi2,
          integral_ball_zero_norm_rpow hp0 hp hr, integral_const_mul,
          integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one, measureReal_def,
          Measure.addHaar_closedBall _ _ hr.le, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, ballVol]
    _ = singConst d p * r ^ ((d : ℝ) - p) := by
        have e : r ^ (-p) * r ^ d = r ^ ((d : ℝ) - p) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hr]; ring_nf
        rw [singConst]
        have hdp : (d : ℝ) - p ≠ 0 := by linarith
        field_simp
        rw [← e]
        ring

end WaveTurbulence.NTSP
