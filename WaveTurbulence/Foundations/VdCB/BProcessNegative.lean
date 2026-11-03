/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.BProcessSelected
public import WaveTurbulence.Foundations.VdCB.StationaryFrequencyCount
public import WaveTurbulence.Foundations.VdCB.IntegerPhase

/-!
# Selected B-process for negative curvature

Integer normalization and conjugation give the source circle convention.
The critical points are proved to exist, and the omitted-frequency count
is controlled by the actual upper curvature bound.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- A negative-curvature B-process estimate with all critical points
constructed and all endpoint-frequency costs explicit. The integer `m`
and natural `N` only normalize actual derivative values. -/
theorem exists_BProcess_negative {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b : ℕ} (hab : a ≤ b) (m : ℤ) (N : ℕ) {r μ Λ M t : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) (hΛ : 0 ≤ Λ) (hM0 : 0 ≤ M) (ht : 0 < t)
    (hinner : (a : ℝ) + r ≤ b - r)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ -deriv f x - m ∧ -deriv f x - m ≤ N)
    (ha0 : -deriv f a - m ≤ 1) (hb0 : (N : ℝ) - 1 ≤ -deriv f b - m)
    (hcurv : ∀ x ∈ Icc (a : ℝ) b, μ ≤ -deriv (deriv f) x ∧ -deriv (deriv f) x ≤ Λ)
    (hM : ∀ x ∈ Icc (a : ℝ) b, |iteratedDeriv 3 f x| ≤ M) :
    ∃ c : ℤ → ℝ,
      (∀ ν ∈ stationaryFrequencies (fun x => -f x - (m : ℝ) * x) a b r N,
        (a : ℝ) ≤ c ν - r ∧ c ν + r ≤ b ∧ deriv f (c ν) = -((m : ℝ) + ν)) ∧
      ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        ∑ ν ∈ stationaryFrequencies (fun x => -f x - (m : ℝ) * x) a b r N,
          expPhase (f (c ν) + ((m : ℝ) + ν) * c ν - 1 / 8) /
            (Real.sqrt (-deriv (deriv f) (c ν)) : ℂ)‖ ≤
        ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        (2 * (Λ * r + 3)) * (2 * t / μ + 2 / (Real.pi * t)) +
        ((N : ℝ) + 1) * (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r))) := by
  let g : ℝ → ℝ := fun x => -f x - (m : ℝ) * x
  have hg : ContDiff ℝ 3 g := hf.neg.sub (contDiff_const.mul contDiff_id)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hneg2 : ContDiff ℝ 2 (fun x => -f x) := hf2.neg
  have hdneg := hneg2.differentiable (by norm_num)
  have hd1 (x : ℝ) : deriv g x = -deriv f x - m := by
    dsimp only [g]
    rw [deriv_sub_frequency hdneg, deriv.fun_neg]
  have hd2 (x : ℝ) : deriv (deriv g) x = -deriv (deriv f) x := by
    dsimp only [g]
    rw [deriv_deriv_sub_frequency hneg2, deriv.fun_neg', deriv.fun_neg]
  have hd3 (x : ℝ) : iteratedDeriv 3 g x = -iteratedDeriv 3 f x := by
    dsimp only [g]
    rw [iteratedDeriv_three_sub_frequency hneg2, iteratedDeriv_fun_neg]
  have hgrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv g x ∧ deriv g x ≤ N := by
    simpa only [hd1] using hrange
  have hgcurv : ∀ x ∈ Icc (a : ℝ) b, μ ≤ deriv (deriv g) x := by
    intro x hx
    rw [hd2]
    exact (hcurv x hx).1
  have hgM : ∀ x ∈ Icc (a : ℝ) b, |iteratedDeriv 3 g x| ≤ M := by
    simpa only [hd3, abs_neg] using hM
  obtain ⟨c, hc, hbound⟩ := exists_BProcess_selected hg hab N hr hμ hM0 ht hinner hgrange hgcurv hgM
  let S := stationaryFrequencies g a b r N
  have hcount := card_compl_stationaryFrequencies_le_of_curvature hg2 hr.le hΛ hinner N
    (by simpa only [hd1] using ha0) (by simpa only [hd1] using hb0)
    (by intro x hx; rw [hd2]; exact (hcurv x hx).2)
  have hcard : (S.card : ℝ) ≤ (N : ℝ) + 1 := by
    have hh := Finset.card_le_card (stationaryFrequencies_subset g a b r N)
    have hhR : (S.card : ℝ) ≤ ((Finset.Icc 0 (N : ℤ)).card : ℝ) := by exact_mod_cast hh
    have hcc : ((Finset.Icc 0 (N : ℤ)).card : ℝ) = (N : ℝ) + 1 := by
      have hnat : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
        rw [Int.card_Icc]
        omega
      exact_mod_cast hnat
    rwa [hcc] at hhR
  have hsource : (starRingEnd ℂ) (∑ n ∈ Finset.Ico a b, expPhase (g ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1)) := by
    have heq : (∑ n ∈ Finset.Ico a b, expPhase (g ((n : ℝ) + 1))) =
        ∑ n ∈ Finset.Ico a b, expPhase (((-m : ℤ) : ℝ) * ((n : ℝ) + 1) - f ((n : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [g]
      congr 1
      push_cast
      ring
    rw [heq]
    exact conj_sum_expPhase_int_linear_sub f (-m) a b
  have hmain : (starRingEnd ℂ) (∑ ν ∈ S, expPhase (g (c ν) - (ν : ℝ) * c ν + 1 / 8) /
      (Real.sqrt (deriv (deriv g) (c ν)) : ℂ)) =
      ∑ ν ∈ S, expPhase (f (c ν) + ((m : ℝ) + ν) * c ν - 1 / 8) /
        (Real.sqrt (-deriv (deriv f) (c ν)) : ℂ) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [map_div₀, Complex.conj_ofReal, conj_expPhase, hd2]
    dsimp only [g]
    congr 2
    ring
  refine ⟨c, ?_, ?_⟩
  · intro ν hν
    obtain ⟨ha, hb, heq⟩ := hc ν hν
    refine ⟨ha, hb, ?_⟩
    rw [hd1] at heq
    linarith only [heq]
  · have heq : (starRingEnd ℂ)
        ((∑ n ∈ Finset.Ico a b, expPhase (g ((n : ℝ) + 1))) -
         ∑ ν ∈ S, expPhase (g (c ν) - (ν : ℝ) * c ν + 1 / 8) /
           (Real.sqrt (deriv (deriv g) (c ν)) : ℂ)) =
        ((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
         ∑ ν ∈ S, expPhase (f (c ν) + ((m : ℝ) + ν) * c ν - 1 / 8) /
           (Real.sqrt (-deriv (deriv f) (c ν)) : ℂ)) := by rw [map_sub, hsource, hmain]
    change ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ S, expPhase (f (c ν) + ((m : ℝ) + ν) * c ν - 1 / 8) /
        (Real.sqrt (-deriv (deriv f) (c ν)) : ℂ)‖ ≤ _
    rw [← heq, Complex.norm_conj]
    apply hbound.trans
    apply add_le_add
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcount (by positivity))
    · exact mul_le_mul_of_nonneg_right hcard (by positivity)

end WaveTurbulence.VdCB
