/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.StationaryFrequencies

/-!
# B-process with the stationary frequencies selected from the source phase

Intermediate value supplies the actual critical points. The uniform
second-derivative estimate handles every omitted frequency, including
frequencies whose critical points approach the endpoints.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- An actual finite B-process approximation under smoothness, curvature
and third-derivative bounds alone. The selected frequencies are defined
from actual derivative values on the radius-trimmed source interval. -/
theorem exists_BProcess_selected {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b : ℕ} (hab : a ≤ b) (N : ℕ) {r μ M t : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) (hM0 : 0 ≤ M) (ht : 0 < t)
    (hinner : (a : ℝ) + r ≤ b - r)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hcurv : ∀ x ∈ Icc (a : ℝ) b, μ ≤ deriv (deriv f) x)
    (hM : ∀ x ∈ Icc (a : ℝ) b, |iteratedDeriv 3 f x| ≤ M) :
    ∃ c : ℤ → ℝ,
      (∀ ν ∈ stationaryFrequencies f a b r N,
        (a : ℝ) ≤ c ν - r ∧ c ν + r ≤ b ∧ deriv f (c ν) = ν) ∧
      ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        ∑ ν ∈ stationaryFrequencies f a b r N,
          expPhase (f (c ν) - (ν : ℝ) * c ν + 1 / 8) /
            (Real.sqrt (deriv (deriv f) (c ν)) : ℂ)‖ ≤
        ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        ((Finset.Icc 0 (N : ℤ) \ stationaryFrequencies f a b r N).card : ℝ) *
          (2 * t / μ + 2 / (Real.pi * t)) +
        ((stationaryFrequencies f a b r N).card : ℝ) *
          (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r))) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  obtain ⟨c, hc⟩ := exists_stationary_centers hf2 hinner N
  refine ⟨c, hc, ?_⟩
  let S := stationaryFrequencies f a b r N
  have hh := norm_exponential_sum_sub_BProcess_uniform_le hf hab N S
    (stationaryFrequencies_subset f a b r N) c (fun _ => r) hμ hM0 ht hrange hcurv
    (fun _ _ => hr) (fun ν hν => (hc ν hν).1) (fun ν hν => (hc ν hν).2.1)
    (fun ν hν => (hc ν hν).2.2)
    (fun ν hν x hx => hM x ⟨(hc ν hν).1.trans hx.1, hx.2.trans (hc ν hν).2.1⟩)
  have hsum : (∑ ν ∈ S, (2 * Real.pi / 3 * M * r ^ 4 +
      2 / (Real.pi * (deriv (deriv f) (c ν) * r)) + 2 / (Real.pi * (μ * r)))) ≤
      (S.card : ℝ) * (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r))) := by
    calc
      _ ≤ ∑ _ν ∈ S, (2 * Real.pi / 3 * M * r ^ 4 + 4 / (Real.pi * (μ * r))) := by
        apply Finset.sum_le_sum
        intro ν hν
        have hcI : c ν ∈ Icc (a : ℝ) b :=
          ⟨by linarith [(hc ν hν).1], by linarith [(hc ν hν).2.1]⟩
        have hq := hcurv (c ν) hcI
        have hden : Real.pi * (μ * r) ≤ Real.pi * (deriv (deriv f) (c ν) * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hr.le) Real.pi_pos.le
        have hterm := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
          (by positivity : 0 < Real.pi * (μ * r)) hden
        calc
          _ ≤ (2 * Real.pi / 3 * M * r ^ 4 + 2 / (Real.pi * (μ * r))) +
              2 / (Real.pi * (μ * r)) := add_le_add (add_le_add le_rfl hterm) le_rfl
          _ = _ := by ring
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  exact hh.trans (add_le_add le_rfl hsum)

end WaveTurbulence.VdCB
