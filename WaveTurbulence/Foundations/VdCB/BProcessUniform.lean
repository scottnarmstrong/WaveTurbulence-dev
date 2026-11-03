/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.BProcessFinite
public import WaveTurbulence.Foundations.VdCB.SecondDerivativeIntegral

/-!
# A finite B-process bound without endpoint separation

Every omitted frequency is bounded by the uniform second-derivative
integral estimate. Critical points may approach the interval endpoints;
their cost is explicit in the number of omitted frequencies.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Sharp B-process with a uniform curvature cost for the omitted
frequencies. No derivative-distance premise is imposed on the complement. -/
theorem norm_exponential_sum_sub_BProcess_uniform_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b : ℕ} (hab : a ≤ b) (N : ℕ) (S : Finset ℤ) (hS : S ⊆ Finset.Icc 0 (N : ℤ))
    (c r : ℤ → ℝ) {μ M t : ℝ} (hμ : 0 < μ) (hM0 : 0 ≤ M) (ht : 0 < t)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hcurv : ∀ x ∈ Icc (a : ℝ) b, μ ≤ deriv (deriv f) x)
    (hr : ∀ ν ∈ S, 0 < r ν)
    (ha : ∀ ν ∈ S, (a : ℝ) ≤ c ν - r ν) (hb : ∀ ν ∈ S, c ν + r ν ≤ b)
    (hc : ∀ ν ∈ S, deriv f (c ν) = ν)
    (hM : ∀ ν ∈ S, ∀ x ∈ Icc (c ν - r ν) (c ν + r ν), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ S, expPhase (f (c ν) - (ν : ℝ) * c ν + 1 / 8) /
        (Real.sqrt (deriv (deriv f) (c ν)) : ℂ)‖ ≤
      ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
      ((Finset.Icc 0 (N : ℤ) \ S).card : ℝ) * (2 * t / μ + 2 / (Real.pi * t)) +
      ∑ ν ∈ S, (2 * Real.pi / 3 * M * r ν ^ 4 +
        2 / (Real.pi * (deriv (deriv f) (c ν) * r ν)) + 2 / (Real.pi * (μ * r ν))) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hsec (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : 0 ≤ deriv (deriv f) x :=
    hμ.le.trans (hcurv x hx)
  have htrunc := norm_sum_sub_truncated_poisson_le hf2 hab N hrange hsec
  have hstat := norm_sum_integral_sub_stationary_dual_le hf S c r hμ hM0 hcurv hr ha hb hc hM
  let T := Finset.Icc 0 (N : ℤ) \ S
  let I : ℤ → ℂ := fun ν => ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)
  have hnon (ν : ℤ) (_hν : ν ∈ T) : ‖I ν‖ ≤ 2 * t / μ + 2 / (Real.pi * t) := by
    have hg : ContDiff ℝ 2 (fun x => f x - (ν : ℝ) * x) := hf2.sub (contDiff_const.mul contDiff_id)
    exact norm_integral_expPhase_le_of_second_deriv_pos hg habR hμ ht
      (by simpa only [deriv_deriv_sub_frequency hf2] using hcurv)
  have hnonSum : ‖∑ ν ∈ T, I ν‖ ≤ (T.card : ℝ) * (2 * t / μ + 2 / (Real.pi * t)) := by
    calc
      _ ≤ ∑ ν ∈ T, ‖I ν‖ := norm_sum_le _ _
      _ ≤ ∑ _ν ∈ T, (2 * t / μ + 2 / (Real.pi * t)) := Finset.sum_le_sum hnon
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : (∑ ν ∈ Finset.Icc 0 (N : ℤ), I ν) =
      (∑ ν ∈ S, I ν) + ∑ ν ∈ T, I ν := by
    have hh := Finset.sum_sdiff hS (f := I)
    dsimp only [T]
    linear_combination -hh
  let P := ∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))
  let D := ∑ ν ∈ S, expPhase (f (c ν) - (ν : ℝ) * c ν + 1 / 8) /
    (Real.sqrt (deriv (deriv f) (c ν)) : ℂ)
  change ‖P - D‖ ≤ _
  have heq : P - D = (P - ∑ ν ∈ Finset.Icc 0 (N : ℤ), I ν) +
      (∑ ν ∈ T, I ν) + ((∑ ν ∈ S, I ν) - D) := by rw [hsplit]; ring
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add htrunc hnonSum) hstat)

end WaveTurbulence.VdCB
