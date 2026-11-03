/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.TruncatedPoisson
public import WaveTurbulence.Foundations.VdCB.StationarySum

/-!
# The finite B-process with explicit endpoint separation

Sharp truncated Poisson and sharp stationary phase give the actual
Legendre dual sum. Nonstationary frequencies left in the truncation
range are controlled by their actual distance from the derivative range.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The B-process for a positive-curvature phase, with explicit radius
and endpoint-separation errors. All derivative hypotheses concern the
actual source phase; no transformed exponential-sum estimate is assumed. -/
theorem norm_exponential_sum_sub_BProcess_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b : ℕ} (hab : a ≤ b) (N : ℕ) (S : Finset ℤ) (hS : S ⊆ Finset.Icc 0 (N : ℤ))
    (c r : ℤ → ℝ) {μ M ρ : ℝ} (hμ : 0 < μ) (hM0 : 0 ≤ M) (hρ : 0 < ρ)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hcurv : ∀ x ∈ Icc (a : ℝ) b, μ ≤ deriv (deriv f) x)
    (hr : ∀ ν ∈ S, 0 < r ν)
    (ha : ∀ ν ∈ S, (a : ℝ) ≤ c ν - r ν) (hb : ∀ ν ∈ S, c ν + r ν ≤ b)
    (hc : ∀ ν ∈ S, deriv f (c ν) = ν)
    (hM : ∀ ν ∈ S, ∀ x ∈ Icc (c ν - r ν) (c ν + r ν), |iteratedDeriv 3 f x| ≤ M)
    (hsep : ∀ ν ∈ Finset.Icc 0 (N : ℤ) \ S,
      (∀ x ∈ Icc (a : ℝ) b, ρ ≤ deriv f x - ν) ∨
      (∀ x ∈ Icc (a : ℝ) b, deriv f x - ν ≤ -ρ)) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ S, expPhase (f (c ν) - (ν : ℝ) * c ν + 1 / 8) /
        (Real.sqrt (deriv (deriv f) (c ν)) : ℂ)‖ ≤
      ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
      ((Finset.Icc 0 (N : ℤ) \ S).card : ℝ) / (Real.pi * ρ) +
      ∑ ν ∈ S, (2 * Real.pi / 3 * M * r ν ^ 4 +
        2 / (Real.pi * (deriv (deriv f) (c ν) * r ν)) + 2 / (Real.pi * (μ * r ν))) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd := hf2.differentiable (by norm_num)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hsec (x : ℝ) (hx : x ∈ Icc (a : ℝ) b) : 0 ≤ deriv (deriv f) x :=
    hμ.le.trans (hcurv x hx)
  have htrunc := norm_sum_sub_truncated_poisson_le hf2 hab N hrange hsec
  have hstat := norm_sum_integral_sub_stationary_dual_le hf S c r hμ hM0 hcurv hr ha hb hc hM
  let T := Finset.Icc 0 (N : ℤ) \ S
  let I : ℤ → ℂ := fun ν => ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)
  have hnon (ν : ℤ) (hν : ν ∈ T) : ‖I ν‖ ≤ 1 / (Real.pi * ρ) := by
    have hg : ContDiff ℝ 2 (fun x => f x - (ν : ℝ) * x) := hf2.sub (contDiff_const.mul contDiff_id)
    have hg2 : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv (fun y => f y - (ν : ℝ) * y)) x := by
      simpa only [deriv_deriv_sub_frequency hf2] using hsec
    rcases hsep ν hν with hpos | hneg
    · exact norm_integral_expPhase_le_of_deriv_pos hg habR hρ
        (by simpa only [deriv_sub_frequency hd] using hpos) hg2
    · exact norm_integral_expPhase_le_of_deriv_neg hg habR hρ
        (by simpa only [deriv_sub_frequency hd] using hneg) hg2
  have hnonSum : ‖∑ ν ∈ T, I ν‖ ≤ (T.card : ℝ) / (Real.pi * ρ) := by
    calc
      _ ≤ ∑ ν ∈ T, ‖I ν‖ := norm_sum_le _ _
      _ ≤ ∑ _ν ∈ T, 1 / (Real.pi * ρ) := Finset.sum_le_sum hnon
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
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
