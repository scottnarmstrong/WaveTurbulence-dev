/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianDamping

/-!
# Log-free quadratic sums with a Gaussian weight

Rational completion, exact Gaussian Poisson summation and the uniform merged
lattice bound give the major-arc estimate with an absolute constant. This
will be transferred to arbitrary smooth compactly supported cutoffs by
Fourier inversion.
-/

public section

open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- An absolute constant for the Gaussian major-arc estimate. -/
@[expose] noncomputable def gaussianMajorArcConstant : ℝ :=
  2 * Real.sqrt 2 * (2 / (1 - Real.exp (-Real.pi * (1 / 5))))

theorem gaussianMajorArcConstant_pos : 0 < gaussianMajorArcConstant := by
  unfold gaussianMajorArcConstant
  have hd : 0 < 1 - Real.exp (-Real.pi * (1 / 5)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    nlinarith only [Real.pi_pos]
  positivity

/-- Gaussian cutoff at scale `L`. -/
@[expose] noncomputable def gaussianWeight (L x : ℝ) : ℝ :=
  Real.exp (-Real.pi * (x / L) ^ 2)

/-- The Gaussian quadratic sum on the integer lattice. -/
@[expose] noncomputable def gaussianQuadraticSum (L s r : ℝ) : ℂ :=
  ∑' n : ℤ, (gaussianWeight L n : ℂ) * e (s * (n : ℝ) ^ 2 + r * n)

/-- The real Gaussian weight and complex damping give the same summand. -/
theorem gaussianTerm_damping_eq (L s r x : ℝ) :
    gaussianTerm (gaussianDamping L s) r x =
      (gaussianWeight L x : ℂ) * e (s * x ^ 2 + r * x) := by
  rw [gaussianWeight, Complex.ofReal_exp, e, ← Complex.exp_add, gaussianTerm, gaussianDamping]
  congr 1
  push_cast
  field_simp
  ring

/-- Absolute convergence of the weighted Gaussian series. -/
theorem summable_gaussianQuadraticTerm {L : ℝ} (hL : 0 < L) (s r : ℝ) :
    Summable (fun n : ℤ => (gaussianWeight L n : ℂ) * e (s * (n : ℝ) ^ 2 + r * n)) := by
  have hh := summable_gaussianTerm (gaussianDamping_re_pos hL s) r
  apply hh.congr
  intro n
  exact gaussianTerm_damping_eq L s r n

/-- **Gaussian major-arc bound**, uniformly in the linear frequency.
The constant is absolute, the scale may be real, and no logarithm is lost. -/
theorem norm_gaussianQuadraticSum_le (L s r : ℝ) (a : ℤ) {q : ℕ}
    (hL : 1 ≤ L) (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ L) (ha : a.natAbs.Coprime q)
    (happrox : |s - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * L)) :
    ‖gaussianQuadraticSum L s r‖ ≤ gaussianMajorArcConstant * L /
      (Real.sqrt q * (1 + L * Real.sqrt |s - (a : ℝ) / q|)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  let : NeZero q := ⟨Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hq)⟩
  have hU : 0 ≤ 2 / (1 - Real.exp (-Real.pi * (1 / 5))) := by
    have hd : 0 < 1 - Real.exp (-Real.pi * (1 / 5)) := by
      apply sub_pos.mpr
      apply Real.exp_lt_one_iff.mpr
      nlinarith only [Real.pi_pos]
    positivity
  have heq : gaussianQuadraticSum L s r = gaussianTheta (gaussianDamping L s) r := by
    apply tsum_congr
    intro n
    exact (gaussianTerm_damping_eq L s r n).symm
  rw [heq, gaussianDamping_split L s ((a : ℝ) / q)]
  have hdecay := gaussianDamping_decay hLpos hqpos hqL happrox
  have hh := norm_gaussianTheta_rational_le (gaussianDamping_re_pos hLpos (s - (a : ℝ) / q))
    a q ha r (by norm_num : (0 : ℝ) < 1 / 5) hdecay
  refine hh.trans ?_
  calc
    _ ≤ (Real.sqrt 2 / Real.sqrt q) *
        (2 * L / (1 + L * Real.sqrt |s - (a : ℝ) / q|)) *
        (2 / (1 - Real.exp (-Real.pi * (1 / 5)))) := by
      apply mul_le_mul_of_nonneg_right _ hU
      exact mul_le_mul_of_nonneg_left (gaussianDamping_prefactor_le hLpos _)
        (by positivity)
    _ = _ := by simp only [gaussianMajorArcConstant, div_mul_eq_div_div]; ring

end WaveTurbulence.WeylSums
