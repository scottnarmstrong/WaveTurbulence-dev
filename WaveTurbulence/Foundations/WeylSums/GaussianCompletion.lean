/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianPoisson
public import WaveTurbulence.Foundations.WeylSums.RationalCompletion
public import WaveTurbulence.Foundations.WeylSums.ResidueLattice

/-!
# Rational completion followed by Gaussian Poisson summation

The rational part has square-root Fourier coefficients. The remaining
Gaussian is transformed exactly and its dual lattices are merged before
estimating their tails; this avoids a spurious factor of the denominator.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- Changing the linear frequency is multiplication by an additive phase. -/
theorem gaussianTerm_linear_shift (z : ℂ) (r t x : ℝ) :
    e (t * x) * gaussianTerm z r x = gaussianTerm z (r + t) x := by
  rw [e, gaussianTerm, ← Complex.exp_add, gaussianTerm]
  congr 1
  push_cast
  ring

/-- Splitting off the periodic rational part of a damped quadratic phase. -/
theorem gaussianTerm_split (z : ℂ) (r t x : ℝ) :
    gaussianTerm (z - 2 * Complex.I * t) r x = e (t * x ^ 2) * gaussianTerm z r x := by
  rw [gaussianTerm, e, gaussianTerm, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact rational completion of the absolutely convergent Gaussian sum. -/
theorem gaussianTheta_completion {z : ℂ} (hz : 0 < z.re)
    (a : ℤ) (q : ℕ) [NeZero q] (r : ℝ) :
    gaussianTheta (z - 2 * Complex.I * Complex.ofReal ((a : ℝ) / (q : ℝ))) r =
      ∑ b : ZMod q, quadraticFourierCoeff (a : ZMod q) b *
        gaussianTheta z (r + (b.val : ℝ) / q) := by
  have hpoint (n : ℤ) : gaussianTerm (z - 2 * Complex.I * Complex.ofReal ((a : ℝ) / (q : ℝ))) r n =
      ∑ b : ZMod q, quadraticFourierCoeff (a : ZMod q) b *
        gaussianTerm z (r + (b.val : ℝ) / q) n := by
    rw [gaussianTerm_split, rational_phase_completion, sum_mul]
    apply sum_congr rfl
    intro b _
    rw [mul_assoc, gaussianTerm_linear_shift]
  rw [gaussianTheta]
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun b _ =>
    (summable_gaussianTerm hz (r + (b.val : ℝ) / q)).mul_left (quadraticFourierCoeff (a : ZMod q) b))]
  simp only [tsum_mul_left, gaussianTheta]

/-- The merged dual Gaussian tails are uniformly bounded when their decay
coefficient is bounded below after rescaling by the residue lattice spacing. -/
theorem sum_dual_gaussian_tails_le (q : ℕ) [NeZero q] (r : ℝ) {t₀ t : ℝ}
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t / (q : ℝ) ^ 2) :
    (∑ b : ZMod q, ∑' n : ℤ,
      Real.exp (-Real.pi * ((n : ℝ) - (r + (b.val : ℝ) / q)) ^ 2 * t)) ≤
      2 / (1 - Real.exp (-Real.pi * t₀)) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have htpos : 0 < t := by
    have hh := lt_of_lt_of_le ht₀ ht
    exact (div_pos_iff.mp hh).elim (fun h => h.1) (fun h => False.elim ((not_lt_of_ge (sq_nonneg _)) h.2))
  have hneg (b : ZMod q) :
      (∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) - (r + (b.val : ℝ) / q)) ^ 2 * t)) =
        ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + (b.val : ℝ) / q - (-r)) ^ 2 * t) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro n
    congr 1
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring
  simp_rw [hneg]
  rw [tsum_gaussian_residues_eq q (-r) htpos]
  exact tsum_gaussian_lattice_le _ ht₀ ht

/-- Gaussian major-arc estimate before specializing the damping. All tails
are estimated after merging the rational dual lattices. -/
theorem norm_gaussianTheta_rational_le {z : ℂ} (hz : 0 < z.re)
    (a : ℤ) (q : ℕ) [NeZero q] (ha : a.natAbs.Coprime q) (r : ℝ)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hdecay : t₀ ≤ z⁻¹.re / (q : ℝ) ^ 2) :
    ‖gaussianTheta (z - 2 * Complex.I * Complex.ofReal ((a : ℝ) / (q : ℝ))) r‖ ≤
      (Real.sqrt 2 / Real.sqrt q) * (1 / Real.sqrt ‖z‖) *
        (2 / (1 - Real.exp (-Real.pi * t₀))) := by
  have hu := isUnit_intCast_of_coprime a q ha
  let D : ZMod q → ℝ := fun b => ∑' n : ℤ,
    Real.exp (-Real.pi * ((n : ℝ) - (r + (b.val : ℝ) / q)) ^ 2 * z⁻¹.re)
  have hD (b : ZMod q) : 0 ≤ D b := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [gaussianTheta_completion hz a q r]
  calc
    _ ≤ ∑ b : ZMod q, ‖quadraticFourierCoeff (a : ZMod q) b *
        gaussianTheta z (r + (b.val : ℝ) / q)‖ := norm_sum_le _ _
    _ ≤ ∑ b : ZMod q, (Real.sqrt 2 / Real.sqrt q) * ((1 / Real.sqrt ‖z‖) * D b) := by
      apply sum_le_sum
      intro b _
      rw [norm_mul]
      exact mul_le_mul (norm_quadraticFourierCoeff_le _ b hu)
        (norm_gaussianTheta_le_dual hz _) (norm_nonneg _) (by positivity)
    _ = (Real.sqrt 2 / Real.sqrt q) * (1 / Real.sqrt ‖z‖) * ∑ b : ZMod q, D b := by
      simp only [mul_assoc, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dual_gaussian_tails_le q r ht₀ hdecay) (by positivity)

end WaveTurbulence.WeylSums
