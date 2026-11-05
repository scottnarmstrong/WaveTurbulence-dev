/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionCovariance
public import WaveTurbulence.Foundations.XChain.NextRemainderIdentity
public import WaveTurbulence.Foundations.XChain.SignedNormSquare
/-! Passing from the actual canonical pair cumulant to the real variance error. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem pair_cumulant_eq_complex_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℂ) (hm : (∫ ω, X ω ∂μ) = 0) :
    cumulant μ (fun j : Fin 2 => fun ω => zpowSign (![1, -1] j) (X ω)) univ =
      ((∫ ω, ‖X ω‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [cumulant_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zpowSign, ite_true, show (-1 : ℤˣ) ≠ 1 from by decide, ite_false, hm, zero_mul, sub_zero]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem variance_error_le_complex_error {v ε : ℝ} {M : ℂ}
    (h : ‖(v : ℂ) - M‖ ≤ ε) : |v - M.re| ≤ ε := by
  have hh := (Complex.abs_re_le_norm ((v : ℂ) - M)).trans h
  simpa only [Complex.sub_re, Complex.ofReal_re] using hh

theorem variance_error_le_remainder_add_error {v φ R E : ℝ}
    (herror : |v - (φ + R)| ≤ E) (hR : |R| ≤ E) : |v - φ| ≤ 2 * E := by
  have he : v - φ = (v - (φ + R)) + R := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end WaveTurbulence.Induct
