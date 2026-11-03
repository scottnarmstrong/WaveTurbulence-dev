/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.OrderedSimplex
public import WaveTurbulence.Foundations.Analysis.FactorialExponential

/-!
# Explicit volumes of monotone chains

The volume `D^n/n!` used at TARGET L2029–2036. The next application to two
independent monotone chains multiplies the two chain volumes.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The volume of `0 ≤ tₙ ≤ ⋯ ≤ t₁ ≤ D`. -/
theorem volume_orderedSimplex : ∀ (n : ℕ) {D : ℝ}, 0 ≤ D →
    volume (orderedSimplex n D) = ENNReal.ofReal (D ^ n / (Nat.factorial n : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro D _
      simp only [orderedSimplex, volume_pi, Measure.pi_univ, Fin.prod_univ_zero,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one]
  | succ n ih =>
      intro D hD
      rw [volume_orderedSimplex_succ]
      calc
        (∫⁻ t in Icc (0 : ℝ) D, volume (orderedSimplex n t)) =
            ∫⁻ t in Icc (0 : ℝ) D, ENNReal.ofReal (t ^ n / (Nat.factorial n : ℝ)) :=
          setLIntegral_congr_fun measurableSet_Icc fun t ht => ih ht.1
        _ = ENNReal.ofReal (∫ t in Icc (0 : ℝ) D, t ^ n / (Nat.factorial n : ℝ)) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            (((continuous_pow n).div_const (Nat.factorial n : ℝ)).integrableOn_Icc
              (μ := volume)).integrable]
          exact (ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall fun t ht => div_nonneg (pow_nonneg ht.1 n) (Nat.cast_nonneg _))
        _ = _ := by
          congr 1
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD,
            intervalIntegral.integral_div, integral_pow]
          simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, div_div,
            Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- The volume of two monotone chains, with no constraints between chains.
Interleaving the original coordinate labels does not change this value. -/
theorem volume_two_orderedSimplex (m n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    volume ((orderedSimplex m D) ×ˢ (orderedSimplex n D)) =
      ENNReal.ofReal (D ^ (m + n) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) := by
  change (volume.prod volume) _ = _
  rw [Measure.prod_prod, volume_orderedSimplex m hD, volume_orderedSimplex n hD,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [pow_add]
  ring

end WaveTurbulence.Analysis
