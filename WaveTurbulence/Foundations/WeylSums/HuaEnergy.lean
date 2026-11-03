/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality

/-!
# Even moments as quadratic resonance counts

DH21 Lemma A.5: expanding an even power and integrating in the quadratic
frequency leaves exactly equal sums of squares. Linear phases have modulus
one and therefore do not affect the cardinality upper bound.
-/

public section

open Finset
open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- Product coefficient in a power of an exponential polynomial. -/
@[expose] noncomputable def tupleCoeff {ι : Type*} {m : ℕ}
    (c : ι → ℂ) (v : Fin m → ι) : ℂ := ∏ i, c (v i)

/-- Sum frequency in a power of an exponential polynomial. -/
@[expose] def tupleFrequency {ι : Type*} {m : ℕ}
    (freq : ι → ℤ) (v : Fin m → ι) : ℤ := ∑ i, freq (v i)

theorem integerExponentialSum_pow {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (freq : ι → ℤ) (m : ℕ) (t : ℝ) :
    integerExponentialSum c freq t ^ m =
      integerExponentialSum (tupleCoeff c) (tupleFrequency (m := m) freq) t := by
  rw [integerExponentialSum, Fintype.sum_pow]
  unfold integerExponentialSum
  apply sum_congr rfl
  intro v _
  rw [prod_mul_distrib]
  change (∏ i, c (v i)) * (∏ i, e ((freq (v i) : ℝ) * t)) =
    (∏ i, c (v i)) * e ((tupleFrequency freq v : ℝ) * t)
  congr 1
  rw [← e_sum]
  congr 1
  simp only [tupleFrequency, Int.cast_sum, sum_mul]

/-- The `2m`-th moment is bounded by its `m`-tuple resonance count. -/
theorem integral_integerExponentialSum_norm_pow_le {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (freq : ι → ℤ) (m : ℕ) (hc : ∀ i, ‖c i‖ = 1) :
    (∫ t : ℝ in 0..1, ‖integerExponentialSum c freq t‖ ^ (2 * m)) ≤
      resonanceCard (tupleFrequency (m := m) freq) := by
  have hpoint (t : ℝ) : ‖integerExponentialSum c freq t‖ ^ (2 * m) =
      ‖integerExponentialSum (tupleCoeff c) (tupleFrequency (m := m) freq) t‖ ^ 2 := by
    rw [← integerExponentialSum_pow, norm_pow, ← pow_mul, mul_comm m 2]
  simp_rw [hpoint]
  apply integral_integerExponentialSum_norm_sq_le
  intro v
  simp only [tupleCoeff, norm_prod, hc, prod_const_one]

/-- Number of pairs of `m`-tuples in `[h,h+n]` having equal sums of squares. -/
@[expose] noncomputable def quadraticEnergy (h : ℤ) (n m : ℕ) : ℕ :=
  resonanceCard (fun v : Fin m → Fin (n + 1) => ∑ i, (h + (v i : ℕ)) ^ 2)

theorem gaussSum_eq_integerExponentialSum (s r : ℝ) (h : ℤ) (n : ℕ) :
    gaussSum s r h n = integerExponentialSum
      (fun p : Fin (n + 1) => e (r * ((h : ℝ) + (p : ℕ))))
      (fun p : Fin (n + 1) => (h + (p : ℕ) : ℤ) ^ 2) s := by
  unfold integerExponentialSum
  change gaussSum s r h n = ∑ p : Fin (n + 1),
    (fun k : ℕ => e (r * ((h : ℝ) + k)) * e (((h + (k : ℤ)) ^ 2 : ℤ) * s)) p.val
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => e (r * ((h : ℝ) + k)) * e (((h + (k : ℤ)) ^ 2 : ℤ) * s)) (n + 1)]
  unfold gaussSum
  apply sum_congr rfl
  intro p _
  rw [← e_add]
  congr 1
  push_cast
  ring

/-- DH21 Lemma A.5's reduction to counting quadratic resonances, uniform in
both the linear frequency and the interval center. -/
theorem integral_gaussSum_norm_pow_le_energy (r : ℝ) (h : ℤ) (n m : ℕ) :
    (∫ s : ℝ in 0..1, ‖gaussSum s r h n‖ ^ (2 * m)) ≤ quadraticEnergy h n m := by
  simp_rw [gaussSum_eq_integerExponentialSum]
  exact integral_integerExponentialSum_norm_pow_le _ _ m (fun _ => norm_e _)

end WaveTurbulence.WeylSums
