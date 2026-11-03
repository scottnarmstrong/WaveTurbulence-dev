/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RationalCounting
public import WaveTurbulence.Foundations.WeylSums.Geometric
public import WaveTurbulence.Foundations.WeylSums.Differencing
public import WaveTurbulence.Foundations.WeylSums.SharpCounting
import WaveTurbulence.Foundations.WeylSums.GaussAlgebra

/-!
# Sharp interval quadratic Gauss sums

The logarithm convention is `1 + log K` so that the bound includes `K = 1`.
This is equivalent up to an absolute constant to `log(2K)`, and to `log K` for `K ≥ 2`.
The sums include both endpoints, as in DH23 equation `huagausssum`.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- The reciprocal cap increases with the cap parameter. -/
theorem cappedInv_mono_cap {S T : ℝ} (hST : S ≤ T) (x : ℝ) :
    cappedInv S x ≤ cappedInv T x := by
  unfold cappedInv
  split
  · exact hST
  · exact min_le_min_right _ hST

/-- The trivial and geometric estimates in one formula, including exact resonances. -/
theorem norm_linearSum_le_cappedInv (t : ℝ) (N : ℕ) :
    ‖linearSum t N‖ ≤ cappedInv N ‖(t : AddCircle (1 : ℝ))‖ := by
  by_cases ht : (t : AddCircle (1 : ℝ)) = 0
  · rw [ht, norm_zero, cappedInv, ite_eq_left rfl]
    exact norm_linearSum_le t N
  · have hp : 0 < ‖(t : AddCircle (1 : ℝ))‖ := norm_pos_iff.mpr ht
    rw [cappedInv, ite_eq_right hp.ne', abs_of_pos hp]
    refine le_min (norm_linearSum_le t N) ?_
    refine (norm_linearSum_le_inv_distance t N ht).trans ?_
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_left zero_le_one hp
    linarith only [hp]

/-- Dominate the positive even differences by the full frequency sum. -/
theorem norm_gaussSum_sq_le_frequency_sum (s r : ℝ) (h : ℤ) (K : ℕ) :
    ‖gaussSum s r h K‖ ^ 2 ≤ (K : ℝ) + 1 +
      2 * ∑ m ∈ range (2 * K + 2),
        cappedInv (2 * K + 2 : ℕ) ‖(s * (m : ℝ) : AddCircle (1 : ℝ))‖ := by
  refine (norm_gaussSum_sq_le_differencing s r h K).trans ?_
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [sum_range_succ]
  simp only [Nat.sub_self, linearSum, range_zero, sum_empty, norm_zero, add_zero]
  refine sum_le_sum_of_injOn (fun d => 2 * (d + 1)) ?_ ?_ ?_ ?_
  · intro i _ j _ hij
    dsimp at hij
    omega
  · intro m hm
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hm
    simp only [mem_range] at hd ⊢
    omega
  · intro d _
    have hf : 2 * s * ((d : ℝ) + 1) = s * ((2 * (d + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    have hlen : ((K - d : ℕ) : ℝ) ≤ ((2 * K + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show K - d ≤ 2 * K + 2 by omega)
    have hh := (norm_linearSum_le_cappedInv (2 * s * ((d : ℝ) + 1)) (K - d)).trans
      (cappedInv_mono_cap hlen _)
    simpa only [linearSum, hf, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh
  · intro m _ _
    exact cappedInv_nonneg (Nat.cast_nonneg _) _

/-- **Quadratic interval Gauss bound**, DH23 L1127–L1129 (the Gauss lemma
used in Lemma 6.6), and DH21 `GaussLem`. The logarithmic convention is
`1 + log K`, equivalent up to an absolute constant to `log(2K)` and to the
large-scale source convention. The estimate includes `K = 1`, both interval
endpoints, and is uniform in the integer shift and real linear frequency. -/
theorem norm_gaussSum_le_of_approx (s r : ℝ) (h a : ℤ) {q K : ℕ}
    (hK : 1 ≤ K) (hq : 1 ≤ q) (hqK : q ≤ K) (ha : a.natAbs.Coprime q)
    (happrox : |s - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * K)) :
    ‖gaussSum s r h K‖ ≤ 128 * (K : ℝ) * (1 + Real.log K) /
      (Real.sqrt q * (1 + K * Real.sqrt |s - (a : ℝ) / q|)) := by
  have hK' : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK'
  have hH : 1 ≤ 1 + Real.log (K : ℝ) :=
    le_add_of_nonneg_right (Real.log_nonneg hK')
  have hβK : |s - (a : ℝ) / q| * q * K ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos hqpos hKpos)).mp happrox
    simpa only [mul_assoc] using hh
  obtain ⟨hc, hr⟩ := frequencyMass_bounds s a hK hq hqK ha happrox
  have hsq := weighted_square_le_of_mass_bounds ‖gaussSum s r h K‖
    (frequencyMass s (2 * K + 2)) K q |s - (a : ℝ) / q| (1 + Real.log K)
    hK' hqpos (Nat.cast_le.mpr hqK) (abs_nonneg _) hβK hH
    (norm_gaussSum_sq_le_frequency_sum s r h K) hc hr
  apply bound_of_weighted_square ‖gaussSum s r h K‖ K (Real.sqrt q)
    (Real.sqrt |s - (a : ℝ) / q|) (1 + Real.log K)
    (norm_nonneg _) hKpos.le (Real.sqrt_pos.mpr hqpos) (Real.sqrt_nonneg _) hH
  simpa only [Real.sq_sqrt (Nat.cast_nonneg q), Real.sq_sqrt (abs_nonneg _)] using hsq


end WaveTurbulence.WeylSums
