/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GeometricInputBound
public import WaveTurbulence.Foundations.XChain.FiniteOrderGrouping
/-! Summing exact-order vectors above a total cutoff preserves a geometric tail. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_pi_geometric_tail_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M J : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) :
    (∑ n : ι → Fin M, if J ≤ ∑ i, (n i).1 then q ^ (2 * ∑ i, (n i).1) else 0) ≤
      q ^ J * 2 ^ Fintype.card ι := by
  classical
  have hq1 : q ≤ 1 := by linarith
  have hterm (n : ι → Fin M) :
      (if J ≤ ∑ i, (n i).1 then q ^ (2 * ∑ i, (n i).1) else 0) ≤
        q ^ J * ∏ i, q ^ (n i).1 := by
    split_ifs with hn
    · rw [prod_pow_eq_pow_sum, mul_comm 2, pow_mul, pow_two]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq hq1 hn) (pow_nonneg hq _)
    · exact mul_nonneg (pow_nonneg hq _) (prod_nonneg (fun i _ => pow_nonneg hq _))
  calc
    _ ≤ ∑ n : ι → Fin M, q ^ J * ∏ i, q ^ (n i).1 := sum_le_sum (fun n _ => hterm n)
    _ = q ^ J * ∏ i : ι, ∑ k : Fin M, q ^ k.1 := by rw [← mul_sum, Fintype.prod_sum]
    _ ≤ q ^ J * 2 ^ Fintype.card ι := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
      have h (i : ι) : (∑ k : Fin M, q ^ k.1) ≤ 2 := by
        rw [Fin.sum_univ_eq_sum_range]
        exact sum_geometric_le_two hq hq' M
      simpa only [prod_const, card_univ] using
        prod_le_prod₀ (s := (univ : Finset ι))
          (fun i _ => sum_nonneg (fun k _ => pow_nonneg hq _)) (fun i _ => h i)

end WaveTurbulence.Induct
