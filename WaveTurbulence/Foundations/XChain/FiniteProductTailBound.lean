/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteGeometricTail
/-! Exact-order product tails retain the geometric cutoff decay before lattice summation. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem norm_sum_pi_product_tail_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M J : ℕ) (f : ι → Fin M → ℂ) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i)
    {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2)
    (hf : ∀ i k, ‖f i k‖ ≤ A i * q ^ (2 * k.1)) :
    ‖∑ n : ι → Fin M, if J ≤ ∑ i, (n i).1 then ∏ i, f i (n i) else 0‖ ≤
      (∏ i, A i) * (q ^ J * 2 ^ Fintype.card ι) := by
  classical
  have hterm (n : ι → Fin M) :
      ‖if J ≤ ∑ i, (n i).1 then ∏ i, f i (n i) else 0‖ ≤
        (∏ i, A i) * (if J ≤ ∑ i, (n i).1 then q ^ (2 * ∑ i, (n i).1) else 0) := by
    split_ifs
    · rw [norm_prod]
      have h := prod_le_prod₀ (s := (univ : Finset ι))
        (fun i _ => norm_nonneg (f i (n i))) (fun i _ => hf i (n i))
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, ← mul_sum] at h
      exact h
    · simp
  calc
    _ ≤ ∑ n : ι → Fin M,
        (∏ i, A i) * (if J ≤ ∑ i, (n i).1 then q ^ (2 * ∑ i, (n i).1) else 0) :=
      (norm_sum_le _ _).trans (sum_le_sum (fun n _ => hterm n))
    _ = (∏ i, A i) *
        ∑ n : ι → Fin M, if J ≤ ∑ i, (n i).1 then q ^ (2 * ∑ i, (n i).1) else 0 := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pi_geometric_tail_le M J hq hq')
      (prod_nonneg (fun i _ => hA i))

end WaveTurbulence.Induct
