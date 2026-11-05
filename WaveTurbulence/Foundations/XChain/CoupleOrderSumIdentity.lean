/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.NextRemainderIdentity
/-! The full complex finite couple sum is the remainder sum plus phi minus the actual Taylor tail. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem couple_order_sum_eq_remainders_add_phi_sub_tail (P : WTParams) (hW : WkeTaylorBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (Ncut : ℕ)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d) :
    (∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k) =
      (∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k) +
        (P.φ (P.δ * t) k : ℂ) - (wkeTaylorTail P p (Ncut / 2 + 1) t k : ℂ) := by
  have hs : (∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k) =
      (∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k) -
        ∑ j ∈ range (Ncut / 2 + 1), (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p j t k : ℂ) := by
    simp only [coupleRemainder, sum_sub_distrib]
    exact congrArg (fun z : ℂ =>
      (∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k) - z)
      (sum_even_half_range (fun j => (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p j t k : ℂ)) Ncut)
  have ht' := congrArg (fun r : ℝ => (r : ℂ))
    (wkeTaylorTail_eq_remainder P hW p hp (Ncut / 2 + 1) t ht k)
  push_cast at ht'
  linear_combination ht' - hs

end WaveTurbulence.Induct
