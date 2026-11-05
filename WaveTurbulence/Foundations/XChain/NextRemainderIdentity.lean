/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.NextRemainderBound
public import WaveTurbulence.Foundations.XChain.EvenTaylorOrders
/-! The next remainder is exactly the real truncated couple sum minus the WKE solution. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem nextRemainder_eq_real_kernel_sum_sub_phi (P : WTParams) (hW : WkeTaylorBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (Ncut : ℕ)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d) :
    nextRemainder P R p Ncut t k =
      (∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k).re -
        P.φ (P.δ * t) k := by
  have hs : (∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k) =
      (∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k) -
        ∑ j ∈ range (Ncut / 2 + 1),
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p j t k : ℂ) := by
    simp only [coupleRemainder, sum_sub_distrib]
    exact congrArg (fun z : ℂ =>
      (∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k) - z)
      (sum_even_half_range (fun j => (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p j t k : ℂ)) Ncut)
  have hr := congrArg Complex.re hs
  simp only [Complex.sub_re, ← Complex.ofReal_sum, Complex.ofReal_re] at hr
  unfold nextRemainder
  rw [hr, wkeTaylorTail_eq_remainder P hW p hp (Ncut / 2 + 1) t ht k]
  ring

end WaveTurbulence.Induct
