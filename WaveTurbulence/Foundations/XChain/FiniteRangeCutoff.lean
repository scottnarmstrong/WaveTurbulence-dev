/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteOrderCutoff
/-! Exact finite range splitting at the ansatz order cutoff. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_range_eq_lower_add_tail (f : ℕ → ℂ) (M K : ℕ) (hMK : M ≤ K) :
    (∑ N ∈ range (K + 1), f N) = (∑ N ∈ range (M + 1), f N) +
      ∑ N ∈ range (K + 1), if M + 1 ≤ N then f N else 0 := by
  have he : (range (K + 1)).filter (fun N => ¬ M + 1 ≤ N) = range (M + 1) := by
    ext N
    simp only [mem_filter, mem_range, not_le]
    omega
  have h := sum_filter_add_sum_filter_not (range (K + 1)) (fun N => M + 1 ≤ N) f
  rw [he, sum_filter] at h
  exact h.symm.trans (add_comm _ _)

end WaveTurbulence.Induct
