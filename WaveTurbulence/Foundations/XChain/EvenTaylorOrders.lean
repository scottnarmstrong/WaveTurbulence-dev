/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.WkeTaylorTailBound
/-! The even garden orders recover exactly the finite WKE Taylor sum. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_even_half_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    (∑ N ∈ range (K + 1), if Even N then f (N / 2) else 0) =
      ∑ j ∈ range (K / 2 + 1), f j := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    by_cases h : Even (K + 1)
    · obtain ⟨m, hm⟩ := h
      have hd : (K + 1) / 2 = K / 2 + 1 := by omega
      have heven : Even (K + 1) := ⟨m, hm⟩
      rw [ite_eq_left heven, hd]
      exact (sum_range_succ f (K / 2 + 1)).symm
    · have hm : (K + 1) % 2 ≠ 0 := by
        intro hm
        exact h (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hm))
      have hd : (K + 1) / 2 = K / 2 := by omega
      rw [ite_eq_right h, add_zero, hd]

end WaveTurbulence.Induct
