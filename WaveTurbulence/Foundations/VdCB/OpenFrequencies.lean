/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.PoissonMarginNegative

/-!
# Exact open frequency intervals

The finite set represents strict inequalities at both ends, including
when a margin endpoint is itself an integer.
-/

public section

namespace WaveTurbulence.VdCB

/-- Integers strictly between two real endpoints. -/
@[expose] noncomputable def openFrequencies (α β : ℝ) : Finset ℤ := Finset.Ioo ⌊α⌋ ⌈β⌉

theorem mem_openFrequencies {α β : ℝ} {ν : ℤ} :
    ν ∈ openFrequencies α β ↔ α < (ν : ℝ) ∧ (ν : ℝ) < β := by
  simp only [openFrequencies, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]

/-- Normalization and conjugation preserve precisely the source open cutoff. -/
theorem image_marginFrequencies_neg_eq {α β η : ℝ} (m : ℤ) (N : ℕ)
    (hα0 : (m : ℝ) ≤ -β) (hβN : -α ≤ m + N) (hη1 : η ≤ 1) :
    (marginFrequencies (-β - m) (-α - m) η N).image (fun ν => -(m + ν)) =
      openFrequencies (α - η) (β + η) := by
  have hnorm0 : 0 ≤ -β - (m : ℝ) := by linarith only [hα0]
  have hnormN : -α - (m : ℝ) ≤ N := by linarith only [hβN]
  ext k
  constructor
  · intro hk
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hk
    rw [mem_marginFrequencies_iff hnorm0 hnormN hη1] at hν
    apply mem_openFrequencies.mpr
    push_cast
    constructor <;> linarith only [hν.1, hν.2]
  · intro hk
    obtain ⟨h1, h2⟩ := mem_openFrequencies.mp hk
    apply Finset.mem_image.mpr
    refine ⟨-m - k, ?_, ?_⟩
    · apply (mem_marginFrequencies_iff hnorm0 hnormN hη1).mpr
      push_cast
      constructor <;> linarith only [h1, h2]
    · omega

/-- Reindex the actual Poisson integrals into the unnormalized source modes. -/
theorem sum_margin_integrals_neg_eq_open {f : ℝ → ℝ} {a b α β η : ℝ}
    (m : ℤ) (N : ℕ) (hα0 : (m : ℝ) ≤ -β) (hβN : -α ≤ m + N) (hη1 : η ≤ 1) :
    (∑ ν ∈ marginFrequencies (-β - m) (-α - m) η N,
      ∫ x in a..b, WaveTurbulence.NumberTheory.expPhase (f x + ((m : ℝ) + ν) * x)) =
      ∑ k ∈ openFrequencies (α - η) (β + η),
        ∫ x in a..b, WaveTurbulence.NumberTheory.expPhase (f x - (k : ℝ) * x) := by
  rw [← image_marginFrequencies_neg_eq m N hα0 hβN hη1, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ν _
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    congr 1
    push_cast
    ring
  · intro i _ j _ heq
    dsimp only at heq
    omega

end WaveTurbulence.VdCB
