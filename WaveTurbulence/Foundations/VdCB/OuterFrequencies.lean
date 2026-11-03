/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.HarmonicTail
public import WaveTurbulence.Foundations.VdCB.SquareKernel

/-!
# Frequencies outside a normalized derivative range

The truncation interval is the integer range `[0,N]`. Outside frequencies
are paired with equal cutoffs at its two ends.
-/

public section

namespace WaveTurbulence.VdCB

/-- Equal cutoffs outside the two endpoints of `[0,N]`. -/
@[expose] def outerFrequencies (N K : ℕ) : Finset ℤ :=
  (Finset.range K).image (fun j : ℕ => -((j : ℤ) + 1)) ∪
    (Finset.range K).image (fun j : ℕ => (N : ℤ) + j + 1)

/-- Sum over the actual outside-frequency set. -/
theorem sum_outerFrequencies {A : Type*} [AddCommMonoid A] (N K : ℕ) (F : ℤ → A) :
    (∑ ν ∈ outerFrequencies N K, F ν) =
      ∑ j ∈ Finset.range K, (F (-((j : ℤ) + 1)) + F ((N : ℤ) + j + 1)) := by
  have hdis : Disjoint ((Finset.range K).image (fun j : ℕ => -((j : ℤ) + 1)))
      ((Finset.range K).image (fun j : ℕ => (N : ℤ) + j + 1)) := by
    apply Finset.disjoint_left.mpr
    intro ν h1 h2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
    omega
  unfold outerFrequencies
  rw [Finset.sum_union hdis, Finset.sum_image, Finset.sum_image, ← Finset.sum_add_distrib]
  · intro i _ j _ h
    dsimp only at h
    omega
  · intro i _ j _ h
    dsimp only at h
    omega

/-- Outside frequencies never meet the normalized derivative range. -/
theorem sub_ne_zero_of_mem_outerFrequencies {N K : ℕ} {r : ℝ}
    (hr : 0 ≤ r) (hrN : r ≤ N) {ν : ℤ} (hν : ν ∈ outerFrequencies N K) : r - ν ≠ 0 := by
  rcases Finset.mem_union.mp hν with hν | hν
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hν
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hν
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith

/-- The endpoint reciprocal kernel has a uniform logarithmic bound. -/
theorem abs_sum_outerFrequencies_inv_le {N K : ℕ} {r : ℝ}
    (hr : 0 ≤ r) (hrN : r ≤ N) :
    |∑ ν ∈ outerFrequencies N K, (r - ν)⁻¹| ≤ 1 + Real.log N := by
  rw [sum_outerFrequencies]
  convert abs_sum_range_shifted_reciprocal_pair_le_log hr hrN K using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  have heq : r - ((N : ℝ) + j + 1) = -((N : ℝ) - r + j + 1) := by ring
  rw [heq, inv_neg]
  congr 1 <;> ring

/-- The square-denominator kernel decays with distance from the endpoints. -/
theorem sum_outerFrequencies_inv_sq_le {N K : ℕ} {r : ℝ}
    (hr : 0 ≤ r) (hrN : r ≤ N) :
    (∑ ν ∈ outerFrequencies N K, ((r - ν) ^ 2)⁻¹) ≤
      2 / (r + 1) + 2 / ((N : ℝ) + 1 - r) := by
  rw [sum_outerFrequencies, Finset.sum_add_distrib]
  have h1 := sum_range_shifted_inv_sq_le_two hr K
  have h2 := sum_range_shifted_inv_sq_le_two (sub_nonneg.mpr hrN) K
  convert add_le_add h1 h2 using 1
  · congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> push_cast
    · ring
    · ring
  · congr 1
    ring

end WaveTurbulence.VdCB
