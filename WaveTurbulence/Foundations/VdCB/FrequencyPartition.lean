/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.OuterFrequencies

/-!
# Exact frequency partitions for sharp Poisson summation

The inner range and the equally cut off outer ranges form one integer
interval. This retains the endpoint conventions in passage to the limit.
-/

public section

namespace WaveTurbulence.VdCB

theorem mem_outerFrequencies_iff (N K : ℕ) (ν : ℤ) :
    ν ∈ outerFrequencies N K ↔
      (-(K : ℤ) ≤ ν ∧ ν < 0) ∨ ((N : ℤ) < ν ∧ ν ≤ (N : ℤ) + K) := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      left
      simp only [Finset.mem_range] at hj
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      right
      simp only [Finset.mem_range] at hj
      omega
  · intro h
    rcases h with h | h
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(-ν - 1).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(ν - N - 1).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega

/-- The shifted cutoff interval is exactly its inner and outer parts. -/
theorem sum_shifted_frequency_interval {A : Type*} [AddCommMonoid A]
    (N K : ℕ) (F : ℤ → A) :
    (∑ ν ∈ Finset.Icc (-(K : ℤ)) ((N : ℤ) + K), F ν) =
      (∑ ν ∈ Finset.Icc 0 (N : ℤ), F ν) + ∑ ν ∈ outerFrequencies N K, F ν := by
  have heq : Finset.Icc (-(K : ℤ)) ((N : ℤ) + K) =
      Finset.Icc 0 (N : ℤ) ∪ outerFrequencies N K := by
    ext ν
    simp only [Finset.mem_Icc, Finset.mem_union, mem_outerFrequencies_iff]
    omega
  have hdis : Disjoint (Finset.Icc 0 (N : ℤ)) (outerFrequencies N K) := by
    apply Finset.disjoint_left.mpr
    intro ν hν hν'
    rw [mem_outerFrequencies_iff] at hν'
    simp only [Finset.mem_Icc] at hν
    omega
  rw [heq, Finset.sum_union hdis]

/-- Adding a fixed number of positive frequencies to a symmetric cutoff. -/
theorem sum_extended_frequency_interval {A : Type*} [AddCommMonoid A]
    (N K : ℕ) (F : ℤ → A) :
    (∑ ν ∈ Finset.Icc (-(K : ℤ)) ((N : ℤ) + K), F ν) =
      (∑ ν ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), F ν) +
        ∑ j ∈ Finset.range N, F ((K : ℤ) + j + 1) := by
  let T := (Finset.range N).image (fun j : ℕ => (K : ℤ) + j + 1)
  have hmem (ν : ℤ) : ν ∈ T ↔ (K : ℤ) < ν ∧ ν ≤ (N : ℤ) + K := by
    constructor
    · intro h
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      simp only [Finset.mem_range] at hj
      omega
    · intro h
      apply Finset.mem_image.mpr
      refine ⟨(ν - K - 1).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
  have heq : Finset.Icc (-(K : ℤ)) ((N : ℤ) + K) = Finset.Icc (-(K : ℤ)) (K : ℤ) ∪ T := by
    ext ν
    simp only [Finset.mem_union, Finset.mem_Icc, hmem]
    omega
  have hdis : Disjoint (Finset.Icc (-(K : ℤ)) (K : ℤ)) T := by
    apply Finset.disjoint_left.mpr
    intro ν hν hν'
    rw [hmem] at hν'
    simp only [Finset.mem_Icc] at hν
    omega
  rw [heq, Finset.sum_union hdis]
  congr 1
  apply Finset.sum_image
  intro i _ j _ h
  dsimp only at h
  omega

end WaveTurbulence.VdCB
