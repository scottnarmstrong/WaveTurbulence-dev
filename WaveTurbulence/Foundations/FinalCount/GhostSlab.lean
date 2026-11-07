/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriSib3
/-! G2-GHOST part 1: a slab count that sees the size of the normal vector. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {d : ℕ}

/-- The slab `{u ∈ [-m,m]^d : |n·u| ≤ r}` has at most `(⌊2r/ν⌋+1)(2m+1)^{d-1}` points when some coordinate of
`n` has absolute value at least `ν`. -/
theorem card_slabF_nu (n : Fin d → ℤ) (i0 : Fin d) (ν : ℝ) (hν : 0 < ν) (hn : ν ≤ |(n i0 : ℝ)|) (m : ℕ) (r : ℝ)
    (hr : 0 ≤ r) :
    (slabF d n m r).card ≤ (⌊2 * r / ν⌋₊ + 1) * (2 * m + 1) ^ (d - 1) := by
  classical
  have ht0 : (n i0 : ℝ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hn; linarith
  have hta : 0 < |(n i0 : ℝ)| := abs_pos.2 ht0
  set K : ℕ := ⌊2 * r / ν⌋₊ with hK
  let s : (Fin d → ℤ) → ℤ := fun u => ∑ i ∈ Finset.univ.erase i0, n i * u i
  let lo : ℤ → ℤ := fun s0 => ⌈-(s0 : ℝ) / (n i0 : ℝ) - r / |(n i0 : ℝ)|⌉
  let ψ : (Fin d → ℤ) → ({j // j ≠ i0} → ℤ) × ℤ := fun u => (fun j => u j.1, u i0 - lo (s u))
  have hcard : ((Fintype.piFinset fun _ : {j // j ≠ i0} => Finset.Icc (-(m : ℤ)) m) ×ˢ
      Finset.Icc (0 : ℤ) K).card = (K + 1) * (2 * m + 1) ^ (d - 1) := by
    rw [Finset.card_product, Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
    have h1 : (Fintype.card {j : Fin d // j ≠ i0}) = d - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]; simp
    rw [h1, mul_comm]
    congr 1
    · congr 1; omega
  have hs : ∀ u : Fin d → ℤ, ∑ i, n i * u i = n i0 * u i0 + s u := by
    intro u
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  rw [show (⌊2 * r / ν⌋₊ + 1) * (2 * m + 1) ^ (d - 1) = (K + 1) * (2 * m + 1) ^ (d - 1) from rfl, ← hcard]
  refine Finset.card_le_card_of_injOn ψ ?_ ?_
  · intro u hu
    rw [Finset.mem_coe] at hu
    unfold slabF at hu
    rw [Finset.mem_filter, mem_boxF] at hu
    rw [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]
    have habs : |((n i0 * u i0 + s u : ℤ) : ℝ)| ≤ r := by
      have := hu.2
      have e : (∑ i, (n i : ℝ) * (u i : ℝ)) = ((n i0 * u i0 + s u : ℤ) : ℝ) := by
        rw [← hs u]; push_cast; rfl
      rwa [e] at this
    refine ⟨fun j => ?_, ?_, ?_⟩
    · have := hu.1 j.1
      simp only [Finset.mem_Icc, abs_le] at this ⊢
      exact ⟨by linarith [this.1], this.2⟩
    · -- lower end
      have h2 : |(n i0 : ℝ) * (u i0 : ℝ) + (s u : ℝ)| ≤ r := by push_cast at habs; exact habs
      have h3 : |(n i0 : ℝ)| * |(u i0 : ℝ) + (s u : ℝ) / (n i0 : ℝ)| ≤ r := by
        rw [← abs_mul]
        convert h2 using 2
        field_simp
      have h4 : |(u i0 : ℝ) + (s u : ℝ) / (n i0 : ℝ)| ≤ r / |(n i0 : ℝ)| := by
        rw [le_div_iff₀ hta]; linarith
      have h5 := (abs_le.mp h4).1
      have h1 : lo (s u) ≤ u i0 := by
        apply Int.ceil_le.mpr
        have : -(s u : ℝ) / (n i0 : ℝ) = -((s u : ℝ) / (n i0 : ℝ)) := by ring
        linarith
      show 0 ≤ u i0 - lo (s u)
      omega
    · -- upper end
      have hlo : -(s u : ℝ) / (n i0 : ℝ) - r / |(n i0 : ℝ)| ≤ (lo (s u) : ℝ) := Int.le_ceil _
      have h2 : |(n i0 : ℝ) * (u i0 : ℝ) + (s u : ℝ)| ≤ r := by push_cast at habs; exact habs
      have h3 : |(n i0 : ℝ)| * |(u i0 : ℝ) + (s u : ℝ) / (n i0 : ℝ)| ≤ r := by
        rw [← abs_mul]
        convert h2 using 2
        field_simp
      have h4 : |(u i0 : ℝ) + (s u : ℝ) / (n i0 : ℝ)| ≤ r / |(n i0 : ℝ)| := by
        rw [le_div_iff₀ hta]; linarith
      have h5 := (abs_le.mp h4).2
      have hdiff : (u i0 : ℝ) - lo (s u) ≤ 2 * r / |(n i0 : ℝ)| := by
        have : -(s u : ℝ) / (n i0 : ℝ) = -((s u : ℝ) / (n i0 : ℝ)) := by ring
        have e2 : 2 * r / |(n i0 : ℝ)| = r / |(n i0 : ℝ)| + r / |(n i0 : ℝ)| := by ring
        linarith
      have hdiff2 : (u i0 : ℝ) - lo (s u) ≤ 2 * r / ν := by
        refine hdiff.trans ?_
        exact div_le_div_of_nonneg_left (by linarith) hν hn
      have : ((u i0 - lo (s u) : ℤ) : ℝ) ≤ (K : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (2 * r / ν)
        push_cast; linarith
      have hint : (u i0 - lo (s u)) ≤ (K : ℤ) := by
        have h6 : ((u i0 - lo (s u) : ℤ) : ℝ) ≤ 2 * r / ν := by push_cast; exact hdiff2
        have h7 : (u i0 - lo (s u)) ≤ ⌊2 * r / ν⌋ := Int.le_floor.mpr h6
        have h8 := Int.natCast_floor_eq_floor (a := 2 * r / ν) (by positivity)
        rw [hK, h8]; exact h7
      exact hint
  · intro u hu u' hu' h
    simp only [ψ, Prod.mk.injEq] at h
    obtain ⟨hj, hl⟩ := h
    have hs' : s u = s u' := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have := congrFun hj ⟨i, (Finset.mem_erase.mp hi).1⟩
      simp only at this
      rw [this]
    funext i
    by_cases hi : i = i0
    · subst hi
      rw [hs'] at hl
      linarith
    · exact congrFun hj ⟨i, hi⟩

/-- A lattice vector of Euclidean length at least `ρ` has a coordinate of absolute value at least `ρ L / d`. -/
theorem exists_coord_ge (L : ℝ) (hL : 0 < L) (n : Fin d → ℤ) (ρ : ℝ) (hρ : 0 < ρ) (h : ρ ≤ ‖latticePoint L n‖) :
    ∃ i0, ρ * L / d ≤ |(n i0 : ℝ)| := by
  by_contra hcon
  push Not at hcon
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have : ‖latticePoint L n‖ = 0 := by
        have : latticePoint L n = 0 := Subsingleton.elim _ _
        simp [this]
      linarith
    · exact h0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : ‖latticePoint L n‖ ^ 2 = ∑ i, ((n i : ℝ) / L) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [latticePoint, Real.norm_eq_abs]
    rw [div_pow, div_pow, sq_abs, sq_abs]
  have hlt : ∀ i, ((n i : ℝ) / L) ^ 2 < (ρ / d) ^ 2 := by
    intro i
    have h1 := hcon i
    have h2 : |(n i : ℝ) / L| < ρ / d := by
      rw [abs_div, abs_of_pos hL, div_lt_iff₀ hL]
      calc |(n i : ℝ)| < ρ * L / d := h1
        _ = ρ / d * L := by ring
    have h3 : |(n i : ℝ) / L| ^ 2 < (ρ / d) ^ 2 := pow_lt_pow_left₀ h2 (abs_nonneg _) (by norm_num)
    rwa [sq_abs] at h3
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hsum : ∑ i, ((n i : ℝ) / L) ^ 2 < ∑ _i : Fin d, (ρ / d) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hne fun i _ => hlt i
  have hc : ∑ _i : Fin d, (ρ / d) ^ 2 = ρ ^ 2 / d := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hρd : ρ ^ 2 / d ≤ ρ ^ 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_iff₀ hdR]; nlinarith [sq_nonneg ρ]
  have : ρ ^ 2 ≤ ‖latticePoint L n‖ ^ 2 := pow_le_pow_left₀ hρ.le h 2
  linarith

end WaveTurbulence.FinalCount
