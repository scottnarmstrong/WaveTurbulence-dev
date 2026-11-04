/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23HalfStar

/-!
# The anti-parallel form `ζ = x − v`: sparse and dense fibers, and the explicit total bound

For `x` away from `0` and `V` (`|X|_∞, |X − V|_∞ ≥ ρ`) both fibers have at most `M = 3(2L+1)^{d-1}` points, and
`N_y N_z ≤ k₀ N_z` (if `N_y < k₀`), `≤ k₀ N_y` (if `N_z < k₀`), `≤ M N_y` otherwise (`sum_big_le`). Together with
`sum_small_le`, **`sum_star_le`** bounds `#S` for `ζ = x − v` explicitly, uniformly in all centres.
-/

public section

open Finset Set

namespace WaveTurbulence.CountLemmas

/-- The explicit dense-fiber bound of `sum_dense_card_ysF_le`. -/
@[expose] noncomputable def denseBound (n : ℕ) (L ρ : ℝ) (k₀ M : ℕ) : ℝ :=
  k₀ * (estcrossConst n * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * max 1 (L ^ (n + 2) / k₀) ^ 2 *
      (1 + Real.log L) ^ 2)) +
    M * (estcrossConst n * (ρ ^ (n + 3) + L ^ (n + 1) * ρ ^ 2 * (1 + Real.log L) ^ 2)) +
    estcrossConst n * L ^ (n + 1) * ρ ^ 2 * (1 + Real.log L) ^ 2 * (L ^ (n + 2)) ^ 2 * (k₀ : ℝ)⁻¹

/-- **Sparse and dense fibers** (`d = n + 3`). -/
theorem sum_big_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L τ : ℝ) (k₀ : ℕ), 2 ≤ L → 0 < τ → 1 / τ ≤ L ^ 2 → 1 ≤ τ * L ^ 2 →
      τ * L ^ 2 ≤ L → 1 ≤ k₀ → 16 * ((3 : ℝ) ^ (n + 1) * max 1 (L ^ (n + 2) / k₀)) ≤ τ * L ^ 2 →
      ∀ (a b c : Mom (n + 3)) (nv : Fin (n + 3) → ℤ) (α β : ℝ),
        ∑ X ∈ (nearFinset L a).filter
            (fun X => ¬ ((supNat X : ℝ) < τ * L ^ 2 ∨ (supNat (X - nv) : ℝ) < τ * L ^ 2)),
          ((ysF L b α τ X).card : ℝ) * (zsF L c (latticePoint L nv) β τ X).card ≤
        2 * k₀ * C * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ)) +
          3 * (2 * L + 1) ^ (n + 2) * denseBound n L (τ * L ^ 2) k₀ ⌊3 * (2 * L + 1) ^ (n + 2)⌋₊ := by
  classical
  obtain ⟨Cy, hCy, hy⟩ := sum_card_ysF_le (d := n + 3) (by omega)
  obtain ⟨Cz, hCz, hz⟩ := sum_card_zsF_le (d := n + 3) (by omega)
  refine ⟨max Cy Cz, lt_max_of_lt_left hCy, ?_⟩
  intro L τ k₀ hL hτ hwin hρ1 hρL hk hscale a b c nv α β
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set ρ := τ * L ^ 2 with hρ
  set A := nearFinset L a
  set B := A.filter (fun X => ¬ ((supNat X : ℝ) < ρ ∨ (supNat (X - nv) : ℝ) < ρ))
  set Ny := fun X => ((ysF L b α τ X).card : ℝ)
  set Nz := fun X => ((zsF L c (latticePoint L nv) β τ X).card : ℝ)
  set M' := 3 * (2 * L + 1) ^ (n + 2)
  set M := ⌊M'⌋₊
  have hM'0 : 0 ≤ M' := by positivity
  -- both fibers are bounded by `M'` on `B`
  have hbig : ∀ X ∈ B, Ny X ≤ M' ∧ Nz X ≤ M' := by
    intro X hX
    have hX' := (Finset.mem_filter.mp hX).2
    push Not at hX'
    have hm1 : 1 ≤ (supNat X : ℝ) := hρ1.trans hX'.1
    have hm2 : 1 ≤ (supNat (X - nv) : ℝ) := hρ1.trans hX'.2
    have hX0 : X ≠ 0 := fun h => by
      rw [h, (supNat_eq_zero_iff _).mpr rfl] at hm1; norm_num at hm1
    have hXv : X ≠ nv := fun h => by
      rw [h, sub_self, (supNat_eq_zero_iff _).mpr rfl] at hm2; norm_num at hm2
    have h1 := card_ysF_le (by omega) hLp hτ.le b α hX0
    have h2 := card_zsF_le (by omega) hLp hτ.le c nv β hXv
    have hq1 : 2 * τ * L ^ 2 / supNat X ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [hX'.1]
    have hq2 : 2 * τ * L ^ 2 / supNat (X - nv) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [hX'.2]
    simp only [show n + 3 - 1 = n + 2 by omega] at h1 h2
    have hP : 0 ≤ (2 * L + 1) ^ (n + 2) := by positivity
    constructor
    · refine h1.trans ?_
      simp only [M']
      nlinarith [mul_le_mul_of_nonneg_left hq1 hP]
    · refine h2.trans ?_
      simp only [M']
      nlinarith [mul_le_mul_of_nonneg_left hq2 hP]
  have hMnat : ∀ X ∈ B, (ysF L b α τ X).card ≤ M := fun X hX =>
    Nat.le_floor (by exact_mod_cast (hbig X hX).1)
  -- pointwise splitting
  have hpt : ∀ X ∈ B, Ny X * Nz X ≤
      (if Ny X < k₀ then k₀ * Nz X else 0) + (if Nz X < k₀ then k₀ * Ny X else 0) +
        (if (k₀ : ℝ) ≤ Ny X then M' * Ny X else 0) := by
    intro X hX
    have hNy : 0 ≤ Ny X := by positivity
    have hNz : 0 ≤ Nz X := by positivity
    have hk0 : (0 : ℝ) ≤ k₀ := by positivity
    have t1 : (0 : ℝ) ≤ (if Ny X < k₀ then k₀ * Nz X else 0) := by split_ifs <;> positivity
    have t2 : (0 : ℝ) ≤ (if Nz X < k₀ then k₀ * Ny X else 0) := by split_ifs <;> positivity
    have t3 : (0 : ℝ) ≤ (if (k₀ : ℝ) ≤ Ny X then M' * Ny X else 0) := by split_ifs <;> positivity
    by_cases h1 : Ny X < k₀
    · rw [ite_eq_left h1]
      nlinarith [mul_le_mul_of_nonneg_right h1.le hNz]
    · by_cases h2 : Nz X < k₀
      · rw [ite_eq_left h2]
        nlinarith [mul_le_mul_of_nonneg_left h2.le hNy]
      · rw [ite_eq_left (le_of_not_gt h1)]
        nlinarith [mul_le_mul_of_nonneg_left (hbig X hX).2 hNy]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have s1 : ∑ X ∈ B, (if Ny X < k₀ then (k₀ : ℝ) * Nz X else 0) ≤ k₀ * (Cz * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ))) := by
    calc _ ≤ ∑ X ∈ B, (k₀ : ℝ) * Nz X := Finset.sum_le_sum fun X _ => by split_ifs <;> first | exact le_rfl | positivity
      _ ≤ ∑ X ∈ A, (k₀ : ℝ) * Nz X := Finset.sum_le_sum_of_subset_of_nonneg hBA fun _ _ _ => by positivity
      _ = k₀ * ∑ X ∈ A, Nz X := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hz L τ hL hτ hwin a c nv β) (by positivity)
  have s2 : ∑ X ∈ B, (if Nz X < k₀ then (k₀ : ℝ) * Ny X else 0) ≤ k₀ * (Cy * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ))) := by
    calc _ ≤ ∑ X ∈ B, (k₀ : ℝ) * Ny X := Finset.sum_le_sum fun X _ => by split_ifs <;> first | exact le_rfl | positivity
      _ ≤ ∑ X ∈ A, (k₀ : ℝ) * Ny X := Finset.sum_le_sum_of_subset_of_nonneg hBA fun _ _ _ => by positivity
      _ = k₀ * ∑ X ∈ A, Ny X := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hy L τ hL hτ hwin a b α) (by positivity)
  have s3 : ∑ X ∈ B, (if (k₀ : ℝ) ≤ Ny X then M' * Ny X else 0) ≤ M' * denseBound n L ρ k₀ M := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hM'0
    have hd := sum_dense_card_ysF_le (n := n) hL1 hτ.le hk hscale hρL a b α B hBA hMnat
    have hfeq : B.filter (fun X => (k₀ : ℝ) ≤ Ny X) = B.filter (fun X => k₀ ≤ (ysF L b α τ X).card) := by
      ext X; simp only [Finset.mem_filter, Ny, Nat.cast_le]
    rw [hfeq]
    exact hd
  have hCm : k₀ * (Cz * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ))) + k₀ * (Cy * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ))) ≤
      2 * k₀ * max Cy Cz * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ)) := by
    have hk0 : (0 : ℝ) ≤ k₀ := by positivity
    have hX : 0 ≤ τ * L ^ (2 * ((n + 3 : ℕ) : ℝ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (le_max_left Cy Cz) (mul_nonneg hk0 hX),
      mul_le_mul_of_nonneg_left (le_max_right Cy Cz) (mul_nonneg hk0 hX)]
  linarith

/-- **The explicit bound for `ζ = x − v`** (`d = n + 3`), uniform in all centres. -/
theorem sum_star_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L τ : ℝ) (k₀ : ℕ), 2 ≤ L → 0 < τ → 1 / τ ≤ L ^ 2 → 1 ≤ τ * L ^ 2 →
      τ * L ^ 2 ≤ L → 1 ≤ k₀ → 16 * ((3 : ℝ) ^ (n + 1) * max 1 (L ^ (n + 2) / k₀)) ≤ τ * L ^ 2 →
      ∀ (a b c : Mom (n + 3)) (nv : Fin (n + 3) → ℤ) (α β : ℝ),
        ((coupledTripleSet L a b c (latticePoint L nv) α β τ 0).ncard : ℝ) ≤
          2 * (2 * L + 1) ^ (2 * (n + 3)) + (2 * L + 1) ^ (2 * (n + 3) - 2) *
            (20 * (2 * ⌈τ * L ^ 2⌉₊ + 1) ^ (n + 3) +
              16 * (n + 3) * 3 ^ (n + 2) * (τ * L ^ 2) ^ 2 * (⌈τ * L ^ 2⌉₊ : ℝ) ^ (n + 1)) +
          (2 * k₀ * C * τ * L ^ (2 * ((n + 3 : ℕ) : ℝ)) +
            3 * (2 * L + 1) ^ (n + 2) * denseBound n L (τ * L ^ 2) k₀ ⌊3 * (2 * L + 1) ^ (n + 2)⌋₊) := by
  obtain ⟨C, hC, hb⟩ := sum_big_le n
  refine ⟨C, hC, ?_⟩
  intro L τ k₀ hL hτ hwin hρ1 hρL hk hscale a b c nv α β
  have hLp : 0 < L := by linarith
  rw [ncard_coupledTripleSet_zero_eq_sum hLp, ← Finset.sum_filter_add_sum_filter_not _
    (fun X => (supNat X : ℝ) < τ * L ^ 2 ∨ (supNat (X - nv) : ℝ) < τ * L ^ 2)]
  exact add_le_add (sum_small_le (by linarith) hτ hρ1 a b c nv α β)
    (hb L τ k₀ hL hτ hwin hρ1 hρL hk hscale a b c nv α β)

end WaveTurbulence.CountLemmas
