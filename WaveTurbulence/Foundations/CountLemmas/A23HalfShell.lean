/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Lattice shell sums `∑_{0 < |X|_∞ ≤ R} |X|_∞^{-2} ≲ R^{d-2}` (`d ≥ 3`)

Used for the small-vector region of DH23 Lemma A.2(3), `ζ = x − v` (referee §4.3(iv)(A)): near `x = 0` the per-vector
strip bound `N_y(x) ≲ L^{d-1}(1 + ρ/|X|_∞)` is summed against `|X|_∞^{-2}`.

* `supNat X = max_i |X_i|`;
* `card_supNat_eq_le`: at most `2d(2m+1)^{d-1}` integer vectors have `supNat = m`;
* **`sum_inv_supNat_sq_le`**: `∑_{X ∈ s, 0 < supNat X ≤ R} supNat(X)^{-2} ≤ 2d·3^{d-1}·R^{d-2}` for any finite `s`.
-/

public section

open Finset

namespace WaveTurbulence.CountLemmas

/-- The sup norm `max_i |X_i|` of an integer vector, as a natural number. -/
@[expose] def supNat {d : ℕ} (X : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (X i).natAbs

/-- The integer box `{X : |X_i| ≤ m}`. -/
@[expose] def intBox (d m : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m

theorem card_intBox (d m : ℕ) : (intBox d m).card = (2 * m + 1) ^ d := by
  simp only [intBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

theorem mem_intBox_iff {d m : ℕ} (X : Fin d → ℤ) : X ∈ intBox d m ↔ supNat X ≤ m := by
  simp only [intBox, Fintype.mem_piFinset, Finset.mem_Icc, supNat, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]
  constructor
  · intro h i
    have := h i
    omega
  · intro h i
    have := h i
    omega

theorem supNat_eq_zero_iff {d : ℕ} (X : Fin d → ℤ) : supNat X = 0 ↔ X = 0 := by
  constructor
  · intro h
    funext i
    have : (X i).natAbs ≤ supNat X := Finset.le_sup (f := fun i => (X i).natAbs) (Finset.mem_univ i)
    rw [h] at this
    simpa using this
  · rintro rfl
    simp [supNat]

theorem exists_coord_eq_supNat {d : ℕ} (hd : 0 < d) (X : Fin d → ℤ) :
    ∃ i, (X i).natAbs = supNat X := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    fun i => (X i).natAbs
  exact ⟨i, hi.symm⟩

theorem pow_sub_pow_le_mul {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    ∀ n : ℕ, a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * (a - b) * a ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := pow_sub_pow_le_mul hb hab n
    have ha : 0 ≤ a := hb.trans hab
    have hbn : b ^ (n + 1) ≤ a ^ (n + 1) := pow_le_pow_left₀ hb hab _
    have h1 : a ^ (n + 2) - b ^ (n + 2) = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [h1]
    have h2 : a * (a ^ (n + 1) - b ^ (n + 1)) ≤ a * ((n + 1) * (a - b) * a ^ n) :=
      mul_le_mul_of_nonneg_left ih ha
    have h3 : (a - b) * b ^ (n + 1) ≤ (a - b) * a ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hbn (by linarith)
    have h4 : a * ((n + 1) * (a - b) * a ^ n) = (n + 1) * (a - b) * a ^ (n + 1) := by ring
    push_cast
    nlinarith only [h2, h3, h4]

/-- At most `2d(2m+1)^{d-1}` integer vectors have sup norm exactly `m ≥ 1`. -/
theorem card_supNat_eq_le {d : ℕ} (hd : 0 < d) (s : Finset (Fin d → ℤ)) {m : ℕ} (hm : 1 ≤ m) :
    ((s.filter fun X => supNat X = m).card : ℝ) ≤ 2 * d * (2 * m + 1) ^ (d - 1) := by
  classical
  have hsub : s.filter (fun X => supNat X = m) ⊆ intBox d m \ intBox d (m - 1) := by
    intro X hX
    have hX' := (Finset.mem_filter.mp hX).2
    rw [Finset.mem_sdiff, mem_intBox_iff, mem_intBox_iff]
    omega
  have hle : (intBox d (m - 1)) ⊆ intBox d m := fun X hX => by
    rw [mem_intBox_iff] at hX ⊢
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hle, card_intBox, card_intBox] at hc
  have hpow : (2 * (m - 1) + 1) ^ d ≤ (2 * m + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have hcR : ((s.filter fun X => supNat X = m).card : ℝ) ≤
      ((2 * m + 1 : ℕ) : ℝ) ^ d - ((2 * (m - 1) + 1 : ℕ) : ℝ) ^ d := by
    have h0 : ((s.filter fun X => supNat X = m).card : ℝ) ≤
        (((2 * m + 1) ^ d - (2 * (m - 1) + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hc
    rwa [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_pow] at h0
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : ((2 * (m - 1) + 1 : ℕ) : ℝ) = 2 * m - 1 := by
    rw [show 2 * (m - 1) + 1 = 2 * m - 1 by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hm2 : ((2 * m + 1 : ℕ) : ℝ) = 2 * m + 1 := by push_cast; ring
  rw [hm1, hm2] at hcR
  have key := pow_sub_pow_le_mul (a := 2 * (m : ℝ) + 1) (b := 2 * m - 1) (by linarith) (by linarith) n
  refine hcR.trans ?_
  simp only [Nat.add_sub_cancel]
  push_cast
  linarith only [key]

/-- **Shell sum.** `∑_{X ∈ s, 0 < supNat X ≤ R} supNat(X)^{-2} ≤ 2d·3^{d-1}·R^{d-2}` (`d ≥ 3`). -/
theorem sum_inv_supNat_sq_le {d : ℕ} (hd : 3 ≤ d) (s : Finset (Fin d → ℤ)) (R : ℕ) :
    ∑ X ∈ s.filter (fun X => 0 < supNat X ∧ supNat X ≤ R), ((supNat X : ℝ) ^ 2)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (R : ℝ) ^ (d - 2) := by
  classical
  set t := s.filter (fun X => 0 < supNat X ∧ supNat X ≤ R)
  have hmaps : ∀ X ∈ t, supNat X ∈ Finset.Icc 1 R := fun X hX => by
    have := (Finset.mem_filter.mp hX).2
    exact Finset.mem_Icc.mpr ⟨this.1, this.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ m ∈ Finset.Icc 1 R, ∑ X ∈ t.filter (fun X => supNat X = m), ((supNat X : ℝ) ^ 2)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (m : ℝ) ^ (d - 3) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have heq : ∑ X ∈ t.filter (fun X => supNat X = m), ((supNat X : ℝ) ^ 2)⁻¹ =
        ((t.filter fun X => supNat X = m).card : ℝ) * ((m : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_congr rfl (fun X hX => by rw [(Finset.mem_filter.mp hX).2]), Finset.sum_const,
        nsmul_eq_mul]
    rw [heq]
    have hc := card_supNat_eq_le (by omega) t hm1
    have h3 : (2 * (m : ℝ) + 1) ^ (d - 1) ≤ (3 * m) ^ (d - 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have hpos : 0 ≤ ((m : ℝ) ^ 2)⁻¹ := by positivity
    calc ((t.filter fun X => supNat X = m).card : ℝ) * ((m : ℝ) ^ 2)⁻¹
        ≤ 2 * d * (3 * m) ^ (d - 1) * ((m : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (hc.trans (by gcongr)) hpos
      _ = 2 * d * 3 ^ (d - 1) * (m : ℝ) ^ (d - 3) := by
          obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
          have hm0 : (m : ℝ) ≠ 0 := by positivity
          simp only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 3 = n by omega, mul_pow]
          field_simp
          ring
  refine (Finset.sum_le_sum hfib).trans ?_
  have hterm : ∀ m ∈ Finset.Icc 1 R, (2 * d * 3 ^ (d - 1) * (m : ℝ) ^ (d - 3)) ≤
      2 * d * 3 ^ (d - 1) * (R : ℝ) ^ (d - 3) := fun m hm => by
    have := (Finset.mem_Icc.mp hm).2
    gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  simp only [show n + 3 - 3 = n by omega, show n + 3 - 2 = n + 1 by omega, Nat.add_sub_cancel]
  rw [pow_succ]
  ring_nf
  exact le_rfl

end WaveTurbulence.CountLemmas
