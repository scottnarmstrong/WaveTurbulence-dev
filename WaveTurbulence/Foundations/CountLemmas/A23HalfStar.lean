/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23HalfDense

/-!
# The anti-parallel form `ζ = x − v`: the explicit bound for `∑_x N_y(x) N_z(x)`

Referee §4.3(iv). With `ρ = τL²` (`1 ≤ ρ ≤ L`) and a threshold `k₀`:

* **small** `x` (`|X|_∞ < ρ` or `|X − V|_∞ < ρ`): by (P), `N_y N_z ≤ (2L+1)^{2d-2}(2 + (2ρ/|X|_∞)² + (2ρ/|X−V|_∞)²)`,
  summed with the shell sum; `x ∈ {0, V}` by the trivial bound;
* **sparse** `x` (`N_y < k₀` or `N_z < k₀`): `≤ k₀ ∑_x N_z + k₀ ∑_x N_y ≤ 2k₀ C τ L^{2d}` (bilinear band);
* **dense** `x` (both `≥ k₀`, not small): `N_y N_z ≤ M N_y`, `M = 3(2L+1)^{d-1}`, and `∑ N_y` by
  `sum_dense_card_ysF_le` (estcross).

`sum_star_le` collects these into an explicit bound, uniform in all centres (`d = n + 3`).
-/

public section

open Finset Set

namespace WaveTurbulence.CountLemmas

theorem card_ysF_le_trivial {d : ℕ} {L : ℝ} (hL : 0 < L) (b : Mom d) (α τ : ℝ) (X : Fin d → ℤ) :
    ((ysF L b α τ X).card : ℝ) ≤ (2 * L + 1) ^ d := by
  classical
  refine le_trans ?_ (card_nearFinset_le hL b)
  exact_mod_cast Finset.card_filter_le _ _

theorem card_zsF_le_trivial {d : ℕ} {L : ℝ} (hL : 0 < L) (c v : Mom d) (β τ : ℝ) (X : Fin d → ℤ) :
    ((zsF L c v β τ X).card : ℝ) ≤ (2 * L + 1) ^ d := by
  classical
  refine le_trans ?_ (card_nearFinset_le hL c)
  exact_mod_cast Finset.card_filter_le _ _

theorem one_add_mul_one_add_le (a b : ℝ) : (1 + a) * (1 + b) ≤ 2 + a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]

/-- `(2ρ/m)² ≤ 4` once `m ≥ ρ`, and `≤ 4ρ² m^{-2}` in general. -/
theorem sq_two_rho_div_le {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) :
    (2 * ρ / m) ^ 2 ≤ (if m < ρ then 4 * ρ ^ 2 * (m ^ 2)⁻¹ else 4) := by
  split_ifs with h
  · rw [div_pow]; field_simp; ring_nf; exact le_rfl
  · rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith

/-- Shell sum over `X ∈ s` translated by `nv`. -/
theorem sum_inv_supNat_sub_sq_le {d : ℕ} (hd : 3 ≤ d) (s : Finset (Fin d → ℤ)) (nv : Fin d → ℤ) (R : ℕ) :
    ∑ X ∈ s.filter (fun X => 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R), ((supNat (X - nv) : ℝ) ^ 2)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (R : ℝ) ^ (d - 2) := by
  classical
  have hinj : Set.InjOn (fun X : Fin d → ℤ => X - nv)
      (s.filter (fun X => 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R) : Set (Fin d → ℤ)) :=
    fun X _ Y _ h => by simpa using h
  rw [show (∑ X ∈ s.filter (fun X => 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R), ((supNat (X - nv) : ℝ) ^ 2)⁻¹) =
      ∑ Y ∈ (s.filter (fun X => 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R)).image (fun X => X - nv),
        ((supNat Y : ℝ) ^ 2)⁻¹ from (Finset.sum_image (f := fun Y => ((supNat Y : ℝ) ^ 2)⁻¹) hinj).symm]
  have himg : (s.filter (fun X => 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R)).image (fun X => X - nv) =
      (s.image fun X => X - nv).filter (fun Y => 0 < supNat Y ∧ supNat Y ≤ R) := by
    ext Y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨X, ⟨hX, h⟩, rfl⟩; exact ⟨⟨X, hX, rfl⟩, h⟩
    · rintro ⟨⟨X, hX, rfl⟩, h⟩; exact ⟨X, ⟨hX, h⟩, rfl⟩
  rw [himg]
  exact sum_inv_supNat_sq_le hd _ R

/-- `#{X ∈ s : supNat (X − nv) ≤ R} ≤ (2R+1)^d`. -/
theorem card_filter_supNat_sub_le {d : ℕ} (s : Finset (Fin d → ℤ)) (nv : Fin d → ℤ) (R : ℕ) :
    ((s.filter fun X => supNat (X - nv) ≤ R).card : ℝ) ≤ (2 * R + 1) ^ d := by
  classical
  have hinj : Set.InjOn (fun X : Fin d → ℤ => X - nv) (s.filter fun X => supNat (X - nv) ≤ R : Set _) :=
    fun X _ Y _ h => by simpa using h
  rw [← Finset.card_image_of_injOn hinj]
  have hsub : (s.filter fun X => supNat (X - nv) ≤ R).image (fun X => X - nv) ⊆ intBox d R := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
    exact (mem_intBox_iff _).mpr (Finset.mem_filter.mp hX).2
  have h := Finset.card_le_card hsub
  rw [card_intBox] at h
  exact_mod_cast h

/-- **The small region** `|X|_∞ < ρ` or `|X − V|_∞ < ρ`. -/
theorem sum_small_le {n : ℕ} {L τ : ℝ} (hL : 1 ≤ L) (hτ : 0 < τ) (hρ1 : 1 ≤ τ * L ^ 2)
    (a b c : Mom (n + 3)) (nv : Fin (n + 3) → ℤ) (α β : ℝ) :
    ∑ X ∈ (nearFinset L a).filter (fun X => (supNat X : ℝ) < τ * L ^ 2 ∨ (supNat (X - nv) : ℝ) < τ * L ^ 2),
        ((ysF L b α τ X).card : ℝ) * (zsF L c (latticePoint L nv) β τ X).card ≤
      2 * (2 * L + 1) ^ (2 * (n + 3)) + (2 * L + 1) ^ (2 * (n + 3) - 2) *
        (20 * (2 * ⌈τ * L ^ 2⌉₊ + 1) ^ (n + 3) +
          16 * (n + 3) * 3 ^ (n + 2) * (τ * L ^ 2) ^ 2 * (⌈τ * L ^ 2⌉₊ : ℝ) ^ (n + 1)) := by
  classical
  have hLp : 0 < L := by linarith
  set ρ := τ * L ^ 2 with hρ
  set R := ⌈ρ⌉₊
  set S := (nearFinset L a).filter (fun X => (supNat X : ℝ) < ρ ∨ (supNat (X - nv) : ℝ) < ρ)
  set P := (2 * L + 1) ^ (2 * (n + 3) - 2)
  have hP : 0 ≤ P := by positivity
  set g₁ := fun X : Fin (n + 3) → ℤ => if (supNat X : ℝ) < ρ then 4 * ρ ^ 2 * ((supNat X : ℝ) ^ 2)⁻¹ else 4
  set g₂ := fun X : Fin (n + 3) → ℤ =>
    if (supNat (X - nv) : ℝ) < ρ then 4 * ρ ^ 2 * ((supNat (X - nv) : ℝ) ^ 2)⁻¹ else 4
  have hpt : ∀ X ∈ S, ((ysF L b α τ X).card : ℝ) * (zsF L c (latticePoint L nv) β τ X).card ≤
      (if X = 0 ∨ X = nv then (2 * L + 1) ^ (2 * (n + 3)) else 0) +
        (if X = 0 ∨ X = nv then 0 else P * (2 + g₁ X + g₂ X)) := by
    intro X _
    by_cases hX : X = 0 ∨ X = nv
    · simp only [hX, ite_true, add_zero]
      have h1 := card_ysF_le_trivial hLp b α τ X
      have h2 := card_zsF_le_trivial hLp c (latticePoint L nv) β τ X
      calc _ ≤ (2 * L + 1) ^ (n + 3) * (2 * L + 1) ^ (n + 3) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by rw [← pow_add]; ring_nf
    · simp only [hX, ite_false, zero_add]
      push Not at hX
      have hm1 : (0 : ℝ) < supNat X := by
        exact_mod_cast Nat.pos_of_ne_zero ((supNat_eq_zero_iff X).not.mpr hX.1)
      have hm2 : (0 : ℝ) < supNat (X - nv) := by
        exact_mod_cast Nat.pos_of_ne_zero ((supNat_eq_zero_iff _).not.mpr (sub_ne_zero.mpr hX.2))
      have h1 := card_ysF_le (by omega) hLp hτ.le b α hX.1
      have h2 := card_zsF_le (by omega) hLp hτ.le c nv β hX.2
      have e1 := sq_two_rho_div_le (lt_of_lt_of_le one_pos hρ1) hm1
      have e2 := sq_two_rho_div_le (lt_of_lt_of_le one_pos hρ1) hm2
      have hprod := one_add_mul_one_add_le (2 * ρ / supNat X) (2 * ρ / supNat (X - nv))
      have hd1 : ((n + 3 - 1 : ℕ)) = n + 2 := by omega
      calc ((ysF L b α τ X).card : ℝ) * (zsF L c (latticePoint L nv) β τ X).card
          ≤ ((2 * L + 1) ^ (n + 3 - 1) * (2 * τ * L ^ 2 / supNat X + 1)) *
            ((2 * L + 1) ^ (n + 3 - 1) * (2 * τ * L ^ 2 / supNat (X - nv) + 1)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = P * ((1 + 2 * ρ / supNat X) * (1 + 2 * ρ / supNat (X - nv))) := by
            simp only [P, hρ]
            rw [show 2 * (n + 3) - 2 = (n + 3 - 1) + (n + 3 - 1) by omega, pow_add]
            ring
        _ ≤ P * (2 + g₁ X + g₂ X) := by
            refine mul_le_mul_of_nonneg_left (hprod.trans ?_) hP
            simp only [g₁, g₂]
            linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  -- the two singular points
  have hsing : ∑ X ∈ S, (if X = 0 ∨ X = nv then (2 * L + 1) ^ (2 * (n + 3)) else (0 : ℝ)) ≤
      2 * (2 * L + 1) ^ (2 * (n + 3)) := by
    rw [← Finset.sum_filter]
    have hsub : S.filter (fun X => X = 0 ∨ X = nv) ⊆ {0, nv} := fun X hX => by
      rcases (Finset.mem_filter.mp hX).2 with h | h <;> simp [h]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((S.filter fun X => X = 0 ∨ X = nv).card : ℝ) ≤ 2 := by
      have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [Finset.card_singleton] at this
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  -- the regular points
  have hreg : ∑ X ∈ S, (if X = 0 ∨ X = nv then (0 : ℝ) else P * (2 + g₁ X + g₂ X)) ≤
      P * (20 * (2 * R + 1) ^ (n + 3) + 16 * (n + 3) * 3 ^ (n + 2) * ρ ^ 2 * (R : ℝ) ^ (n + 1)) := by
    have hceil : ∀ m : ℕ, (m : ℝ) < ρ → m ≤ R := fun m hm => by
      have : (m : ℝ) ≤ R := hm.le.trans (Nat.le_ceil ρ)
      exact_mod_cast this
    have hgen : ∀ m : ℕ, (if (m : ℝ) < ρ then 4 * ρ ^ 2 * ((m : ℝ) ^ 2)⁻¹ else 4) ≤
        4 + (if 0 < m ∧ m ≤ R then 4 * ρ ^ 2 * ((m : ℝ) ^ 2)⁻¹ else 0) := by
      intro m
      by_cases h0 : m = 0
      · subst h0
        simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero,
          mul_zero, lt_self_iff_false, false_and, ite_false, add_zero]
        split_ifs <;> norm_num
      · have hpos : 0 < m := Nat.pos_of_ne_zero h0
        by_cases h1 : (m : ℝ) < ρ
        · rw [ite_eq_left h1, ite_eq_left (⟨hpos, hceil m h1⟩ : 0 < m ∧ m ≤ R)]
          linarith
        · rw [ite_eq_right h1]
          have : (0 : ℝ) ≤ (if 0 < m ∧ m ≤ R then 4 * ρ ^ 2 * ((m : ℝ) ^ 2)⁻¹ else 0) := by
            split_ifs <;> positivity
          linarith
    have hterm : ∀ X ∈ S, (if X = 0 ∨ X = nv then (0 : ℝ) else P * (2 + g₁ X + g₂ X)) ≤
        P * (10 + (if 0 < supNat X ∧ supNat X ≤ R then 4 * ρ ^ 2 * ((supNat X : ℝ) ^ 2)⁻¹ else 0) +
          (if 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R then
            4 * ρ ^ 2 * ((supNat (X - nv) : ℝ) ^ 2)⁻¹ else 0)) := by
      intro X _
      have e1 := hgen (supNat X)
      have e2 := hgen (supNat (X - nv))
      have h0a : (0 : ℝ) ≤ (if 0 < supNat X ∧ supNat X ≤ R then 4 * ρ ^ 2 * ((supNat X : ℝ) ^ 2)⁻¹ else 0) := by
        split_ifs <;> positivity
      have h0b : (0 : ℝ) ≤ (if 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R then
          4 * ρ ^ 2 * ((supNat (X - nv) : ℝ) ^ 2)⁻¹ else 0) := by split_ifs <;> positivity
      by_cases hX : X = 0 ∨ X = nv
      · rw [ite_eq_left hX]
        exact mul_nonneg hP (by linarith)
      · rw [ite_eq_right hX]
        apply mul_le_mul_of_nonneg_left _ hP
        simp only [g₁, g₂]
        linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ hP
    -- the number of small points
    have hcard : (S.card : ℝ) ≤ 2 * (2 * R + 1) ^ (n + 3) := by
      have hsub : S ⊆ (nearFinset L a).filter (fun X => supNat X ≤ R) ∪
          (nearFinset L a).filter (fun X => supNat (X - nv) ≤ R) := by
        intro X hX
        obtain ⟨hA, hX'⟩ := Finset.mem_filter.mp hX
        rcases hX' with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA, by exact_mod_cast (Nat.le_ceil ρ |>.trans' h.le)⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, by exact_mod_cast (Nat.le_ceil ρ |>.trans' h.le)⟩)
      have h1 : (((nearFinset L a).filter (fun X => supNat X ≤ R)).card : ℝ) ≤ (2 * R + 1) ^ (n + 3) := by
        have := card_filter_supNat_sub_le (nearFinset L a) 0 R
        simpa only [sub_zero] using this
      have h2 := card_filter_supNat_sub_le (nearFinset L a) nv R
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hcR : (S.card : ℝ) ≤ (((nearFinset L a).filter (fun X => supNat X ≤ R)).card : ℝ) +
          (((nearFinset L a).filter (fun X => supNat (X - nv) ≤ R)).card : ℝ) := by exact_mod_cast hc
      linarith
    -- the two shell sums
    have hs1 : ∑ X ∈ S, (if 0 < supNat X ∧ supNat X ≤ R then 4 * ρ ^ 2 * ((supNat X : ℝ) ^ 2)⁻¹ else 0) ≤
        4 * ρ ^ 2 * (2 * (n + 3) * 3 ^ (n + 2) * (R : ℝ) ^ (n + 1)) := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsh := sum_inv_supNat_sq_le (d := n + 3) (by omega) S R
      simp only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] at hsh
      push_cast at hsh
      exact hsh
    have hs2 : ∑ X ∈ S, (if 0 < supNat (X - nv) ∧ supNat (X - nv) ≤ R then
        4 * ρ ^ 2 * ((supNat (X - nv) : ℝ) ^ 2)⁻¹ else 0) ≤
        4 * ρ ^ 2 * (2 * (n + 3) * 3 ^ (n + 2) * (R : ℝ) ^ (n + 1)) := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsh := sum_inv_supNat_sub_sq_le (d := n + 3) (by omega) S nv R
      simp only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] at hsh
      push_cast at hsh
      exact hsh
    nlinarith [hcard, hs1, hs2]
  linarith [hsing, hreg]

end WaveTurbulence.CountLemmas
