/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ScaleConditions
import Mathlib.Tactic

/-! # Dyadic gap scales, energy windows and the choice of the new bond's vector

Three elementary facts used when a (Y) sequence ending in (Y2) inserts its new bond (DH23 L1954):

* `exists_scale`: every gap norm `r` with `r = 0` or `r ≥ L⁻¹` has a source scale `P` (`GapScale L P r`) in a fixed
  set of `⌊log₂ L⌋ + 3` values. New ladder cells of the post molecule are decomposed by these scales.
* `exists_window`: a window `|Γ − β| ≤ K τ` is covered by `K` windows of radius `τ`. The energy at the two ends of
  the new bond is known up to the sum of the windows of the removed atoms.
* `exists_good_multiplier`: the new bond's vector `k₂ + g (k₁ − k₂)`, `g ∈ {0,…,4}`, keeps a large gap (`≥ λ/11`) to
  the at most four bonds of opposite direction at its two ends ("weakened by a constant multiple", L1954).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4

/-- The dyadic scales `0, 1, 2^{-n}` (`n ≤ log₂ L`). -/
noncomputable def scaleSet (L : ℝ) : Finset ℝ :=
  insert 0 (insert 1 ((range (⌊Real.logb 2 L⌋₊ + 1)).image fun n => ((2 : ℝ) ^ n)⁻¹))

theorem card_scaleSet_le (L : ℝ) : (scaleSet L).card ≤ ⌊Real.logb 2 L⌋₊ + 3 := by
  unfold scaleSet
  refine (card_insert_le _ _).trans ?_
  have := (card_insert_le 1 ((range (⌊Real.logb 2 L⌋₊ + 1)).image fun n => ((2 : ℝ) ^ n)⁻¹))
  have h2 := card_image_le (s := range (⌊Real.logb 2 L⌋₊ + 1)) (f := fun n => ((2 : ℝ) ^ n)⁻¹)
  rw [card_range] at h2
  omega

theorem scaleSet_nonneg {L P : ℝ} (hP : P ∈ scaleSet L) : 0 ≤ P := by
  simp only [scaleSet, mem_insert, mem_image, mem_range] at hP
  rcases hP with rfl | rfl | ⟨n, _, rfl⟩
  · exact le_rfl
  · exact zero_le_one
  · positivity

/-- **Every admissible gap norm has a dyadic source scale.** -/
theorem exists_scale {L r : ℝ} (hL : 1 ≤ L) (hr : r = 0 ∨ L⁻¹ ≤ r) :
    ∃ P ∈ scaleSet L, MoleProp.GapScale L P r := by
  rcases hr with rfl | hr
  · exact ⟨0, by simp [scaleSet], Or.inl ⟨rfl, rfl⟩⟩
  by_cases h1 : 1 / 2 ≤ r
  · exact ⟨1, by simp [scaleSet], Or.inr (Or.inr ⟨rfl, h1⟩)⟩
  push Not at h1
  have hLp : 0 < L := by linarith
  have hrp : 0 < r := lt_of_lt_of_le (inv_pos.mpr hLp) hr
  have hx : 1 ≤ r⁻¹ := by rw [one_le_inv₀ hrp]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hP1 : r ≤ ((2 : ℝ) ^ n)⁻¹ := by
    rw [le_inv_comm₀ hrp (by positivity)]; exact hn1
  have hP2 : ((2 : ℝ) ^ n)⁻¹ < 2 * r := by
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
    have := (inv_lt_iff_one_lt_mul₀ hrp).mp hn2
    rw [pow_succ] at this; nlinarith
  have hrL : r⁻¹ ≤ L := by rw [inv_le_comm₀ hrp hLp]; exact hr
  have hnL : n ≤ ⌊Real.logb 2 L⌋₊ := by
    apply Nat.le_floor
    rw [Real.le_logb_iff_rpow_le (by norm_num) hLp, Real.rpow_natCast]
    exact hn1.trans hrL
  refine ⟨((2 : ℝ) ^ n)⁻¹, ?_, Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)⟩
  · simp only [scaleSet, mem_insert, mem_image, mem_range]
    exact Or.inr (Or.inr ⟨n, by omega, rfl⟩)
  · exact hr.trans hP1
  · linarith
  · linarith
  · linarith

/-- **Window splitting**: `|Γ − β| ≤ K τ` puts `Γ` in one of `K` windows of radius `τ`. -/
theorem exists_window {Γ β τ : ℝ} (hτ : 0 < τ) {K : ℕ} (hK : 1 ≤ K) (h : |Γ - β| ≤ K * τ) :
    ∃ j ∈ range K, |Γ - (β - K * τ + (2 * j + 1) * τ)| ≤ τ := by
  set t := (Γ - β + K * τ) / (2 * τ) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; apply div_nonneg _ (by positivity)
    have := neg_abs_le (Γ - β); linarith
  have htK : t ≤ K := by
    rw [ht, div_le_iff₀ (by positivity)]
    have := le_abs_self (Γ - β); nlinarith
  let j := min ⌊t⌋₊ (K - 1)
  have hjt : (j : ℝ) ≤ t := (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht0)
  have htj : t ≤ j + 1 := by
    by_cases hc : ⌊t⌋₊ ≤ K - 1
    · have : j = ⌊t⌋₊ := min_eq_left hc
      rw [this]; exact (Nat.lt_floor_add_one t).le
    · have : j = K - 1 := min_eq_right (by omega)
      rw [this, Nat.cast_sub hK]; push_cast; linarith
  refine ⟨j, mem_range.mpr (by omega), ?_⟩
  have hΓ : Γ = β - K * τ + 2 * τ * t := by rw [ht]; field_simp; ring
  rw [hΓ, abs_le]
  constructor <;> nlinarith

/-- **Choice of the multiplier `g`** (DH23 L1954, `|g| ≲ 3`): with `r = k₁ − k₂`, some `g ∈ {0,…,4}` puts
`k₂ + g r` at distance at least `λ/11` from the vectors `Zc` (each at distance `≥ λ` from `k₁`) and `Zd` (each at
distance `≥ λ` from `k₂`), when there are at most four of them. -/
theorem exists_good_multiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {lam : ℝ} (hlam : 0 < lam)
    (k₁ k₂ : E) (Z : Finset (E × Bool)) (hZ : Z.card ≤ 4)
    (hfar : ∀ p ∈ Z, lam ≤ ‖(if p.2 then k₁ else k₂) - p.1‖) :
    ∃ g ∈ Icc (0 : ℤ) 4, ∀ p ∈ Z, lam / 11 ≤ ‖k₂ + (g : ℝ) • (k₁ - k₂) - p.1‖ := by
  classical
  set r := k₁ - k₂ with hr
  by_cases hsmall : ‖r‖ ≤ 2 * lam / 11
  · refine ⟨0, by simp, fun p hp => ?_⟩
    have h := hfar p hp
    simp only [Int.cast_zero, zero_smul, add_zero]
    by_cases hb : p.2
    · simp only [hb, ite_true] at h
      have : k₂ - p.1 = (k₁ - p.1) - r := by rw [hr]; abel
      rw [this]
      have := norm_sub_norm_le (k₁ - p.1) r
      linarith
    · simp only [hb, Bool.false_eq_true, ite_false] at h; linarith
  push Not at hsmall
  -- each vector excludes at most one integer
  have hone : ∀ p ∈ Z, ∀ g g' : ℤ, ‖k₂ + (g : ℝ) • r - p.1‖ < lam / 11 → ‖k₂ + (g' : ℝ) • r - p.1‖ < lam / 11 →
      g = g' := by
    intro p _ g g' hg hg'
    by_contra hne
    have hdiff : ((g : ℝ) - g') • r = (k₂ + (g : ℝ) • r - p.1) - (k₂ + (g' : ℝ) • r - p.1) := by
      rw [sub_smul]; abel
    have h1 : ‖((g : ℝ) - g') • r‖ < 2 * lam / 11 := by
      rw [hdiff]; have := norm_sub_le (k₂ + (g : ℝ) • r - p.1) (k₂ + (g' : ℝ) • r - p.1); linarith
    rw [norm_smul] at h1
    have h2 : (1 : ℝ) ≤ ‖(g : ℝ) - g'‖ := by
      rw [Real.norm_eq_abs]
      have : (1 : ℤ) ≤ |g - g'| := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast this
    nlinarith [norm_nonneg r]
  let bad : Finset ℤ := (Icc (0 : ℤ) 4).filter fun g : ℤ => ∃ p ∈ Z, ‖k₂ + (g : ℝ) • r - p.1‖ < lam / 11
  have hbad : bad.card ≤ Z.card := by
    have hsub : bad ⊆ Z.biUnion fun p => (Icc (0 : ℤ) 4).filter fun g : ℤ => ‖k₂ + (g : ℝ) • r - p.1‖ < lam / 11 := by
      intro g hg
      obtain ⟨hgI, p, hp, hgp⟩ := mem_filter.mp hg
      exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hgI, hgp⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ p ∈ Z, ((Icc (0 : ℤ) 4).filter fun g : ℤ => ‖k₂ + (g : ℝ) • r - p.1‖ < lam / 11).card
        ≤ ∑ _p ∈ Z, 1 := by
          refine sum_le_sum fun p hp => card_le_one.mpr fun g hg g' hg' =>
            hone p hp g g' (mem_filter.mp hg).2 (mem_filter.mp hg').2
      _ = Z.card := by simp
  have hcard : bad.card < (Icc (0 : ℤ) 4).card := by
    have : (Icc (0 : ℤ) 4).card = 5 := by decide
    omega
  obtain ⟨g, hgI, hgn⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨g, hgI, fun p hp => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hgn (mem_filter.mpr ⟨hgI, p, hp, hlt⟩)

end WaveTurbulence.MoleProp4
