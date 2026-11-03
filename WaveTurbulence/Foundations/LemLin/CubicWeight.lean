/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicMoments
public import WaveTurbulence.Foundations.LemLin.LatticeTail

/-!
# A summable product majorant for the scalar cubic integral

Six frequency moments dominate the product of three quadratic weights.
The resulting scalar lattice majorant keeps the stationary scale gain.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- A polynomial form of the summable frequency bound. -/
theorem scalarCubic_product_weight (f : Fin 3 → ScalarCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (kind : CubicPhase) (s t : ℝ) (ν : Fin 3 → ℝ),
      cubicScale s t * (∏ i, (cubicScale s t + |ν i|) ^ 2) *
        ‖scalarCubicIntegral kind f s t ν‖ ≤ K * cubicScale s t ^ 6 := by
  obtain ⟨C, hC0, hC⟩ := scalarCubic_moments 6 f
  let B := scalarStationaryConstant f
  have hB : 0 ≤ B := scalarStationaryConstant_nonneg f
  refine ⟨32 * (B + C), mul_nonneg (by norm_num) (add_nonneg hB hC0), ?_⟩
  intro kind s t ν
  let Γ := cubicScale s t
  let I := ‖scalarCubicIntegral kind f s t ν‖
  have hΓ : 0 ≤ Γ := (cubicScale_pos s t).le
  have hI : 0 ≤ I := norm_nonneg _
  obtain ⟨j, _, hj⟩ := (univ : Finset (Fin 3)).exists_max_image (fun i => |ν i|)
    ⟨0, mem_univ _⟩
  have hprod : (∏ i, (Γ + |ν i|) ^ 2) ≤ (Γ + |ν j|) ^ 6 := by
    calc
      _ ≤ ∏ _i : Fin 3, (Γ + |ν j|) ^ 2 := prod_le_prod₀
        (fun i _ => sq_nonneg _) (fun i hi => pow_le_pow_left₀
          (add_nonneg hΓ (abs_nonneg _)) (add_le_add le_rfl (hj i hi)) 2)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
  have hp : (Γ + |ν j|) ^ 6 ≤ 32 * (Γ ^ 6 + |ν j| ^ 6) := by
    have ha := add_pow_le hΓ (abs_nonneg (ν j)) 6
    norm_num at ha
    exact ha
  have hb : Γ * I ≤ B := scalarCubic_stationary kind f s t ν
  have hm : Γ * |ν j| ^ 6 * I ≤ C * Γ ^ 6 := hC kind s t ν j
  calc
    _ ≤ Γ * (Γ + |ν j|) ^ 6 * I :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hΓ) hI
    _ = (Γ * I) * (Γ + |ν j|) ^ 6 := by ring
    _ ≤ (Γ * I) * (32 * (Γ ^ 6 + |ν j| ^ 6)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hΓ hI)
    _ = 32 * (Γ ^ 6 * (Γ * I) + Γ * |ν j| ^ 6 * I) := by ring
    _ ≤ 32 * (Γ ^ 6 * B + C * Γ ^ 6) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hb (pow_nonneg hΓ 6)) hm) (by norm_num)
    _ = _ := by ring

/-- Exact normalization of the scalar rational tail weights. -/
theorem scalarTailWeight_product_normalize {Γ : ℝ} (hΓ : 0 < Γ) (ν : Fin 3 → ℝ) :
    (∏ i, scalarTailWeight (ν i / Γ)) * (∏ i, (Γ + |ν i|) ^ 2) = Γ ^ 6 := by
  rw [← prod_mul_distrib]
  have he (i : Fin 3) : scalarTailWeight (ν i / Γ) * (Γ + |ν i|) ^ 2 = Γ ^ 2 := by
    unfold scalarTailWeight
    rw [abs_div, abs_of_pos hΓ]
    have hp : Γ + |ν i| ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hΓ (abs_nonneg _))
    field_simp [hΓ.ne', hp]
  simp only [he, prod_const, card_univ, Fintype.card_fin, ← pow_mul]

/-- A genuinely summable majorant, uniform over both source phases. -/
theorem scalarCubic_tail_majorant (f : Fin 3 → ScalarCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (kind : CubicPhase) (s t : ℝ) (ν : Fin 3 → ℝ),
      ‖scalarCubicIntegral kind f s t ν‖ ≤
        (K / cubicScale s t) * ∏ i, scalarTailWeight (ν i / cubicScale s t) := by
  obtain ⟨K, hK, hbound⟩ := scalarCubic_product_weight f
  refine ⟨K, hK, ?_⟩
  intro kind s t ν
  let Γ := cubicScale s t
  have hΓ : 0 < Γ := cubicScale_pos s t
  have hP : 0 < ∏ i, (Γ + |ν i|) ^ 2 := prod_pos
    (fun i _ => sq_pos_of_pos (add_pos_of_pos_of_nonneg hΓ (abs_nonneg _)))
  have he := scalarTailWeight_product_normalize hΓ ν
  have hb := hbound kind s t ν
  apply (mul_le_mul_iff_of_pos_right hP).mp
  apply (mul_le_mul_iff_of_pos_left hΓ).mp
  calc
    _ ≤ K * Γ ^ 6 := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
    _ = _ := by
      rw [mul_assoc (K / Γ), he]
      field_simp

end WaveTurbulence.LemLin
