/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Extraction
public import WaveTurbulence.Foundations.FC23.ExtractionThresholds
/-! The numerical cut1 scale estimate for the `W`-weighted family, with a free `δ`-exponent `c`
(`c = 6` recovers main's `FC23.cut1_scale_bound`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.FamilyW
open WaveTurbulence.FC23

theorem interpolation_delta_absorption_c {δ ν E c : ℝ} (hδ : 0 < δ) (hE : 0 ≤ E)
    (w N : ℕ) (hsmall : E ^ (2 * w) * δ ^ (c * ν) ≤ 1) :
    E ^ (w * (2 * N + 1)) * δ ^ ((2 + c) * ν * N) ≤ E ^ w * δ ^ (2 * ν * N) := by
  have hpow := pow_le_one₀ (mul_nonneg (pow_nonneg hE _) (Real.rpow_nonneg hδ.le _)) hsmall (n := N)
  have hsplit : E ^ (w * (2 * N + 1)) * δ ^ ((2 + c) * ν * N) =
      E ^ w * (E ^ (2 * w) * δ ^ (c * ν)) ^ N * δ ^ (2 * ν * N) := by
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    have he : w + 2 * w * N = w * (2 * N + 1) := by ring
    rw [he, ← Real.rpow_mul_natCast hδ.le]
    simp only [mul_assoc]
    rw [← Real.rpow_add hδ]
    congr 2
    ring
  rw [hsplit]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (pow_nonneg hE _))
    (Real.rpow_nonneg hδ.le _)).trans_eq (by ring)

theorem extraction_absorption_c (S N w : ℕ) {C U L M δ ν J b c : ℝ}
    (hC : 0 < C) (hU : 0 < U) (hL : 0 < L) (hM : 0 < M) (hδ : 0 < δ) (hJ : 0 ≤ J)
    (hsmall : (4 * Real.exp 1) ^ (2 * w) * δ ^ (c * ν) ≤ 1)
    (hcost : 3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2) ≤ L) :
    (3 : ℝ) ^ w * (4 * Real.exp 1) ^ (w * (2 * N + 1)) *
      (((2 * N + 1 : ℕ) : ℝ) / extractionRadius S N C U M) ^ w *
      (J * L ^ b * δ ^ ((2 + c) * ν * N)) ≤
      J * L ^ (b + (w : ℝ)) * δ ^ (2 * ν * N) * M ^ (-((S * w : ℕ) : ℝ)) := by
  let E : ℝ := 4 * Real.exp 1
  let t : ℝ := ((2 * N + 1 : ℕ) : ℝ) / extractionRadius S N C U M
  have ht : 0 ≤ t := div_nonneg (by positivity) (extractionRadius_pos S N hC hU hM).le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnum : 3 * E * t ≤ L / M ^ S := by
    dsimp only [t, E]
    rw [extractionRadius_identity S N hC hU hM]
    calc
      _ = (3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2)) / M ^ S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcost (pow_nonneg hM.le S)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * E * t) hnum w
  have hδabs := interpolation_delta_absorption_c hδ hE w N hsmall
  calc
    _ = (3 ^ w * t ^ w * (J * L ^ b)) * (E ^ (w * (2 * N + 1)) * δ ^ ((2 + c) * ν * N)) := by
      dsimp [t, E]; ring
    _ ≤ (3 ^ w * t ^ w * (J * L ^ b)) * (E ^ w * δ ^ (2 * ν * N)) :=
      mul_le_mul_of_nonneg_left hδabs (by positivity)
    _ = (3 * E * t) ^ w * (J * L ^ b * δ ^ (2 * ν * N)) := by dsimp only [E]; simp only [mul_pow]; ring
    _ ≤ (L / M ^ S) ^ w * (J * L ^ b * δ ^ (2 * ν * N)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      rw [div_pow, ← pow_mul, Real.rpow_neg hM.le, Real.rpow_natCast,
        Real.rpow_add hL, Real.rpow_natCast]
      ring

end WaveTurbulence.Flower.FamilyW
