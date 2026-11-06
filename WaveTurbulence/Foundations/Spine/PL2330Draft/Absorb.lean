/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Piece3

/-!
# Constant absorptions with the Leibniz constant `L = (2d)^{30d}` (PL23-30D)

The analogs of `PL234.absorb_*` with `D₀ = 2C⁴L` and `M₀ = K_tr C² L`, for `L ≥ 1`.
-/

@[expose] public section

namespace WaveTurbulence.PL2330

open WaveTurbulence.PL234

/-- The constant `L² = (2d)^{60d}` that absorbs one multiplier and one product factor per block. -/
noncomputable def Lsq (P : WTParams) : ℝ := cLeib P.d (30 * P.d) ^ 2

theorem one_le_Lsq (P : WTParams) (hd : 1 ≤ P.d) : 1 ≤ Lsq P :=
  one_le_pow₀ (one_le_cLeib hd _)

theorem cLeib_le_Lsq (P : WTParams) (hd : 1 ≤ P.d) : cLeib P.d (30 * P.d) ≤ Lsq P := by
  unfold Lsq
  have := one_le_cLeib hd (30 * P.d)
  nlinarith

variable {C δ Λ β L : ℝ}

theorem absorb_tree_err30 (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β) (hL : 1 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    L * (C * (C * δ) ^ n * Λ * β) ≤ (2 * C ^ 4 * L) ^ n * δ ^ n * Λ * β := by
  have h1 := absorb_tree_err hC hδ hΛ hβ hn
  have hL1 : L ≤ L ^ n := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ n := pow_le_pow_right₀ hL hn
  have hC0 : 0 ≤ C := by linarith
  calc L * (C * (C * δ) ^ n * Λ * β) ≤ L ^ n * ((2 * C ^ 4) ^ n * δ ^ n * Λ * β) := by
        apply mul_le_mul hL1 h1 (by positivity) (by positivity)
    _ = (2 * C ^ 4 * L) ^ n * δ ^ n * Λ * β := by rw [mul_pow]; ring

theorem absorb_tree_app30 (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hL : 1 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    L * (δ ^ n * 2 ^ n * (C * C ^ n) * (C * C ^ n * β)) ≤ (2 * C ^ 4 * L) ^ n * δ ^ n * β := by
  have h1 := absorb_tree_app hC hδ hβ hn
  have hL1 : L ≤ L ^ n := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ n := pow_le_pow_right₀ hL hn
  have hC0 : 0 ≤ C := by linarith
  calc L * (δ ^ n * 2 ^ n * (C * C ^ n) * (C * C ^ n * β)) ≤ L ^ n * ((2 * C ^ 4) ^ n * δ ^ n * β) := by
        apply mul_le_mul hL1 h1 (by positivity) (by positivity)
    _ = (2 * C ^ 4 * L) ^ n * δ ^ n * β := by rw [mul_pow]; ring

theorem absorb_base_err30 (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β) (hL : 1 ≤ L) {K : ℝ} (hK : 0 ≤ K)
    (m : ℕ) :
    K * (C * (C * δ) ^ m * Λ * β) ≤ 3 ^ (m + 1) * (K * C ^ 2 * L) * (2 * C ^ 4 * L) ^ m * δ ^ m * Λ * β := by
  have h1 := absorb_base_err hC hδ hΛ hβ hK m
  have hC0 : 0 ≤ C := by linarith
  have hLm : (2 * C ^ 4) ^ m ≤ (2 * C ^ 4 * L) ^ m :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [pow_nonneg hC0 4]) m
  refine h1.trans ?_
  have e1 : 3 ^ (m + 1) * (K * C ^ 2) * (2 * C ^ 4) ^ m * δ ^ m * Λ * β =
      (3 ^ (m + 1) * (K * C ^ 2)) * ((2 * C ^ 4) ^ m) * (δ ^ m * Λ * β) := by ring
  have e2 : 3 ^ (m + 1) * (K * C ^ 2 * L) * (2 * C ^ 4 * L) ^ m * δ ^ m * Λ * β =
      (3 ^ (m + 1) * (K * C ^ 2 * L)) * ((2 * C ^ 4 * L) ^ m) * (δ ^ m * Λ * β) := by ring
  rw [e1, e2]
  have hpos : 0 ≤ δ ^ m * Λ * β := by positivity
  have hK3 : 0 ≤ 3 ^ (m + 1) * (K * C ^ 2) := by positivity
  apply mul_le_mul_of_nonneg_right _ hpos
  calc (3 ^ (m + 1) * (K * C ^ 2)) * (2 * C ^ 4) ^ m ≤ (3 ^ (m + 1) * (K * C ^ 2)) * (2 * C ^ 4 * L) ^ m :=
        mul_le_mul_of_nonneg_left hLm hK3
    _ ≤ (3 ^ (m + 1) * (K * C ^ 2 * L)) * (2 * C ^ 4 * L) ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : 0 ≤ 3 ^ (m + 1) * (K * C ^ 2) := hK3
        nlinarith

theorem absorb_base_app30 (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hL : 1 ≤ L) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    2 ^ m * (L * (δ ^ m * (C * C ^ m * β)) * (K * (C * C ^ m))) ≤
      (K * C ^ 2 * L) * (2 * C ^ 4 * L) ^ m * δ ^ m * β := by
  have hC0 : 0 ≤ C := by linarith
  have h1 : C ^ (2 * m) ≤ C ^ (4 * m) := pow_le_pow_right₀ hC (by omega)
  have hLm : L ^ m ≥ 1 := one_le_pow₀ hL
  calc 2 ^ m * (L * (δ ^ m * (C * C ^ m * β)) * (K * (C * C ^ m)))
      = (K * C ^ 2 * L) * (2 ^ m * C ^ (2 * m)) * δ ^ m * β := by ring
    _ ≤ (K * C ^ 2 * L) * (2 ^ m * C ^ (4 * m) * L ^ m) * δ ^ m * β := by
        have h2 : 2 ^ m * C ^ (2 * m) ≤ 2 ^ m * C ^ (4 * m) * L ^ m := by
          calc 2 ^ m * C ^ (2 * m) ≤ 2 ^ m * C ^ (4 * m) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 ^ m * C ^ (4 * m) * 1 := by ring
            _ ≤ 2 ^ m * C ^ (4 * m) * L ^ m := mul_le_mul_of_nonneg_left hLm (by positivity)
        have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ K * C ^ 2 * L by positivity)
        have h4 := mul_le_mul_of_nonneg_right h3 (show 0 ≤ δ ^ m * β by positivity)
        calc (K * C ^ 2 * L) * (2 ^ m * C ^ (2 * m)) * δ ^ m * β
            = ((K * C ^ 2 * L) * (2 ^ m * C ^ (2 * m))) * (δ ^ m * β) := by ring
          _ ≤ ((K * C ^ 2 * L) * (2 ^ m * C ^ (4 * m) * L ^ m)) * (δ ^ m * β) := h4
          _ = _ := by ring
    _ = (K * C ^ 2 * L) * (2 * C ^ 4 * L) ^ m * δ ^ m * β := by rw [mul_pow, mul_pow, pow_mul]

end WaveTurbulence.PL2330
