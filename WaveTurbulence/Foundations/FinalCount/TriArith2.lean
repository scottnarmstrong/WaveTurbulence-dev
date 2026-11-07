/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriArith1
/-! Triangles, part 17 (FINALCOUNT-G2): the `min(slab, box)` factor and the rank factor. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- The normalisation `C₁⁻¹ δ^{1/2}` of one characteristic. -/
noncomputable def qq (δ C₁ : ℝ) : ℝ := C₁⁻¹ * δ ^ (1 / 2 : ℝ)

theorem qq_nonneg {δ C₁ : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C₁) : 0 ≤ qq δ C₁ :=
  mul_nonneg (inv_nonneg.2 hC) (Real.rpow_nonneg hδ _)

theorem qq_le_one {δ C₁ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) : qq δ C₁ ≤ 1 := by
  unfold qq
  have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ0.le hδ (by norm_num)
  have h3 : 0 ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hδ0.le _
  nlinarith [inv_nonneg.2 (zero_le_one.trans hC)]

/-- `δ⁻¹ q² = C₁⁻²`, at most `1`. -/
theorem delta_inv_qq_sq {δ C₁ : ℝ} (hδ0 : 0 < δ) (hC : 1 ≤ C₁) : δ⁻¹ * qq δ C₁ ^ 2 ≤ 1 := by
  unfold qq
  have h : (δ ^ (1 / 2 : ℝ)) ^ 2 = δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]; norm_num
  have : δ⁻¹ * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 2 = (C₁⁻¹) ^ 2 := by
    rw [mul_pow, h]; field_simp
  rw [this]
  have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  have h2 : 0 ≤ C₁⁻¹ := inv_nonneg.2 (zero_le_one.trans hC)
  nlinarith

/-- `δ⁻¹ q ≤ δ^{-1/2}`. -/
theorem delta_inv_qq {δ C₁ : ℝ} (hδ0 : 0 < δ) (hC : 1 ≤ C₁) : δ⁻¹ * qq δ C₁ ≤ δ ^ (-(1 / 2 : ℝ)) := by
  unfold qq
  have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  have h3 : 0 ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hδ0.le _
  have e : δ⁻¹ * δ ^ (1 / 2 : ℝ) = δ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ0]; norm_num
  calc δ⁻¹ * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) = C₁⁻¹ * (δ⁻¹ * δ ^ (1 / 2 : ℝ)) := by ring
    _ ≤ 1 * (δ⁻¹ * δ ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1
        positivity
    _ = _ := by rw [one_mul, e]

theorem rankFactor_nat (d : ℕ) (L γ δ C₁ : ℝ) (hL : 0 < L) (k : ℕ) :
    rankFactor d L γ δ C₁ (k : ℤ) = (L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k := by
  unfold rankFactor qq
  have : L ^ (-((d : ℝ) - γ) * ((k : ℤ) : ℝ)) = (L ^ (-((d : ℝ) - γ))) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; norm_num
  rw [this, zpow_natCast]

theorem two_m_succ_le {L : ℝ} (hL : 1 ≤ L) : ((2 * ⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * L := by
  have := Nat.floor_le (a := 2 * L) (by linarith)
  push_cast
  linarith

/-- **The `min(slab, box)` factor** (DH23 L1793: `δ⁻¹ min(L^{d-2γ+1}, L^d) L^{-(d-γ)}`). -/
theorem F1_bound (d : ℕ) {L γ δ C₁ na : ℝ} (c : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) :
    ((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) * L ^ (-((d : ℝ) - γ)) * qq δ C₁ ≤
      3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ (min γ (1 - γ)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hP1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hPc : 1 ≤ Real.log L ^ c := one_le_pow₀ hP1
  have hq := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hδ1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδ0 |>.2 hδ
  have hLd := rpow_nat_mul_neg d (γ := γ) hL0
  have h5 := two_m_succ_le hL1
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  have hK : 0 ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c := by positivity
  rcases le_total γ (1 - γ) with hγ | hγ
  · -- γ₀ = γ : use the box
    rw [min_eq_left hγ]
    refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by exact_mod_cast min_le_right _ _ : ((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) ≤ (((2 * ⌊2 * L⌋₊ + 1) ^ d : ℕ) : ℝ)) hLn) hq) ?_
    push_cast
    calc ((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d) * L ^ (-((d : ℝ) - γ)) * qq δ C₁ ≤ (5 * L) ^ d * L ^ (-((d : ℝ) - γ)) * qq δ C₁ := by
          gcongr
          exact_mod_cast h5
      _ = 5 ^ d * (L ^ d * L ^ (-((d : ℝ) - γ))) * qq δ C₁ := by rw [mul_pow]; ring
      _ = 5 ^ d * L ^ γ * qq δ C₁ := by rw [hLd]
      _ ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ γ := by
          have hLg : 0 ≤ L ^ γ := Real.rpow_nonneg hL0.le _
          have h5d : 0 ≤ (5 : ℝ) ^ d := by positivity
          have : qq δ C₁ ≤ δ⁻¹ * qq δ C₁ * Real.log L ^ c := by
            calc qq δ C₁ = 1 * qq δ C₁ * 1 := by ring
              _ ≤ δ⁻¹ * qq δ C₁ * Real.log L ^ c := by gcongr
          nlinarith [mul_nonneg h5d hLg, mul_nonneg (mul_nonneg h5d hLg) (sub_nonneg.2 this)]
  · rw [min_eq_right hγ]
    set X : ℝ := L ^ (2 - 2 * γ) with hX
    have hXge : 1 ≤ X := Real.one_le_rpow hL1 (by linarith)
    have hslab : na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 = na * δ⁻¹ * X := by
      have : L ^ (-2 * γ) * L ^ 2 = X := by
        rw [hX, show (2 - 2 * γ) = -2 * γ + (2 : ℕ) by push_cast; ring, Real.rpow_add hL0, Real.rpow_natCast]
      calc na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 = na * δ⁻¹ * (L ^ (-2 * γ) * L ^ 2) := by ring
        _ = _ := by rw [this]
    rw [hslab]
    have hone : 1 ≤ Real.log L ^ c * δ⁻¹ * X := by
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have h2 : 2 * (na * δ⁻¹ * X) + 1 ≤ 3 * (Real.log L ^ c * δ⁻¹ * X) := by
      have : na * δ⁻¹ * X ≤ Real.log L ^ c * δ⁻¹ * X := by gcongr
      linarith
    have hfl : ((⌊2 * (na * δ⁻¹ * X)⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * (Real.log L ^ c * δ⁻¹ * X) := by
      push_cast
      have := Nat.floor_le (a := 2 * (na * δ⁻¹ * X)) (by positivity)
      linarith
    have hm : (((2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) ≤ 5 ^ (d - 1) * L ^ (d - 1) := by
      push_cast
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h5) _
    have hNS : (((⌊2 * (na * δ⁻¹ * X)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) ≤
        3 * (Real.log L ^ c * δ⁻¹ * X) * (5 ^ (d - 1) * L ^ (d - 1)) := by
      push_cast
      push_cast at hm hfl
      exact mul_le_mul hfl hm (by positivity) (by positivity)
    have hmin : (((min ((⌊2 * (na * δ⁻¹ * X)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ)) : ℝ) ≤ 3 * (Real.log L ^ c * δ⁻¹ * X) * (5 ^ (d - 1) * L ^ (d - 1)) :=
      (by exact_mod_cast min_le_left _ _ : (((min ((⌊2 * (na * δ⁻¹ * X)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ)) : ℝ) ≤ _).trans hNS
    have hexp : X * L ^ (d - 1) * L ^ (-((d : ℝ) - γ)) = L ^ (1 - γ) := by
      rw [hX, ← Real.rpow_natCast L (d - 1), ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1
      have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; ring
    calc _ ≤ 3 * (Real.log L ^ c * δ⁻¹ * X) * (5 ^ (d - 1) * L ^ (d - 1)) * L ^ (-((d : ℝ) - γ)) * qq δ C₁ := by
          gcongr
      _ = 3 * 5 ^ (d - 1) * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * (X * L ^ (d - 1) * L ^ (-((d : ℝ) - γ))) := by ring
      _ = 3 * 5 ^ (d - 1) * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ (1 - γ) := by rw [hexp]
      _ ≤ 3 * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ (1 - γ) := by
          have : (5 : ℝ) ^ (d - 1) ≤ 5 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
          have hpos : 0 ≤ (δ⁻¹ * qq δ C₁) * Real.log L ^ c * L ^ (1 - γ) := by positivity
          nlinarith [mul_nonneg hpos (by norm_num : (0:ℝ) ≤ 3)]

end WaveTurbulence.FinalCount
