/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Real-variable budgets of the rung bounds (S3b LADDER-DECAY)

With `c = δ L^{2γ}` and `E = L^{2d-2γ}`, the same-layer bounds are `≲ δ⁻¹ E` and the
different-layer bounds `≲ δ⁻¹ E L^{-x}`, under `x < 2γ`, `x ≤ 1` and `δ⁻¹ L^{-2γ} ≤ L^{-x}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay

section
variable {d : ℕ} {γ x δ L : ℝ}

lemma rpow_nat_mul_inv (_hd : 0 < d) (hL : 0 < L) :
    L ^ (2 * d) * (L ^ (2 * γ))⁻¹ = L ^((2 : ℝ) * d - 2 * γ) := by
  rw [Real.rpow_sub hL, ← Real.rpow_natCast, Nat.cast_mul]
  simp [div_eq_mul_inv]

lemma pow_d_le (hd : 3 ≤ d) (hγ : γ < 1) (hx : x ≤ 1) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    L ^ d ≤ δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by
  have hL0 : 0 < L := by linarith
  have h1 : (1 : ℝ) ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ, hδ1⟩
  have h2 : L ^ d = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
  have h3 : L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x) = L ^((2 : ℝ) * d - 2 * γ + -x) :=
    (Real.rpow_add hL0 _ _).symm
  have h4 : L ^ (d : ℝ) ≤ L ^((2 : ℝ) * d - 2 * γ + -x) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h5 : 0 ≤ L ^((2 : ℝ) * d - 2 * γ + -x) := (Real.rpow_pos_of_pos hL0 _).le
  calc L ^ d = L ^ (d : ℝ) := h2
    _ ≤ L ^((2 : ℝ) * d - 2 * γ + -x) := h4
    _ ≤ δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ + -x) := le_mul_of_one_le_left h5 h1
    _ = _ := by rw [← h3]; ring



lemma inv16c_mul (hd : 0 < d) (hL : 0 < L) (hδ : 0 < δ) :
    (16 * (δ * L ^ (2 * γ)))⁻¹ * L ^ (2 * d) = (1 / 16) * δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) := by
  rw [← rpow_nat_mul_inv (γ := γ) hd hL]
  field_simp

lemma inv16c_le (hL : 0 < L) (hδ : 0 < δ) (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x)) :
    (16 * (δ * L ^ (2 * γ)))⁻¹ ≤ (1 / 16) * L ^ (-x) := by
  have : (16 * (δ * L ^ (2 * γ)))⁻¹ = (1 / 16) * (δ⁻¹ * (L ^ (2 * γ))⁻¹) := by
    field_simp
  rw [this]; exact mul_le_mul_of_nonneg_left hB (by norm_num)

lemma four_pow (L : ℝ) (d : ℕ) : (4 * L) ^ (2 * d) = 16 ^ d * L ^ (2 * d) := by
  rw [mul_pow, pow_mul]; norm_num

/-- Fully smooth rung, same layer. -/
lemma budget_F_same (hd : 3 ≤ d) (hL : 1 ≤ L) (hδ : 0 < δ) {C vw : ℝ} (hC : 0 ≤ C)
    (_hvw0 : 0 ≤ vw) (hvw : vw ≤ 1) :
    vw * (16 * (δ * L ^ (2 * γ)))⁻¹ * C * (4 * L) ^ (2 * d) ≤
      (C * 16 ^ d / 16) * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ)) := by
  have hL0 : 0 < L := by linarith
  have h := inv16c_mul (γ := γ) (d := d) (by omega) hL0 hδ
  have ha : 0 ≤ (16 * (δ * L ^ (2 * γ)))⁻¹ := by
    have : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
    positivity
  rw [four_pow]
  calc vw * (16 * (δ * L ^ (2 * γ)))⁻¹ * C * (16 ^ d * L ^ (2 * d))
      ≤ 1 * (16 * (δ * L ^ (2 * γ)))⁻¹ * C * (16 ^ d * L ^ (2 * d)) := by
        gcongr
    _ = (C * 16 ^ d) * ((16 * (δ * L ^ (2 * γ)))⁻¹ * L ^ (2 * d)) := by ring
    _ = _ := by rw [h]; ring

/-- Fully smooth rung, different layers. -/
lemma budget_F_diff (hd : 3 ≤ d) (hL : 1 ≤ L) (hδ : 0 < δ)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x)) {C vw e : ℝ} (hC : 0 ≤ C)
    (_hvw0 : 0 ≤ vw) (hvw : vw ≤ 1) (he : e ≤ -x) (he0 : e ≤ 0) :
    C * (4 * L) ^ (2 * d) * ((16 * (δ * L ^ (2 * γ)))⁻¹ * (16 * (δ * L ^ (2 * γ)))⁻¹ +
        vw * (16 * (δ * L ^ (2 * γ)))⁻¹ * (4 * L) ^ e) ≤
      (C * 16 ^ d / 8) * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
  have hL0 : 0 < L := by linarith
  have h := inv16c_mul (γ := γ) (d := d) (by omega) hL0 hδ
  have h2 := inv16c_le (x := x) (γ := γ) hL0 hδ hB
  have hLx : 0 < L ^ (-x) := Real.rpow_pos_of_pos hL0 _
  have ha : 0 ≤ (16 * (δ * L ^ (2 * γ)))⁻¹ := by
    have : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
    positivity
  have he4 : (4 * L) ^ e ≤ L ^ (-x) := by
    have h5 : (4 * L) ^ e ≤ L ^ e := by
      rw [Real.mul_rpow (by norm_num) hL0.le]
      have : (4 : ℝ) ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) he0
      calc (4 : ℝ) ^ e * L ^ e ≤ 1 * L ^ e := by gcongr
        _ = _ := one_mul _
    exact h5.trans (Real.rpow_le_rpow_of_exponent_le hL he)
  rw [four_pow]
  set a := (16 * (δ * L ^ (2 * γ)))⁻¹ with ha_def
  calc C * (16 ^ d * L ^ (2 * d)) * (a * a + vw * a * (4 * L) ^ e)
      ≤ C * (16 ^ d * L ^ (2 * d)) * (a * ((1 / 16) * L ^ (-x)) + 1 * a * L ^ (-x)) := by
        gcongr
    _ = (C * 16 ^ d) * (a * L ^ (2 * d)) * ((1 / 16) * L ^ (-x) + L ^ (-x)) := by ring
    _ ≤ (C * 16 ^ d) * (a * L ^ (2 * d)) * (2 * L ^ (-x)) := by gcongr; linarith
    _ = _ := by rw [h]; ring

/-- The one-variable-sharp rung (kinds X, Y), same layer. -/
lemma budget_ball_same (hd : 3 ≤ d) (hγ : γ < 1) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {C0 vw ul : ℝ} (hC0 : 0 ≤ C0) (hvw0 : 0 ≤ vw) (hvw : vw ≤ 1) (hul0 : 0 ≤ ul) (hul : ul ≤ 1) :
    vw * (ul * (C0 * (4 * L)) ^ d * 1 + (16 * (δ * L ^ (2 * γ)))⁻¹ *
        ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1)))) ≤
      ((4 * C0) ^ d + (16 * C0) ^ d / 16) * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ)) := by
  have hL0 : 0 < L := by linarith
  have h := inv16c_mul (γ := γ) (d := d) (by omega) hL0 hδ
  have h1 := pow_d_le (x := 0) hd hγ (by norm_num) hL hδ hδ1
  rw [neg_zero, Real.rpow_zero, mul_one] at h1
  have ha : 0 ≤ (16 * (δ * L ^ (2 * γ)))⁻¹ := by
    have : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
    positivity
  have hK : 2 / ((d : ℝ) - 1) ≤ 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_one (by linarith)]; linarith
  have hK0 : 0 ≤ 2 / ((d : ℝ) - 1) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_nonneg (by norm_num) (by linarith)
  have e1 : (C0 * (4 * L)) ^ d = (4 * C0) ^ d * L ^ d := by rw [← mul_pow]; ring_nf
  have e2 : (C0 * (4 * L) ^ 2) ^ d = (16 * C0) ^ d * L ^ (2 * d) := by
    rw [show C0 * (4 * L) ^ 2 = (16 * C0) * L ^ 2 by ring, mul_pow, ← pow_mul]
  have hP : 0 ≤ (4 * C0) ^ d := by positivity
  have hP2 : 0 ≤ (16 * C0) ^ d := by positivity
  rw [e1, e2]
  have hvu : vw * ul ≤ 1 := (mul_le_of_le_one_left hul0 hvw).trans hul
  have hvu0 : 0 ≤ vw * ul := mul_nonneg hvw0 hul0
  have t1 : vw * (ul * ((4 * C0) ^ d * L ^ d) * 1) ≤ (4 * C0) ^ d * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ)) := by
    calc vw * (ul * ((4 * C0) ^ d * L ^ d) * 1) = (vw * ul) * ((4 * C0) ^ d * L ^ d) := by ring
      _ ≤ 1 * ((4 * C0) ^ d * L ^ d) := by gcongr
      _ ≤ (4 * C0) ^ d * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ)) := by rw [one_mul]; gcongr
  have t2 : vw * ((16 * (δ * L ^ (2 * γ)))⁻¹ * ((16 * C0) ^ d * L ^ (2 * d) * (2 / ((d : ℝ) - 1)))) ≤
      (16 * C0) ^ d / 16 * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ)) := by
    calc vw * ((16 * (δ * L ^ (2 * γ)))⁻¹ * ((16 * C0) ^ d * L ^ (2 * d) * (2 / ((d : ℝ) - 1))))
        ≤ 1 * ((16 * (δ * L ^ (2 * γ)))⁻¹ * ((16 * C0) ^ d * L ^ (2 * d) * 1)) := by gcongr
      _ = (16 * C0) ^ d * ((16 * (δ * L ^ (2 * γ)))⁻¹ * L ^ (2 * d)) := by ring
      _ = _ := by rw [h]; ring
  calc _ = vw * (ul * ((4 * C0) ^ d * L ^ d) * 1) + vw * ((16 * (δ * L ^ (2 * γ)))⁻¹ * ((16 * C0) ^ d * L ^ (2 * d) * (2 / ((d : ℝ) - 1)))) := by ring
    _ ≤ _ := by linarith

/-- The one-variable-sharp rung (kinds X, Y), different layers. -/
lemma budget_ball_diff (hd : 3 ≤ d) (hγ : γ < 1) (hx : x ≤ 1) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x))
    {C0 vw ul : ℝ} (hC0 : 0 ≤ C0) (hvw0 : 0 ≤ vw) (hvw : vw ≤ 1) (hul0 : 0 ≤ ul) (hul : ul ≤ 1) :
    vw * (ul * (C0 * (4 * L)) ^ d * 1) + (16 * (δ * L ^ (2 * γ)))⁻¹ *
        ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1))) * (16 * (δ * L ^ (2 * γ)))⁻¹ ≤
      ((4 * C0) ^ d + (16 * C0) ^ d / 256) * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
  have hL0 : 0 < L := by linarith
  have h := inv16c_mul (γ := γ) (d := d) (by omega) hL0 hδ
  have h2 := inv16c_le (x := x) (γ := γ) hL0 hδ hB
  have h1 := pow_d_le (x := x) hd hγ hx hL hδ hδ1
  have hLx : 0 < L ^ (-x) := Real.rpow_pos_of_pos hL0 _
  have ha : 0 ≤ (16 * (δ * L ^ (2 * γ)))⁻¹ := by
    have : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
    positivity
  have hK : 2 / ((d : ℝ) - 1) ≤ 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_one (by linarith)]; linarith
  have hK0 : 0 ≤ 2 / ((d : ℝ) - 1) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact div_nonneg (by norm_num) (by linarith)
  have e1 : (C0 * (4 * L)) ^ d = (4 * C0) ^ d * L ^ d := by rw [← mul_pow]; ring_nf
  have e2 : (C0 * (4 * L) ^ 2) ^ d = (16 * C0) ^ d * L ^ (2 * d) := by
    rw [show C0 * (4 * L) ^ 2 = (16 * C0) * L ^ 2 by ring, mul_pow, ← pow_mul]
  have hP : 0 ≤ (4 * C0) ^ d := by positivity
  have hP2 : 0 ≤ (16 * C0) ^ d := by positivity
  rw [e1, e2]
  set a := (16 * (δ * L ^ (2 * γ)))⁻¹ with ha_def
  have hvu : vw * ul ≤ 1 := (mul_le_of_le_one_left hul0 hvw).trans hul
  have hvu0 : 0 ≤ vw * ul := mul_nonneg hvw0 hul0
  have t1 : vw * (ul * ((4 * C0) ^ d * L ^ d) * 1) ≤ (4 * C0) ^ d * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
    calc vw * (ul * ((4 * C0) ^ d * L ^ d) * 1) = (vw * ul) * ((4 * C0) ^ d * L ^ d) := by ring
      _ ≤ 1 * ((4 * C0) ^ d * L ^ d) := by gcongr
      _ ≤ _ := by rw [one_mul]; gcongr
  have t2 : a * ((16 * C0) ^ d * L ^ (2 * d) * (2 / ((d : ℝ) - 1))) * a ≤
      (16 * C0) ^ d / 256 * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
    calc a * ((16 * C0) ^ d * L ^ (2 * d) * (2 / ((d : ℝ) - 1))) * a
        ≤ a * ((16 * C0) ^ d * L ^ (2 * d) * 1) * a := by gcongr
      _ = (16 * C0) ^ d * (a * L ^ (2 * d)) * a := by ring
      _ ≤ (16 * C0) ^ d * (a * L ^ (2 * d)) * ((1 / 16) * L ^ (-x)) := by gcongr
      _ = _ := by rw [h]; ring
  calc _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

/-- Finite-set (kind Z) budget: `(2R+1)^{2d} + (8L+1)^d ≲ δ⁻¹ E L^{-x}` for `R = L^{1-γ+η}`. -/
lemma budget_Z {η : ℝ} (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ : γ < 1) (hη : 0 < η)
    (hη1 : 10 * (d : ℝ) * η ≤ γ) (hx : x < 2 * γ) (hx1 : x ≤ 1) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 * L ^ (1 - γ + η) + 1) ^ (2 * d) + (8 * L + 1) ^ d ≤
      (2 * 9 ^ d) * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
  have hL0 : 0 < L := by linarith
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := pow_d_le (x := x) hd hγ hx1 hL hδ hδ1
  have hδ' : (1 : ℝ) ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ, hδ1⟩
  have hR1 : 1 ≤ L ^ (1 - γ + η) := Real.one_le_rpow hL (by nlinarith)
  have hA : (2 * L ^ (1 - γ + η) + 1) ^ (2 * d) ≤ 9 ^ d * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
    have e1 : (2 * L ^ (1 - γ + η) + 1) ^ (2 * d) ≤ (3 * L ^ (1 - γ + η)) ^ (2 * d) := by
      gcongr; linarith
    have e2 : (3 * L ^ (1 - γ + η)) ^ (2 * d) = 9 ^ d * L ^ ((1 - γ + η) * ((2 * d : ℕ) : ℝ)) := by
      rw [mul_pow, Real.rpow_mul_natCast hL0.le, pow_mul]; norm_num
    have e3 : L ^ ((1 - γ + η) * ((2 * d : ℕ) : ℝ)) ≤ L ^((2 : ℝ) * d - 2 * γ + -x) := by
      apply Real.rpow_le_rpow_of_exponent_le hL
      push_cast
      nlinarith
    have e4 : L ^((2 : ℝ) * d - 2 * γ + -x) = L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x) := Real.rpow_add hL0 _ _
    have e5 : 0 ≤ L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by positivity
    calc (2 * L ^ (1 - γ + η) + 1) ^ (2 * d) ≤ _ := e1
      _ = _ := e2
      _ ≤ 9 ^ d * (L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by rw [← e4]; gcongr
      _ ≤ 9 ^ d * (δ⁻¹ * (L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x))) := by
        have := le_mul_of_one_le_left e5 hδ'
        exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hB : (8 * L + 1) ^ d ≤ 9 ^ d * (δ⁻¹ * L ^((2 : ℝ) * d - 2 * γ) * L ^ (-x)) := by
    calc (8 * L + 1) ^ d ≤ (9 * L) ^ d := by gcongr; linarith
      _ = 9 ^ d * L ^ d := mul_pow _ _ _
      _ ≤ _ := by gcongr
  linarith

end
end WaveTurbulence.LadderDecay
