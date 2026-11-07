/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Tactic

/-! # Prop 9.6: exponent arithmetic of the interpolation (cases (2), (3)) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8

/-- Common smallness facts for `η ≪_{d,γ} 1`. -/
theorem small_facts {d : ℕ} {γ η : ℝ} (hd : 3 ≤ d) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ (1 - γ) / 1000) :
    η ≤ (1 - γ) / 3000 ∧ η ≤ 1 / 6000 ∧ η ^ 3 * (16 * (d : ℝ) + 28) ≤ (1 - γ) / 30 * η ^ 2 ∧
      η ^ 3 * (16 * (d : ℝ) + 28) ≤ η ^ 2 / 30 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : η ≤ (1 - γ) / 3000 := by nlinarith
  have h2 : η ≤ 1 / 6000 := by linarith
  have e : η ^ 3 * (16 * (d : ℝ) + 28) = η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) := by ring
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [e]; nlinarith [pow_pos hη 2]
  · rw [e]; nlinarith [pow_pos hη 2]

/-- Case (2): `V_β ≥ 3`. -/
theorem case2_arith {d : ℕ} {γ η Va Vb : ℝ} (hd : 3 ≤ d) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ (1 - γ) / 1000) (hVa : 0 ≤ Va) (hVb : 3 ≤ Vb) :
    η ^ 3 * (16 * (d : ℝ) + 28) * (Va + Vb + 1) + (1 - η ^ 3) * ((1 - γ) + η ^ 2 / 8) ≤
      Va * ((γ - 5 * η) / 2) + ((1 - γ + 2 * η ^ 2) * Vb - (2 * (1 - γ) + 5 * η ^ 2) * 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := small_facts hd hγ1 hγ2 hη hsm
  have hc : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
  have hν : η ^ 3 * (16 * (d : ℝ) + 28) ≤ (1 - γ) / 10 := by
    nlinarith [pow_pos hη 2, pow_le_one₀ hη.le (by linarith : η ≤ 1) (n := 2)]
  have hc1 : (1 - γ) / 10 ≤ (γ - 5 * η) / 2 := by nlinarith
  have hc2 : (1 - γ) / 10 ≤ 1 - γ + 2 * η ^ 2 := by nlinarith [pow_pos hη 2]
  have hη3 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  set N := η ^ 3 * (16 * (d : ℝ) + 28) with hN
  have hw : 0 ≤ Vb - 3 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hc1 hVa, mul_le_mul_of_nonneg_left hc2 hw,
    mul_le_mul_of_nonneg_right hν hVa, mul_le_mul_of_nonneg_right hν hw, pow_pos hη 2, pow_pos hη 3]


/-- Case (3): `V_β = 2, V_α ≥ 1` or `V_β = 1, V_α ≥ 3`. -/
theorem case3_arith {d : ℕ} {γ η Va Vb : ℝ} (hd : 3 ≤ d) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ (1 - γ) / 1000) (hcase : (Vb = 2 ∧ 1 ≤ Va) ∨ (Vb = 1 ∧ 3 ≤ Va)) :
    η ^ 3 * (16 * (d : ℝ) + 28) * (Va + Vb + 1) - (1 - η ^ 3) * ((γ - 3 * η) / 2) + (1 - η ^ 3) * (η ^ 2 / 8) ≤
      (Va - 1) * ((γ - 5 * η) / 2) + ((1 - γ + 2 * η ^ 2) * Vb - (2 * (1 - γ) + 5 * η ^ 2) * 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := small_facts hd hγ1 hγ2 hη hsm
  have hν : η ^ 3 * (16 * (d : ℝ) + 28) ≤ (1 - γ) / 10 := by
    nlinarith [pow_pos hη 2, pow_le_one₀ hη.le (by linarith : η ≤ 1) (n := 2)]
  have hc1 : (1 - γ) / 10 ≤ (γ - 5 * η) / 2 := by nlinarith
  have hη3 : η ^ 3 ≤ 1 / 100 := by nlinarith [pow_pos hη 2]
  have hη2 : η ^ 2 ≤ 1 / 100 := by nlinarith
  set N := η ^ 3 * (16 * (d : ℝ) + 28) with hN
  have hN0 : 0 ≤ N := by positivity
  rcases hcase with ⟨hb, ha⟩ | ⟨hb, ha⟩
  · subst hb
    have hu : 0 ≤ Va - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hν hu, mul_le_mul_of_nonneg_left hc1 hu, pow_pos hη 2, pow_pos hη 3]
  · subst hb
    have hu : 0 ≤ Va - 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hν hu, mul_le_mul_of_nonneg_left hc1 hu, pow_pos hη 2, pow_pos hη 3]

end WaveTurbulence.FinalCountG8
