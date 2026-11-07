/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Interp96
public import WaveTurbulence.Foundations.FinalCount.Arith96b
public import Mathlib.Tactic

/-! # Prop 9.6, case (5): the final interpolation (DH23 L1887-L1890)

`𝔄 ≤ L^{E₁}` (roughbd) and `𝔄 ≤ (operc)·(log L)^B·L^{-4γ₀/7}` give (finalcount) for `V_α = V_β = 1`.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8

/-- The exponent arithmetic of case (5). -/
theorem case5_arith {d : ℕ} {γ η ρ c : ℝ} (hd : 3 ≤ d) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ (1 - γ) / 1000) (hρ : 0 ≤ ρ) (hc : c ≤ 2) :
    η ^ 3 * (-η ^ 2 * ρ + (16 * (d : ℝ) + 28) * (c + 1)) +
      (1 - η ^ 3) * (-(γ - 3 * η) / 2 - 4 / 7 * (1 - γ) + η ^ 2 / 8) ≤
      -(1 - γ) - 3 * η ^ 2 - η ^ 5 * ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := small_facts hd hγ1 hγ2 hη hsm
  have hη3 : η ^ 3 ≤ 1 / 100 := by nlinarith [pow_pos hη 2]
  have hη2 : η ^ 2 ≤ 1 / 100 := by nlinarith
  have hN : η ^ 3 * (16 * (d : ℝ) + 28) ≤ η ^ 2 / 30 := h4
  have hN0 : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
  have hc1 : c + 1 ≤ 3 := by linarith
  have hq : 0 < 1 - γ := by linarith
  have e1 : η ^ 3 * (16 * (d : ℝ) + 28) * (c + 1) ≤ η ^ 3 * (16 * (d : ℝ) + 28) * 3 := by
    by_cases hc0 : 0 ≤ c + 1
    · exact mul_le_mul_of_nonneg_left hc1 hN0
    · have : η ^ 3 * (16 * (d : ℝ) + 28) * (c + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 (by linarith)
      linarith
  have e2 : η ^ 3 * (-η ^ 2 * ρ) = -(η ^ 5 * ρ) := by ring
  nlinarith [pow_pos hη 2, pow_pos hη 3, mul_pos hη hη]

/-- **Case (5) finish.** -/
theorem case5_finish {d : ℕ} (hd : 3 ≤ d) {γ η δ L K B R0 ρ c rhs : ℝ} {A : ℝ≥0∞}
    (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η) (hsm : (d : ℝ) * η ≤ (1 - γ) / 1000) (hδ : 0 < δ)
    (hL1 : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hR0 : L⁻¹ ≤ R0 ∧ R0 ≤ L ^ (-γ + η)) (hK0 : 0 ≤ K)
    (hconst : 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (K * Real.log L ^ B) ≤ L ^ (η ^ 2 / 8))
    (hρ : 0 ≤ ρ) (hc : c ≤ 2)
    (hA1 : A ≤ ENNReal.ofReal (L ^ (-η ^ 2 * ρ + (16 * (d : ℝ) + 28) * (c + 1))))
    (hA2 : A ≤ ENNReal.ofReal (3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
      Real.log L ^ (8 : ℝ) * (K * Real.log L ^ B) * L ^ (-(4 / 7 * (1 - γ)))))
    (hrhs : L ^ (-(γ + 3 * η) / 2) * R0⁻¹ * L ^ (-(1 - γ) - 3 * η ^ 2 - η ^ 5 * ρ) ≤ rhs) :
    A ≤ ENNReal.ofReal rhs := by
  obtain ⟨s1, s2, s3, s4⟩ := small_facts hd hγ1 hγ2 hη hsm
  have hLp : 0 < L := by linarith
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hR0.1
  have hRinv : L ^ (γ - η) ≤ R0⁻¹ := by
    have : (L ^ (-γ + η))⁻¹ = L ^ (γ - η) := by rw [← Real.rpow_neg hLp.le]; congr 1; ring
    rw [← this]; exact inv_anti₀ hR0pos hR0.2
  set f : ℝ := L ^ (-(γ + 3 * η) / 2) * R0⁻¹ with hf
  have hfge : L ^ ((γ - 5 * η) / 2) ≤ f := by
    calc L ^ ((γ - 5 * η) / 2) = L ^ (-(γ + 3 * η) / 2) * L ^ (γ - η) := by
          rw [← Real.rpow_add hLp]; congr 1; ring
      _ ≤ f := mul_le_mul_of_nonneg_left hRinv (Real.rpow_nonneg hLp.le _)
  have hf1 : 1 ≤ f := le_trans (Real.one_le_rpow hL1 (by linarith)) hfge
  set Kc : ℝ := K * Real.log L ^ B with hKc
  have hlogB : 0 ≤ Real.log L ^ B := Real.rpow_nonneg (by linarith) _
  have hKc0 : 0 ≤ Kc := mul_nonneg hK0 hlogB
  have hlog0 : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
  have t1 : R0⁻¹ * L ^ (-γ) = f * L ^ (-(γ - 3 * η) / 2) := by
    have : L ^ (-γ) = L ^ (-(γ + 3 * η) / 2) * L ^ (-(γ - 3 * η) / 2) := by
      rw [← Real.rpow_add hLp]; congr 1; ring
    rw [hf, this]; ring
  have t2 : L ^ (γ - 1) ≤ f * L ^ (-(γ - 3 * η) / 2) := by
    calc L ^ (γ - 1) ≤ L ^ ((γ - 5 * η) / 2 + -(γ - 3 * η) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L ^ ((γ - 5 * η) / 2) * L ^ (-(γ - 3 * η) / 2) := Real.rpow_add hLp _ _
      _ ≤ f * L ^ (-(γ - 3 * η) / 2) := mul_le_mul_of_nonneg_right hfge (Real.rpow_nonneg hLp.le _)
  set g : ℝ := f * L ^ (-(γ - 3 * η) / 2) with hg
  have hg0 : 0 ≤ g := by positivity
  have hinv : (R0 / 2)⁻¹ = 2 * R0⁻¹ := by rw [inv_div]; field_simp
  have hCnn : 0 ≤ 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) := by positivity
  have hsum : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) ≤
      (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g := by
    have e : (d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) = 2 * (d : ℝ) * δ⁻¹ * (R0⁻¹ * L ^ (-γ)) := by
      rw [hinv]; ring
    rw [e, t1]
    have hdd : 0 ≤ 2 * (d : ℝ) * δ⁻¹ := by positivity
    calc 3 ^ d * (2 * (d : ℝ) * δ⁻¹ * g + L ^ (γ - 1)) ≤ 3 ^ d * (2 * (d : ℝ) * δ⁻¹ * g + g) := by gcongr
      _ = (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g := by ring
  have hpow4 : 0 ≤ L ^ (-(4 / 7 * (1 - γ))) := Real.rpow_nonneg hLp.le _
  have hX : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) * Kc *
      L ^ (-(4 / 7 * (1 - γ))) ≤ f * L ^ (-(γ - 3 * η) / 2 - 4 / 7 * (1 - γ) + η ^ 2 / 8) := by
    calc _ ≤ ((3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1)) * g) * Real.log L ^ (8 : ℝ) * Kc * L ^ (-(4 / 7 * (1 - γ))) := by
          gcongr
      _ = (3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * Kc) * g * L ^ (-(4 / 7 * (1 - γ))) := by ring
      _ ≤ L ^ (η ^ 2 / 8) * g * L ^ (-(4 / 7 * (1 - γ))) := by
          gcongr
      _ = f * L ^ (-(γ - 3 * η) / 2 - 4 / 7 * (1 - γ) + η ^ 2 / 8) := by
          have : L ^ (-(γ - 3 * η) / 2 - 4 / 7 * (1 - γ) + η ^ 2 / 8) =
              L ^ (-(γ - 3 * η) / 2) * L ^ (-(4 / 7 * (1 - γ))) * L ^ (η ^ 2 / 8) := by
            rw [← Real.rpow_add hLp, ← Real.rpow_add hLp] <;> congr 1 <;> ring
          rw [this, hg]; ring
  have hA2' : A ≤ ENNReal.ofReal (f * L ^ (-(γ - 3 * η) / 2 - 4 / 7 * (1 - γ) + η ^ 2 / 8)) :=
    hA2.trans (ENNReal.ofReal_le_ofReal hX)
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have he := case5_arith hd hγ1 hγ2 hη hsm hρ hc
  have hend := endgame hL1 hf1 hA1 hA2' hθ0 hθ1 he
  refine hend.trans (ENNReal.ofReal_le_ofReal ?_)
  exact hrhs

end WaveTurbulence.FinalCountG8
