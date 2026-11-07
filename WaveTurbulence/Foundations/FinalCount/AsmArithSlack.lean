/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmArith
/-! **FINALCOUNT-ASSEMBLY: `final_exponent_le` with strict slack** (`η ≤ 1/40`; ruling 3 of the session-10 brief).  The constant is
`d - γ - 1/4 - 1/40 - 1/20`, i.e. an extra `L^{-(R-1)/20}` pays for the `2^{R-1}` of the tame-set split. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountAsm

/-- (together3), exponent form with strict slack `(R-1)/20`. -/
theorem final_exponent_le_slack (d γ η R ρsb ρfin psb pop pplus Fim Z C₀ : ℝ)
    (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη : η ≤ 1 / 40) (hC₀ : C₀ * η ^ 2 ≤ 1 / 4)
    (hR : 1 ≤ R) (hFim : Fim ≤ R) (hpplus : pplus ≤ 2 * R - 2) (hZ : Z ≤ 4 * (R - 1))
    (hρsb : 0 ≤ ρsb) (_hpsb : 0 ≤ psb) (hpop : 0 ≤ pop) (hpsb2 : psb ≤ 2 * pop) (hρ : ρsb - C₀ * pop ≤ ρfin) :
    (2 * min γ (1 - γ) + 5 * η ^ 2) * (Fim - 1) + min γ (1 - γ) * pplus + η * Z
        - η ^ 5 * ρfin - (3 / 4) * η ^ 3 * pop ≤
      -4 * η ^ 6 * (ρsb + psb) + (R - 1) * (d - γ - 1 / 4 - 1 / 40 - 1 / 20) := by
  have hγ0' : 0 ≤ min γ (1 - γ) := le_min hγ0.le (by linarith)
  have hslack := d_gamma_slack d γ hd hγ0 hγ1
  have hη2 : 0 < η ^ 2 := by positivity
  have hη3 : 0 < η ^ 3 := by positivity
  have hη5 : 0 < η ^ 5 := by positivity
  have hη6 : 0 < η ^ 6 := by positivity
  have h6 : 4 * η ^ 6 ≤ η ^ 5 := by nlinarith [mul_pos hη5 hη0]
  have hη3' : η ^ 3 ≤ 1 / 16 := by
    have : η ^ 3 ≤ (1 / 40) ^ 3 := pow_le_pow_left₀ hη0.le hη 3
    nlinarith
  have hC5 : C₀ * η ^ 5 * pop ≤ (1 / 4) * η ^ 3 * pop := by
    have : C₀ * η ^ 5 = (C₀ * η ^ 2) * η ^ 3 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hC₀ hη3.le
    exact mul_le_mul_of_nonneg_right (by linarith) hpop
  have hpsb' : 8 * η ^ 6 * pop ≥ 4 * η ^ 6 * psb := by nlinarith
  have hpsb'' : 8 * η ^ 6 * pop ≤ (1 / 2) * η ^ 3 * pop := by
    have : 8 * η ^ 6 = (8 * η ^ 3) * η ^ 3 := by ring
    rw [this]; nlinarith [mul_nonneg hη3.le hpop]
  have hρ5 : η ^ 5 * ρfin ≥ η ^ 5 * ρsb - C₀ * η ^ 5 * pop := by nlinarith
  have hρ6 : η ^ 5 * ρsb ≥ 4 * η ^ 6 * ρsb := by nlinarith
  have hR1 : 0 ≤ R - 1 := by linarith
  have hS : 4 * η + 5 * η ^ 2 ≤ 9 / 40 - 1 / 20 := by nlinarith
  have hA : (2 * min γ (1 - γ) + 5 * η ^ 2) * (Fim - 1) ≤ (2 * min γ (1 - γ) + 5 * η ^ 2) * (R - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hB : min γ (1 - γ) * pplus ≤ min γ (1 - γ) * (2 * (R - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hγ0'
  have hZ' : η * Z ≤ η * (4 * (R - 1)) := mul_le_mul_of_nonneg_left hZ hη0.le
  have hT : (4 * min γ (1 - γ) + 4 * η + 5 * η ^ 2) * (R - 1) ≤ (d - γ - 1 / 4 - 1 / 40 - 1 / 20) * (R - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hR1
  nlinarith

end WaveTurbulence.FinalCountAsm
