/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm2d
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 3: the terminal exponent inequality (real arithmetic).**
With `a = 2γ₀+5η²`, `b = γ₀+2η²`, `q = #clusters`, `m = |T|`, `e = Σ e_K`, `J = Σ j_K`, `ib = Σ ib_K`, `iso` the dropped atoms:
`F₅ = F - J + e + ib - m - iso`, `R₅ + 2m + iso ≤ R + e + ib`, `Fim₅ ≤ R₅`, `ρ ≤ ρ₅ + m + iso`, `iso ≤ e`, `β₅ ≤ Vβ`,
`Z₅ ≤ e + 4(R-1) + 3q`, `C₀ ≥ 1`, `ρ ≥ 1` give
`-(η³+3η)q + a(m-J) - ηe - C₀η⁵(m+e) + bβ₅ - a(F₅-Fim₅) - η⁵ρ₅ + ηZ₅ ≤ aR + 4η(R-1) - (η⁵-4η⁶)/2 - 4η⁶ρ - aF + bVβ`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountAsm

theorem term_arith (a b η C₀ q m e J ib iso F F₅ Fim₅ R₅ R ρ ρ₅ β₅ Vβ Z₅ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hC₀ : 1 ≤ C₀) (hq : 0 ≤ q)
    (hF₅ : F₅ = F - J + e + ib - m - iso) (hR₅ : R₅ + 2 * m + iso ≤ R + e + ib) (hFim : Fim₅ ≤ R₅)
    (hρ : ρ ≤ ρ₅ + m + iso) (hiso0 : 0 ≤ iso) (hiso : iso ≤ e) (hm : 0 ≤ m) (he : 0 ≤ e) (hβ : β₅ ≤ Vβ)
    (hZ : Z₅ ≤ e + 4 * (R - 1) + 3 * q) (hρ1 : 1 ≤ ρ) :
    -(η ^ 3 + 3 * η) * q + a * (m - J) - η * e - C₀ * η ^ 5 * (m + e) + b * β₅ - a * (F₅ - Fim₅) - η ^ 5 * ρ₅ + η * Z₅ ≤
      a * R + 4 * η * (R - 1) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * ρ - a * F + b * Vβ := by
  have hη5 : 0 < η ^ 5 := by positivity
  have hη3 : 0 < η ^ 3 := by positivity
  have h46 : 4 * η ^ 6 ≤ η ^ 5 := by nlinarith [mul_pos hη5 hη]
  have e1 : a * F₅ = a * (F - J + e + ib - m - iso) := by rw [hF₅]
  have e2 : a * Fim₅ ≤ a * R₅ := mul_le_mul_of_nonneg_left hFim ha
  have e3 : a * R₅ ≤ a * (R + e + ib - 2 * m - iso) := mul_le_mul_of_nonneg_left (by linarith) ha
  have e4 : b * β₅ ≤ b * Vβ := mul_le_mul_of_nonneg_left hβ hb
  have e5 : η * Z₅ ≤ η * (e + 4 * (R - 1) + 3 * q) := mul_le_mul_of_nonneg_left hZ hη.le
  have e6 : η ^ 5 * (ρ - m - iso) ≤ η ^ 5 * ρ₅ := mul_le_mul_of_nonneg_left (by linarith) hη5.le
  have e7 : η ^ 5 * (m + e) ≤ C₀ * η ^ 5 * (m + e) := by
    have : 0 ≤ (C₀ - 1) * (η ^ 5 * (m + e)) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have e8 : η ^ 5 * iso ≤ η ^ 5 * e := mul_le_mul_of_nonneg_left hiso hη5.le
  have e9 : (η ^ 5 - 4 * η ^ 6) / 2 ≤ (η ^ 5 - 4 * η ^ 6) * ρ := by
    have : 0 ≤ η ^ 5 - 4 * η ^ 6 := by linarith
    nlinarith
  have e10 : 0 ≤ η ^ 3 * q := mul_nonneg hη3.le hq
  nlinarith

end WaveTurbulence.FinalCountAsm
