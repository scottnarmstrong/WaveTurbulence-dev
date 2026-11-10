/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.AtomSmall
public import WaveTurbulence.Foundations.Regref.FourierAE

/-! # PROT-TA, Lemma 12.1: Fourier reconstruction of the consumed-modulation operator

For `h` on `ℝ³` with `h, ĥ ∈ L¹` (`ĥ = timeFourier h`): `h = ∫ ĥ(l) e^{2πi l·x} dl` a.e.; slicing through `u`
(`ae_slice`); and the atomwise identity (12.3): `∫_s^t e^{πiA(u-s)} e^{2πi l·(t,u,s)} du =
e^{2πi (l₀ t + (l₁+l₂) s)} h_{A/2+l₁}(t-s)`. Consequently `op_agree`: for a.e. `(t,s)` with `s < t`,
`T_A h (t,s) = ∫ ĥ(l) · atom` (before the cutoff `Φ`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

/-- The frequency `(l₀, l₁ + l₂)` of the output `(t,s)` for the input frequency `l = (l₀, l₁, l₂)`. -/
def nu (l : Fin 3 → ℝ) : Fin 2 → ℝ := ![l 0, l 1 + l 2]

theorem pairing_apply (r : ℕ) (t ξ : Fin r → ℝ) : timePairing r t ξ = ∑ i, t i * ξ i := rfl

/-- The atomwise identity (12.3). -/
theorem inner_eq (A : ℝ) (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) :
    ∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        (Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ) =
      (Real.fourierChar (timePairing 2 y (nu l)) : ℂ) * hz (A / 2 + l 1) (y 0 - y 1) := by
  have hsub := intervalIntegral.integral_comp_add_left (a := 0) (b := y 0 - y 1)
    (fun u : ℝ => Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        (Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ)) (y 1)
  simp only [add_zero, add_sub_cancel] at hsub
  rw [← hsub]
  unfold hz
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun w _ => ?_)
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [pairing_apply, Fin.sum_univ_three, Fin.sum_univ_two, nu]
  simp
  push_cast
  ring

end WaveTurbulence.Flower.ProtTa
