/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourMomentDecay
import Mathlib.Tactic

/-!
# Endpoint Fourier moments before integration in frequency

The right hand side retains the Fourier transforms of the four actual
derivatives. Hausdorff–Young can therefore estimate them in `L^{p'}`.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Two-bracket decay with the derivative Fourier transforms retained pointwise. -/
theorem norm_timeFourier_le_two_brackets_fourier_sum {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ξ : Fin 2 → ℝ) :
    ‖timeFourier f ξ‖ ≤
      4 * (∑ j : Fin 4, ‖timeFourier (fourTimeDerivatives f j) ξ‖) /
        (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2)) := by
  let S := ∑ j : Fin 4, ‖timeFourier (fourTimeDerivatives f j) ξ‖
  have hs (j : Fin 4) : ‖timeFourier (fourTimeDerivatives f j) ξ‖ ≤ S :=
    Finset.single_le_sum (f := fun j : Fin 4 => ‖timeFourier (fourTimeDerivatives f j) ξ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h0 := timeDirectionalDerivative_single (hf.differentiable (by simp)) (0 : Fin 2)
  have h1 := timeDirectionalDerivative_single (hf.differentiable (by simp)) (1 : Fin 2)
  have hp1 := WaveTurbulence.contDiff_infty_partialDeriv hf 1
  have h01 : timeDirectionalDerivative (Pi.single 0 1)
      (timeDirectionalDerivative (Pi.single 1 1) f) =
      WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 f) := by
    rw [h1, timeDirectionalDerivative_single (hp1.differentiable (by simp))]
  have hx := timeFourier_word_moment_le hf hc [Pi.single 0 1] ξ
  have hy := timeFourier_word_moment_le hf hc [Pi.single 1 1] ξ
  have hxy := timeFourier_word_moment_le hf hc [Pi.single 0 1, Pi.single 1 1] ξ
  simp only [timeWordDerivative, h0, h1, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hx hy
  simp only [timeWordDerivative, h01, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hxy
  apply frequency_decay_two (timeFourier f ξ) (ξ 0) (ξ 1) S
  · simpa only [fourTimeDerivatives, Matrix.cons_val_zero] using hs 0
  · have hj := hs 1
    change ‖timeFourier (WaveTurbulence.partialDeriv 0 f) ξ‖ ≤ S at hj
    have hh := hx.trans hj
    simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using hh
  · have hj := hs 2
    change ‖timeFourier (WaveTurbulence.partialDeriv 1 f) ξ‖ ≤ S at hj
    have hh := hy.trans hj
    simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using hh
  · have hj := hs 3
    change ‖timeFourier (WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 f)) ξ‖ ≤ S at hj
    have hh := hxy.trans hj
    simpa [timePairing, dotProduct, Fin.sum_univ_two, Pi.single_apply] using hh

end WaveTurbulence.Fourier
