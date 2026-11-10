/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Jets
public import WaveTurbulence.Foundations.Stage1.Represents.RepSup1
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreAux

/-! # STAGE1W-O4: the SNorm multiplier lemma and superposition transports (row O4c)

* `snorm_value_mul_le`: a Fourier-presented weight `g = M.value` with `J`-th moment mass `≤ c` is a bounded multiplier
  on `𝔖^{A,0}`, `A ≤ J`: `SNorm A 0 (g a) ≤ 2^A d^A (2π)^A c · SNorm A 0 a`.
* `CenSup.mul_left`, `Sup.mul_left`: a superposition times a bounded multiplier of the momentum.
* `CenSup.update0`, `Sup.update0`: freezing the first time coordinate at a constant (the clamp used at slots whose
  root is a garden root). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS

variable {d : ℕ}

/-- The multiplier constant of a weight with moment mass `c`. -/
def multC (d A : ℕ) (c : ℝ) : ℝ := 2 ^ A * (d : ℝ) ^ A * ((2 * π) ^ A * c)

theorem multC_pos (d A : ℕ) (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) : 0 < multC d A c := by
  unfold multC
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- **The SNorm multiplier lemma** for a Fourier-presented weight. -/
theorem snorm_value_mul_le {α : Type*} [MeasurableSpace α] (M : Cut2A.SpatialMeasure (Mom d) α)
    (hd : 1 ≤ d) {J A : ℕ} (hAJ : A ≤ J) {c : ℝ} (hc : 0 < c)
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c)
    (a : Mom d → ℂ) (ha : ContDiff ℝ A a) :
    SNorm A 0 (fun k => M.value k * a k) ≤ ENNReal.ofReal (multC d A c) * SNorm A 0 a := by
  by_cases htop : SNorm A 0 a = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using multC_pos d A hd hc)]
    exact le_top
  set CF : ℝ := (SNorm A 0 a).toReal with hCF
  have hF : SNorm A (0 + 0) a ≤ ENNReal.ofReal CF := by
    rw [zero_add, hCF, ENNReal.ofReal_toReal htop]
  have hgd : ContDiff ℝ A M.value := (contDiff_value M hM).of_le (by exact_mod_cast hAJ)
  have hjet : ∀ r ≤ A, ∀ x, ‖iteratedFDeriv ℝ r M.value x‖ ≤ ((2 * π) ^ A * c) * jbr x ^ 0 := by
    intro r hr x
    rw [pow_zero, mul_one]
    refine (norm_iteratedFDeriv_value_le M hc.le hM r (hr.trans hAJ) x).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [pi_gt_three]) hr) hc.le
  have key := LGSpine.SNorm_mul_of_polynomial_jet_bound (A := A) (B := 0) (M := 0) hd M.value a hgd ha
    ((2 * π) ^ A * c) CF (by positivity) ENNReal.toReal_nonneg hjet hF
  refine key.trans (le_of_eq ?_)
  rw [hCF, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (multC_pos d A hd hc).le, ENNReal.toReal_ofReal
    ENNReal.toReal_nonneg]
  unfold multC
  ring_nf


end WaveTurbulence.Flower.Stage1WNoVine
