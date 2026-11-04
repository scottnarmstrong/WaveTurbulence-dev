/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.WickNormalization
import Mathlib.Basic.ENNReal.Real

/-! # The trace cost is absorbed in the actual Wick weighted mass -/

public section
namespace WaveTurbulence.RegAsymp
open scoped ENNReal

/-- After the simultaneous trace cost is paid per removed link, both
the source mass and the fixed Gaussian normalization retain gamma1 decay. -/
theorem wick_weighted_trace_mass_budget {d r : ℕ} (hd : 3 ≤ d) {L γ cost : ℝ}
    (hL : 1 ≤ L) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hr : 1 ≤ r)
    (hcost : cost ≤ L^((r:ℝ)/4)) (H G : ℝ≥0∞) :
    ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r)*(ENNReal.ofReal cost*H+G) ≤
      ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*(H+G) := by
  have hgain := wick_gain_after_trace hd hL hγ hr
  have hp : (1:ℝ) ≤ L^((r:ℝ)/4) := Real.one_le_rpow hL (by positivity)
  have hmain : ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r)*ENNReal.ofReal cost ≤
      ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ)) := by
    calc
      _ ≤ ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r)*ENNReal.ofReal (L^((r:ℝ)/4)) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hcost)
      _ = ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r*L^((r:ℝ)/4)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hgain
  have hgauss : ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r) ≤
      ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ)) := by
    apply ENNReal.ofReal_le_ofReal
    exact (le_mul_of_one_le_right (by positivity) hp).trans hgain
  calc
    _ = (ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r)*ENNReal.ofReal cost)*H +
        ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^r)*G := by ring
    _ ≤ ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*H +
        ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*G :=
      add_le_add (mul_le_mul' hmain le_rfl) (mul_le_mul' hgauss le_rfl)
    _ = _ := by rw [mul_add]

end WaveTurbulence.RegAsymp
