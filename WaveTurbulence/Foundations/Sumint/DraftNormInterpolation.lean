/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.NormInterpolation
public import WaveTurbulence.Foundations.Sumint.InterpolationMargins
public import WaveTurbulence.Foundations.Sumint.TimeBridge
import Mathlib.Tactic

/-!
# Interpolation of the exact snapshot-5 norm

The bridge is proved against the unchanged snapshot. The endpoint bounds
must concern the same ambient function; no interpolation of unrelated
restriction-norm minimizers is used.
-/

public section

open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Hölder interpolation for the exact drafted general-output norm. -/
theorem XNorm00_interpolate {r : ℕ} {V : Type*} (θ θ' : ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 (a*θ+(1-a)*θ') F ≤ XNorm00 θ F^a * XNorm00 θ' F^(1-a) := by
  simpa only [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] using
    mixedFourierNorm00_interpolate θ θ' ha ha1 F

/-- The exact two source endpoints yield the exact target regularity `2η^8`. -/
theorem XNorm00_target_interpolate {r : ℕ} {V : Type*} {η : ℝ}
    (hη : 0 < η) (hsmall : 8 * η^8 < 1) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 (2*η^8) F ≤
      XNorm00 (1/4) F^(interpolationWeight η) *
        XNorm00 (-η^8) F^(1-interpolationWeight η) := by
  have hp : 0 < 1 + 4 * η^8 := by positivity
  have ha : 0 < interpolationWeight η := div_pos (by positivity) hp
  have ha1 : interpolationWeight η < 1 := by
    unfold interpolationWeight
    apply (div_lt_iff₀ hp).mpr
    linarith only [hsmall]
  have he : interpolationWeight η * (1/4) + (1-interpolationWeight η) * (-η^8) = 2*η^8 := by
    linarith only [interpolation_regularity η]
  rw [← he]
  exact XNorm00_interpolate (1/4) (-η^8) ha ha1 F

end WaveTurbulence.Sumint
