/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularCauchyAlgebra

/-!
# Extended Cauchy–Schwarz pairing with a symmetric angular kernel
-/

public section

open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Absorbing the common kernel into the two Cauchy–Schwarz factors. -/
theorem ennreal_schur_pairing_kernel (E F A B K : ℝ≥0∞) :
    ((E ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2)) *
      (F ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2))) * K =
      (E * B * K) ^ ((1 : ℝ) / 2) * (F * A * K) ^ ((1 : ℝ) / 2) := by
  symm
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  calc
    _ = ((E ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2)) *
        (F ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2))) *
          (K ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2)) := by ac_rfl
    _ = _ := by rw [← pow_two, ← ENNReal.rpow_two, ennreal_half_sq]

end WaveTurbulence.WKEL2
