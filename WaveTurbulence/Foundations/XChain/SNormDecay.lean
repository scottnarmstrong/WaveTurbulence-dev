/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormOperations
/-! The exact complex spatial norm controls pointwise decay at every momentum. -/
public section
namespace WaveTurbulence.Induct
open scoped ENNReal

theorem SNorm_decay_bound {d A B : ℕ} (f : Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B f ≤ ENNReal.ofReal C) (k : Mom d) :
    ‖f k‖ ≤ C * jbr k ^ (-(B : ℝ)) := by
  have hb := SNorm_pointwise f C hC h k
  have hd := (le_div_iff₀ (pow_pos (jbr_pos k) B)).mpr
    (show ‖f k‖ * jbr k ^ B ≤ C by simpa only [mul_comm] using hb)
  simpa only [Real.rpow_neg (jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv] using hd

end WaveTurbulence.Induct
