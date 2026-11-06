/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLargeConstantBounds
public import WaveTurbulence.Foundations.XChain.JbrBounds
public import WaveTurbulence.Foundations.Spine.SpineAt
public import WaveTurbulence.Foundations.Spine.TaylorBoundPrefix
/-! Large-constant monotonicity for the literal Prop 6.2 and landed Taylor bounds. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem sourceCoherentTaylor_largeConstantMonotone : LargeConstantMonotone SourceCoherentTaylorAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp R hR n hn t ht k
  rw [N_largeConstants] at hn
  have hL0 : 0 ≤ P.L := by linarith
  apply (hsource p hp R hR n hn t ht k).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (jbr_pos k).le _)
  exact source_coefficient_mono (by linarith) hCC hδ.le n

theorem taylorBound_largeConstantMonotone : LargeConstantMonotone TaylorBoundAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp n t ht
  apply (hsource p hp n t ht).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul hCC₂ (pow_le_pow_left₀ (by positivity : 0 ≤ P.C₁ * P.δ)
    (mul_le_mul_of_nonneg_right hCC hδ.le) n) (by positivity) (by linarith)

end WaveTurbulence.LGSpine
