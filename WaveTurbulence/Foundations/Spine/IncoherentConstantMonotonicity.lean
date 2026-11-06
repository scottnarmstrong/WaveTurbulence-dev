/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLargeConstantBounds
/-! Large-constant monotonicity of the literal leafwise incoherent source estimate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem leafwiseIncoherentDecay_largeConstantMonotone : LargeConstantMonotone LeafwiseIncoherentDecayAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp n hn
  rw [N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  constructor
  · intro Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hb
    apply ((hsource p hp n hn).1 Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hb).trans
    exact mul_le_mul_of_nonneg_right
      (regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _) (by positivity)
  · intro X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi H B hb
    apply ((hsource p hp n hn).2 X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi H B hb).trans
    exact mul_le_mul_of_nonneg_right
      (regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _) (by positivity)

end WaveTurbulence.LGSpine
