/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SchwartzUniformNorm
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
/-! Choose the common low profile constant before nu, delta, and the number of layers. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set

abbrev LowProfileAt (P : WTParams) : Prop :=
  ∀ τ ∈ Icc (0 : ℝ) P.τstar,
    SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal (P.C₁ - 1)

theorem lowProfile_prefix : WTPrefix LowProfileAt := by
  intro d hd γ hγ
  refine ⟨1, by norm_num, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C, hC, hb⟩ := exists_uniform_SNormR hsol.1 (40 * d) (40 * d)
  refine ⟨C + 1, by linarith, 1, by norm_num, ?_⟩
  intro ν hν
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ D hD htime
  refine ⟨1, by norm_num, 2, by norm_num, ?_⟩
  intro L hL t ht
  simpa only [add_sub_cancel_right] using hb t ht

theorem lowProfile_largeConstantMonotone : LargeConstantMonotone LowProfileAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hprofile t ht
  exact (hprofile t ht).trans (ENNReal.ofReal_le_ofReal (by dsimp; linarith))

end WaveTurbulence.LGSpine
