/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # A fixed auxiliary exponent for the high-γ pair estimates -/

public section
namespace WaveTurbulence.CountLemmas

@[expose] noncomputable def highPairEpsilon (γ : ℝ) : ℝ := min ((2*γ-1)/100) ((1-γ)/100)

theorem highPairEpsilon_bounds {γ : ℝ} (hγ : (1 : ℝ)/2 < γ) (hγ1 : γ < 1) :
    0 < highPairEpsilon γ ∧ highPairEpsilon γ ≤ 1 ∧
    4*highPairEpsilon γ ≤ 2*γ-1 ∧ highPairEpsilon γ < 2-2*γ ∧
    highPairEpsilon γ < 2*γ-1 := by
  have hl := min_le_left ((2*γ-1)/100) ((1-γ)/100)
  have hr := min_le_right ((2*γ-1)/100) ((1-γ)/100)
  have hp : 0 < highPairEpsilon γ := lt_min (by linarith only [hγ]) (by linarith only [hγ1])
  exact ⟨hp,by dsimp only [highPairEpsilon]; linarith only [hr,hγ],
    by dsimp only [highPairEpsilon]; linarith only [hl,hγ],
    by dsimp only [highPairEpsilon]; linarith only [hr,hγ1],
    by dsimp only [highPairEpsilon]; linarith only [hl,hγ]⟩

end WaveTurbulence.CountLemmas
