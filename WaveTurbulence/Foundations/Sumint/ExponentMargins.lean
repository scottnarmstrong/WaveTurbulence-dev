/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
import Mathlib.Tactic

/-!
# Dimension-dependent exponent margins in sumint

For `d ≥ 2`, the source decay exponent γ₁ is at least `2 min(γ,1-γ)`.
The margin is used when reserving weight decay for the bad-block case (d),
including the F23 branch for γ close to one.
-/

public section

namespace WaveTurbulence.Sumint

/-- The basic positive decay exponent in the source proposition. -/
@[expose] def gammaBase (γ : ℝ) : ℝ := min γ (1 - γ)

/-- The exact decay exponent used by the draft weight bounds. -/
@[expose] def gammaWeight (d : ℕ) (γ : ℝ) : ℝ :=
  min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))

/-- Positivity holds throughout the source parameter range. -/
theorem gammaBase_pos {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) : 0 < gammaBase γ := by
  exact lt_min hγ.1 (by linarith [hγ.2])

/-- In dimension at least two the weight exponent contains twice the basic gain. -/
theorem two_gammaBase_le_gammaWeight {d : ℕ} (hd : 2 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) : 2 * gammaBase γ ≤ gammaWeight d γ := by
  have h0 : gammaBase γ ≤ γ := min_le_left _ _
  have h1 : gammaBase γ ≤ 1 - γ := min_le_right _ _
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 ≤ 1 - γ := by linarith [hγ.2]
  apply le_min (by linarith)
  apply le_min (by dsimp [gammaBase] at *; linarith)
  have hm := mul_nonneg (sub_nonneg.mpr (show 1 ≤ (d : ℝ) - 1 by linarith)) hp
  nlinarith

end WaveTurbulence.Sumint
