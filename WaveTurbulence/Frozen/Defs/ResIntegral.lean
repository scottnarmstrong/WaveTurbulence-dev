/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# resIntegral

Wave B tier B2 (WaveB2-Regular.lean), source: T (regref3-0); WAVE-B §2.8. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **The resonant integral** `∫ δ(k₁-k₂+k₃-k) δ(|k₁|²-|k₂|²+|k₃|²-|k|²) Ψ(k₁,k₂,k₃) dk` (T (regref3-0),
(regref3-3) with `𝙸 = 0`; WAVE-B §2.8), in the parametrization and hyperplane normalization of the
frozen `collisionOp` (`k₁ = k+ℓ`, `k₃ = k+w`, `k₂ = k+ℓ+w`, `w ⊥ ℓ`). Same body as the landed
`resonantIntegral` (bridge `resIntegral_eq_resonantIntegral`); `collisionOp` is a special case. -/
noncomputable def resIntegral {d : ℕ} (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ : Mom d, (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, Ψ (k + ℓ) (k + ℓ + w) (k + w)

end WaveTurbulence
