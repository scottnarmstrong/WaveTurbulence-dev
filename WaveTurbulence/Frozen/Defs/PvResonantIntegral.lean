/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.ResSlice
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# pvResonantIntegral

Wave B tier B2 (WaveB2-Regular.lean), source: T (regref3-3); WAVE-B §2.8. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **The principal-value resonant integral** `p.v.∫ δ(k₁-k₂+k₃-k) Ψ(k₁,k₂,k₃)/Ω dk` with
`Ω = |k₁|²-|k₂|²+|k₃|²-|k|² = -2⟨ℓ, x⟩` (T (regref3-3), `𝙸 = 1`; WAVE-B §2.8) in the `collisionOp`
parametrization: the absolutely convergent symmetric-quotient form
`∫_ℓ -(2|ℓ|)^{-1} ∫_t (S_ℓ(t) - S_ℓ(-t)) / (2t) dt`. Same body as the landed
`∫ ℓ, energyInvSliceLimit (resonantKernel Ψ k) ℓ` (bridge `pvResonantIntegral_eq_energyInv`); it is
the cutoff limit `lim_{μ→∞} ∫∫ Ψ (1 - χ(μΩ))/Ω` for every admissible cutoff `χ`, for every kernel with
`DeltaKernel` decay of itself and its gradient, with no support radius: characterization
`tendsto_pvResonantIntegral_of_decay` (`WaveB2-Regular-probes.lean`; FINDINGS F66, independent audit F-5,
B2-CL-19), proved from the landed `Resonant.tendsto_energyInvIntegral_of_decay` (`Foundations/Resonant/PVDecay`,
wt-ansob). The compactly supported case is `tendsto_pvResonantIntegral`. -/
noncomputable def pvResonantIntegral {d : ℕ} (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ : Mom d, -(2 * ‖ℓ‖)⁻¹ *
    ∫ t : ℝ, 2⁻¹ * dslope (fun v => resSlice Ψ k ℓ v - resSlice Ψ k ℓ (-v)) 0 t

end WaveTurbulence
