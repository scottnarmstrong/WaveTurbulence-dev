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
# resSlice

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The slice integral `S_ℓ(t) = ∫_{w ⊥ ℓ} Ψ(k+ℓ, k+ℓ+x, k+x)`, `x = t ℓ/|ℓ| + w`, of the kernel
on the hyperplanes `⟨ℓ, x⟩ = t|ℓ|`. -/
noncomputable def resSlice {d : ℕ} (Ψ : Mom d → Mom d → Mom d → ℝ) (k ℓ : Mom d) (t : ℝ) : ℝ :=
  ∫ w : ↥(ℝ ∙ ℓ)ᗮ, Ψ (k + ℓ) (k + ℓ + (t • (‖ℓ‖⁻¹ • ℓ) + w)) (k + (t • (‖ℓ‖⁻¹ • ℓ) + w))

end WaveTurbulence
