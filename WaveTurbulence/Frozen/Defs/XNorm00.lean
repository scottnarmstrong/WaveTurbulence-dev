/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MaxBracketPow
public import WaveTurbulence.Frozen.Defs.TimeFT

/-!
# XNorm00

Wave B tier B1 (WaveB1-System.lean), source: T L589. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

open Classical in
/-- **`‖F‖_{𝔛^{θ,0,0}}`** with an arbitrary type `V` of vector variables (T L589, last sentence):
`∫ max_i⟨λ_i⟩^θ sup_v |F̂(λ, v)| dλ`; `⊤` unless every `t ↦ F(t, v)` is integrable. -/
noncomputable def XNorm00 {r : ℕ} {V : Type*} (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) : ℝ≥0∞ :=
  if ∀ v, Integrable fun t => F t v then
    ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam * ⨆ v, ‖timeFT F lam v‖ₑ
  else ⊤

end Norms
end WaveTurbulence
