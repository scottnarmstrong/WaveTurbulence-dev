/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Chi0Vec
public import WaveTurbulence.Frozen.Defs.EZ
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Foundations.WeylSums.FrozenBridge
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum3

/-!
# Provider for `WaveTurbulence.quadExpSum3`

The proof of the frozen anchor `WaveTurbulence.quadExpSum3` (ruling D7), exported as
`WaveTurbulence.Provider.quadExpSum3`, from the landed `WeylSums.quadExpSum3_bound` (TARGET `lemcubic`)
through the carrier identities of `Foundations/WeylSums/FrozenBridge`. This module must not import the frozen
anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- **B1.10 `quadExpSum3`** (T Lemma `lemcubic`, L1554–L1593). For
`Λ ∈ {⟨x,z⟩, ⟨z, x+y-z⟩}`, uniformly in `a, b, c, ξ, ξ', ξ''`:
`∫∫_{L ≤ max(|t|,|s|), |t|,|s| ≤ T₀L^{2γ}} |∑_{x,y,z} χ₀(x-a)χ₀(y-b)χ₀(z-c)
e(t⟨x,y⟩ + sΛ + ⟨ξ,x⟩ + ⟨ξ',y⟩ + ⟨ξ'',z⟩)| dt ds ≤ C L^{3d+γ-2γ₀} log L`, `C = C(d,γ,T₀)`. -/
theorem quadExpSum3 :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ Λsel : Bool, ∀ a b c ξ ξ' ξ'' : Mom d,
      let Λf : Mom d → Mom d → Mom d → ℝ := fun x y z =>
        if Λsel then inner ℝ x z else inner ℝ z (x + y - z)
      ∫ ts in {ts : ℝ × ℝ | L ≤ max |ts.1| |ts.2| ∧ |ts.1| ≤ T₀ * L ^ (2 * γ) ∧
          |ts.2| ≤ T₀ * L ^ (2 * γ)},
          ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
            ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2.1 - b) *
                chi0Vec (latticePoint L q.2.2 - c) : ℝ) : ℂ) *
              eZ (ts.1 * inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) +
                ts.2 * Λf (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2) +
                inner ℝ ξ (latticePoint L q.1) + inner ℝ ξ' (latticePoint L q.2.1) +
                inner ℝ ξ'' (latticePoint L q.2.2))‖ ≤
        C * L ^ (3 * (d : ℝ) + γ - 2 * min γ (1 - γ)) * Real.log L := by
  intro d hd γ hγ T₀ hT₀
  obtain ⟨C, L₀, h⟩ := WeylSums.quadExpSum3_bound d hd γ hγ T₀ hT₀
  refine ⟨C, L₀, fun L hL Λsel a b c ξ ξ' ξ'' => ?_⟩
  simpa only [WeylSums.cubicLatticeSum, WeylSums.cubicQuadraticForm, WeylSums.timeSquareWindow,
    WeylSums.chi0Vec_eq_latticeCutoff, WeylSums.eZ_eq_e] using h L hL Λsel a b c ξ ξ' ξ''

end WaveTurbulence.Provider
