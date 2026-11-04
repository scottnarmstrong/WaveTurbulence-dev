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
public import WaveTurbulence.Foundations.WeylSums.QuadExpSum2

/-!
# Provider for `WaveTurbulence.quadExpSum2`

The proof of the frozen anchor `WaveTurbulence.quadExpSum2` (ruling D7), exported as
`WaveTurbulence.Provider.quadExpSum2`, from the landed `WeylSums.quadExpSum2_bound` (TARGET Lemma 5.3) through
the carrier identities of `Foundations/WeylSums/FrozenBridge`. This module must not import the frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- **B1.9 `quadExpSum2`** (T Lemma `lemlayer2`, L970–L977; DH23 Lemma 6.6(2)). Uniformly in
`a, b, ξ, ξ' ∈ ℝ^d`: `∫_{L ≤ |s| ≤ T₀L^{2γ}} |∑_{x,y ∈ ℤ_L^d} χ₀(x-a)χ₀(y-b) e(⟨x,ξ⟩+⟨y,ξ'⟩+s⟨x,y⟩)| ds
≤ C L^{2d-2(d-1)(1-γ)+η}`, `C = C(d,γ,η,T₀)` (T: `≲₂` with `T₀ = 𝔇δ`). The lattice sum has finitely many
nonzero terms (`χ₀` has compact support). -/
theorem quadExpSum2 :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b ξ ξ' : Mom d,
      ∫ s in {s : ℝ | L ≤ |s| ∧ |s| ≤ T₀ * L ^ (2 * γ)},
          ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ),
            ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2 - b) : ℝ) : ℂ) *
              eZ (inner ℝ (latticePoint L q.1) ξ + inner ℝ (latticePoint L q.2) ξ' +
                s * inner ℝ (latticePoint L q.1) (latticePoint L q.2))‖ ≤
        C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) := by
  intro d hd γ hγ η hη T₀ hT₀
  obtain ⟨C, L₀, h⟩ := WeylSums.quadExpSum2_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨C, L₀, fun L hL a b ξ ξ' => ?_⟩
  simpa only [WeylSums.bilinearLatticeSum, WeylSums.chi0Vec_eq_latticeCutoff, WeylSums.eZ_eq_e] using
    h L hL a b ξ ξ'

end WaveTurbulence.Provider
