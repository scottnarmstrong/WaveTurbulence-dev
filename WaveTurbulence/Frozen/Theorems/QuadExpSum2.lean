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
public import WaveTurbulence.Provider.QuadExpSum2

/-!
# quadExpSum2

Wave B tier B1 (WaveB1-Statements.lean), source: T Lemma `lemlayer2`, L970–L977; DH23 Lemma 6.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
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
        C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.quadExpSum2
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
