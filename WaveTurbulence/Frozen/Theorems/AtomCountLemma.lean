/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.NearLattice
public import WaveTurbulence.Provider.AtomCountLemma

/-!
# atomCountLemma

Wave B tier B1 (WaveB1-Statements.lean), source: T Lemma `atomcountlem`, L2467–L2478; T L2472; T L1293–L2339. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B1.8 `atomCountLemma`** (T Lemma `atomcountlem`, L2467–L2478; DH23 Lemma A.3 (1), (2)).
For `k_j ∈ ℤ_L^d` in unit balls: (1) for `ε ∈ {(+,+), (+,-)}` the solutions of `ε₁k₁ + ε₂k₂ = k`,
`|ε₁|k₁|² + ε₂|k₂|² - β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-1} min(L^d, L^{d+1-2γ})`, for `ε = (+,-)` only
when `k ≠ 0` (DH23 A.3(1) assumes `|k₁ - k₂| ∼ R ≥ L^{-1}`; at `k = 0`, `γ > 1/2` the bound is false,
and so is TARGET's literal (atomcountbd), T L2472: stage-3 R4, new finding); (2) for `ε = (+,-)` and
`|k| ≥ L^{-γ+η}` (reading Q8b of "`|r| ≥ L^{-γ+η}`") they number `≤ C δ^{-1} L^{d-γ-η}`; (3) the solutions
of `k₁ - k₂ + k₃ = k`, `||k₁|² - |k₂|² + |k₃|² - β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-1} L^{2(d-γ)}`.
(atomcountbd3) is omitted (unused in T L1293–L2339). Deviations: Q8b reading; signs `(+,-,+)` for
`r = 3`. The counted sets are finite (stated). -/
theorem atomCountLemma :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ min γ (1 - γ) / 2 →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ β : ℝ, ∀ nk : Fin d → ℤ, ∀ a₁ a₂ a₃ : Mom d,
      let k := latticePoint L nk
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₂ (ε : ℤˣ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2 ∧ q.1 + (ε : ℤ) • q.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 + (ε : ℤ) * ‖latticePoint L q.2‖ ^ 2 - β| ≤ tol}
      let S₃ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2.1 ∧ NearLattice L a₃ q.2.2 ∧ q.1 - q.2.1 + q.2.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 - ‖latticePoint L q.2.1‖ ^ 2 + ‖latticePoint L q.2.2‖ ^ 2 - β| ≤
          tol}
      (∀ ε : ℤˣ, (S₂ ε).Finite) ∧
      (∀ ε : ℤˣ, (ε = -1 → nk ≠ 0) →
        ((S₂ ε).ncard : ℝ) ≤ C * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ))) ∧
      (L ^ (-γ + η) ≤ ‖k‖ → ((S₂ (-1)).ncard : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ) - γ - η)) ∧
      (S₃.Finite ∧ (S₃.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.atomCountLemma
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
