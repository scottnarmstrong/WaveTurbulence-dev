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
public import WaveTurbulence.Foundations.CountLemmas.CountLemma

/-!
# Provider for `WaveTurbulence.countLemma`

The proof of the frozen anchor `WaveTurbulence.countLemma` (ruling D7), exported as
`WaveTurbulence.Provider.countLemma`, stated with the frozen `NearLattice`; the CountLemmas proof uses its own
`CountLemmas.NearLattice` with the identical body, so the term checks by unfolding. This module must not
import the frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- **B1.7 `countLemma`** (T Lemma `countlem`, L2459–L2466; DH23 Lemma A.2 (1), (3); F3 revised,
G-5). For `x, y, z ∈ ℤ_L^d` in unit balls, `|r| ∼ P` (constant `c₀`), `ξ ∈ {x, y, x+y}`,
`ζ ∈ {x-v, x+y-v, x+y-v-z}`, `𝔛 = min((log L)², 1 + δL^{2γ}P)`: (1) the pairs with
`|⟨x,y⟩-α|, |⟨r,ξ⟩-β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-1} L^{2(d-γ)} 𝔛^{-1}`; (2) the triples with
`|⟨x,y⟩-α|, |⟨ζ,z⟩-β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-2} L^{3(d-γ)-γ₀}`. The counted sets are finite
(stated, against junk `ncard`). Constants `C(d,γ,η,c₀)` uniform in `δ`, `η ≤ η₀(d,γ)`, and
`L ≥ L₀(δ)`: DH23's bound (countc1-1) needs `δ^{-1}L^{-10η} ≤ (log L)^{-2}` (stage-3 R5; consumers fix
`δ` before `L`). The binder `η ∈ (0, η₀]` does not occur in the bound; it is kept so that `C` may
depend on `η` as in the source (delta-stage-3 O1). Deviations: `|r| ∼₀ P` made explicit with `c₀`; for `P = 1` also `|r| ≤ c₀` (DH23's
dyadic setting; in every use `r` is a difference of vectors in unit balls; stage-3 O2). -/
theorem countLemma :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀,
    ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ C : ℝ, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α β : ℝ,
    ∀ (nr nv : Fin d → ℤ) (Pr : ℝ), (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) →
      (Pr = 0 → nr = 0) →
      (0 < Pr → Pr < 1 → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀ * Pr) →
      (Pr = 1 → c₀⁻¹ ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀) →
    ∀ ax ay az : Mom d, ∀ ξsel : Fin 3, ∀ ζsel : Fin 3,
      let r := latticePoint L nr
      let v := latticePoint L nv
      let 𝔛 := min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr)
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₁ : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ tol ∧
        |inner ℝ r (![latticePoint L q.1, latticePoint L q.2,
            latticePoint L q.1 + latticePoint L q.2] ξsel) - β| ≤ tol}
      let S₂ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧
        NearLattice L ay q.2.1 ∧ NearLattice L az q.2.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ tol ∧
        |inner ℝ (![latticePoint L q.1 - v, latticePoint L q.1 + latticePoint L q.2.1 - v,
            latticePoint L q.1 + latticePoint L q.2.1 - v - latticePoint L q.2.2] ζsel)
          (latticePoint L q.2.2) - β| ≤ tol}
      (S₁.Finite ∧ (S₁.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * 𝔛⁻¹) ∧
      (S₂.Finite ∧ (S₂.ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) :=
  CountLemmas.countLemma_bound

end WaveTurbulence.Provider
