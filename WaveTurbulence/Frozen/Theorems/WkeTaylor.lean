/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm
public import WaveTurbulence.Provider.WkeTaylor

/-!
# wkeTaylor

Wave B tier B1 (WaveB1-Statements.lean), source: T (wketaylor); L752–L758; WAVE-B §5. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B1.5 `wkeTaylor`** (T (wketaylor)–(taylorbound), L752–L758; F10). Under (Π) (statement
independent of `L`), for `0 ≤ p < 𝔇`: (0) the `t'`-integrands of (wketaylor2) are interval integrable
(no junk integrals, WAVE-B §5); (1) for `t ∈ [p,p+1]`, `k ∈ ℝ^d`: `∑_N |𝒰_N(t,k)| < ∞` and
`∑_N 𝒰_N(t,k) = φ(δt, k)`; (2) `‖𝒰_N(t)‖_{𝔖^{4Λ_{p+1},4Λ_{p+1}}} ≤ C₂ (C₁δ)^N`. Constants: `C₁` must
not depend on `𝔇` (it is chosen before `δ, 𝔇` in (Π)); `C₂` may. Deviations: item (1) for all `t`
(time parameter); item (0) added. -/
theorem wkeTaylor : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D →
      let U := wkeTaylorTerm (P.φ (P.δ * p)) P.δ p
      (∀ N, ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k, ∀ x ∈ Finset.Nat.antidiagonalTuple 3 N,
        IntervalIntegrable (fun t' => collisionOp (U (x 0) t') (U (x 1) t') (U (x 2) t') k)
          volume p t) ∧
      (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k, Summable (fun N => |U N t k|) ∧
        ∑' N, U N t k = P.φ (P.δ * t) k) ∧
      ∀ N, ∀ t ∈ Icc (p : ℝ) (p + 1),
        SNormR (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (U N t) ≤
          ENNReal.ofReal (P.C₂ * (P.C₁ * P.δ) ^ N) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.wkeTaylor
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
