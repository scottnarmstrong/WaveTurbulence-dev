/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleRemainder
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.IsBalancedSig
public import WaveTurbulence.Frozen.Defs.JbrProd
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.SNorm
public import WaveTurbulence.Frozen.Defs.TruncSum
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTParamsR
public import WaveTurbulence.Frozen.Defs.WTParamsTheta
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Provider.LayergardenV2

/-!
# layergarden

Wave B tier B1 (WaveB1-Statements.lean), source: T Prop `layergarden`, L761–L779; T L776; WAVE-B v2 §4.2; T L762. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Versioned successor (ruling D9; docs/ERRATA-AND-DEVIATIONS.md E1): restricted to `1 / 2 < γ < 1`.**
For `0 < γ ≤ 1/2` the source proof chain fails at DH23 Prop 9.6 (necklace counterexample); the original
anchor stays frozen and open. Apart from this restriction the statement is the original's, verbatim.

**B1.2 `layergarden`** (T Prop `layergarden`, L761–L779; deterministic, F36; time parameter
F27). For `0 ≤ p < 𝔇`, remainders with (ansatz2) bounds, inputs `F_q = φ(δq) + R_q`, every
`t ∈ (p, p+1]` and `N ≤ N_{p+1}^4`: (1) for `2 ≤ m ≤ 10 R_{p+1}` the truncated garden sum is
`≤ (∏⟨n_j⟩)^{-4Λ_{p+1}} L^{-(m-1)/4} δ^{2νN}`; (2)(a) the lattice couple sum vanishes off the diagonal;
(2)(b) `k ↦ 𝒦^tr_{p+1,N}(t;k) - [N even] 𝒰^{(p)}_{N/2}(t,k)` has
`𝔖^{4Λ_{p+1},4Λ_{p+1}}` norm `≤ L^{-(4θ_{p+1}+θ_p)/5} δ^{2νN}` (so it is `C^{4Λ_{p+1}}`; TARGET L776
claims no more: a smoothness conjunct was false, stage-3 R2).
Deviations (WAVE-B v2 §4.2): (D1) the induction hypothesis is replaced by `RemainderBound`;
(D2) `t ∈ (p, p+1]`; (D3) (estcouple)+(estcouple2) merged; (D4) shared sums; (D5) general carriers.
Note T L762: for `N ≤ N_{p+1}^4` the attached-garden truncation is void. -/
theorem layergarden_v2 : WTPrefix fun P => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ N ≤ P.N (p + 1) ^ 4,
      (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
        truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
