/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Glue.Halves
public import WaveTurbulence.Foundations.GammaLow.LGLow.Statement
public import WaveTurbulence.Frozen.Theorems.LayergardenV2

/-! # L0 GLUE: `layergarden` (v1) from the sealed `layergarden_v2` and LG-low

Provider skeleton (conditional helper, distinct name; not a source result). Its conclusion is the type of the frozen
DRAFT_SORRY anchor `WaveTurbulence.layergarden` (`Frozen/Theorems/Layergarden.lean`), pasted verbatim by
`Glue/tools/gen_glue.py`; the anchor itself is not imported (AGENTS rule 7). -/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.GammaLow.Glue

/-- **`layergarden` (v1, `0 < γ < 1`) from LG-low**: `wtPrefix_of_halves` of the sealed `layergarden_v2` and the
low half `LGLow.LayergardenLowGate`. -/
theorem layergarden_of_low (hLG : WaveTurbulence.GammaLow.LGLow.LayergardenLowGate) : WTPrefix fun P =>
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
  wtPrefix_of_halves WaveTurbulence.layergarden_v2 hLG

end WaveTurbulence.GammaLow.Glue
