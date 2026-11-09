/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Glue.Halves
public import WaveTurbulence.Foundations.GammaLow.Flower.Statement
public import WaveTurbulence.Frozen.Theorems.LayergardenFlowerV3

/-! # L0 GLUE: `layergardenFlower_v4` from the sealed `layergardenFlower_v3` and FL-low

Provider skeleton (conditional helper, distinct name). Its conclusion is the type of the frozen DRAFT_SORRY anchor
`WaveTurbulence.layergardenFlower_v4` (ruling D16, `Frozen/Theorems/LayergardenFlowerV4.lean`), pasted verbatim by
`Glue/tools/gen_glue.py`; its statement block is byte-identical to the audited draft's (AUDIT-V4, sha256 4b29cdf4…).
The anchor itself is not imported (AGENTS rule 7). The low half is packet L8's
`GammaLow.Flower.LayergardenFlowerLowGate`. -/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.GammaLow.Glue

open Classical in
/-- **`layergardenFlower_v4` (`0 < γ < 1`) from FL-low**: `wtPrefixP_of_halves` of the sealed `layergardenFlower_v3`
and L8's low half. -/
theorem layergardenFlower_v4_of_low (hFL : WaveTurbulence.GammaLow.Flower.LayergardenFlowerLowGate) : WTPrefixP fun Pm P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)) :=
  wtPrefixP_of_halves WaveTurbulence.layergardenFlower_v3 hFL

end WaveTurbulence.GammaLow.Glue
