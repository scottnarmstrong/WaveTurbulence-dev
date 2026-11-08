/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleSum
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.FlowerSumP
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.InstDecidableEqFixPat
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.TreeKind
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixP
import WaveTurbulence.Foundations.Flower.Top.Proof

/-!
# Provider for `WaveTurbulence.layergardenFlower_v3` (the product-form flower cutoff successor, ruling D13)

The proof of the frozen anchor `WaveTurbulence.layergardenFlower_v3` (T Prop `flowerest1`, L2279–L2305; T L2306–L2338; WAVE-B v2 §4.15; T L2280; T (flowerest2); T (newnormn); T L2331; T L2312; T L2290) is assembled here under the export
`WaveTurbulence.Provider.layergardenFlower_v3`.
The proof is the flower world's `WaveTurbulence.Flower.Top.layergardenFlower_v3_proof` (`WaveTurbulence.Foundations.Flower.Top.Proof`), landed by the final flower port:
TARGET Prop `flowerest1` for every kind, pattern vector and `†`, with the product-form cutoffs of ruling
D13. This module must not import the frozen anchor.
The proof modules are imported privately (`import`), so that the frozen anchor elaborates its statement
in its freeze environment.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.Provider

open Classical in
/-- The frozen statement of `WaveTurbulence.layergardenFlower_v3`, verbatim,
proved by the assembly in the module docstring. -/
theorem layergardenFlower_v3 : WTPrefixP fun Pm P => 1 / 2 < P.γ →
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
  WaveTurbulence.Flower.Top.layergardenFlower_v3_proof

end WaveTurbulence.Provider
