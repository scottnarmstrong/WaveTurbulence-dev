/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# WeightedL2Norm

Deng–Hani, L599 (blowuptest), L2515 (Z_s); GIT20 L549. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The weighted norm `‖f‖_{Z_s} = ‖⟨k⟩^s f‖_{L²_k}` of the blow-up criterion (blowuptest) and of
Appendix C (L2515), with `⟨k⟩ = (1 + |k|²)^{1/2}` (GIT20 L549; the source does not define `⟨k⟩`). -/
def weightedL2Norm {d : ℕ} (s : ℝ) (f : Mom d → ℝ) : ℝ :=
  Real.sqrt (∫ k : Mom d, ((1 + ‖k‖ ^ 2) ^ (s / 2) * f k) ^ 2)

end WaveTurbulence
