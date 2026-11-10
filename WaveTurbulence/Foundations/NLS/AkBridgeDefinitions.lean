/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.NLS.BridgeWeights

/-!
# Exact snapshot-5 a-system and norm identifications
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.NLSBridge

variable {d : ℕ}

/-- Snapshot 5 and the landed classed system have exactly the same bodies. -/
theorem isASolution_iff_nls (L γ δ T : ℝ) (c : (Fin d → ℤ) → ℂ)
    (a : ℝ → (Fin d → ℤ) → ℂ) : IsASolution L γ δ T c a ↔ NLS.IsAkSolution L γ δ T c a := Iff.rfl

/-- A uniform finite Japanese-bracket bound implies the exact snapshot restriction norm is finite. -/
theorem zNormOn_lt_top {L s : ℝ} {S : Set ℝ} {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : ∃ C, ∀ t ∈ S, ∀ n, jbr (latticePoint L n) ^ s * ‖a t n‖ ≤ C) :
    ZNormOn L s S a < ⊤ := by
  obtain ⟨C, hC⟩ := ha
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  unfold ZNormOn
  exact iSup_le fun t => iSup_le fun ht => iSup_le fun n => ENNReal.ofReal_le_ofReal (hC t ht n)

/-- The all-real bracket condition in snapshot 5 implies the landed rapid-decay predicate. -/
theorem isRapidDecay_of_draft {L : ℝ} (hL : 0 < L) {c : (Fin d → ℤ) → ℂ}
    (hc : ∀ s : ℝ, ∃ C, ∀ n, jbr (latticePoint L n) ^ s * ‖c n‖ ≤ C) : IsRapidDecay c :=
  NLS.bridge_isRapidDecay_of_weight_bounds hL hc

end WaveTurbulence.NLSBridge
