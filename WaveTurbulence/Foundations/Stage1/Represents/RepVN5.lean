/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D: `RepIntC` to `RepresentsIntA` (AMEND9 exponent `η²/2 · b_sk`)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory WaveTurbulence.RepAnalytic WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS Set

/-- The bound of `RepresentsIntA`. -/
noncomputable def repBoundA (P : WTParams) {R : ℕ} (π : Stage1Piece P R) (n : ℕ) (s : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s

theorem RepIntC.toRepresentsIntA {P : WTParams} {R : ℕ} {π : Stage1Piece P R} {tt : Fin (2 * R) → ℝ}
    {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {val : ℂ} {B : ℝ}
    (h : RepIntC π tt base roots val B) (n : ℕ) (s : ℝ) (hB : B ≤ repBoundA P π n s) :
    π.RepresentsIntA n tt base roots s val := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  let _ : MeasurableSpace Ξ := ⊤
  have : MeasurableSingletonClass Ξ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hint, hint2⟩ := integral_count_eq_tsum _ h1
  obtain ⟨hint', hint2'⟩ := integral_count_real_eq_tsum _ h3.norm
  refine ⟨Ξ, inferInstance, Measure.count, w, ctr, edge, hinge, freq, hint, ?_, hint', ?_, h5⟩
  · rw [hint2]; exact h2
  · rw [hint2']; exact h4.trans hB

end WaveTurbulence.Represents
