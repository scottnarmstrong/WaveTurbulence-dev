/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Algebra of the van der Corput exponent transforms

This module records only coordinate identities and admissible-coordinate
geometry. It does not assert that either transform preserves an analytic
exponent-pair predicate. Those closure theorems require the analytic
A/B-processes on an appropriate stable phase class.
-/

public section

namespace WaveTurbulence.VdCB

/-- Coordinate transform of the B-process. -/
@[expose] noncomputable def bTransform (p : ℝ × ℝ) : ℝ × ℝ := (p.2 - 1 / 2, p.1 + 1 / 2)

/-- Coordinate transform of the A-process. -/
@[expose] noncomputable def aTransform (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 / (2 * p.1 + 2), (p.1 + p.2 + 1) / (2 * p.1 + 2))

/-- The usual triangle of admissible exponent-pair coordinates. -/
@[expose] def AdmissibleCoordinates (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ 1 / 2 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.1 + p.2 ≤ 1

theorem bTransform_involutive (p : ℝ × ℝ) : bTransform (bTransform p) = p := by
  apply Prod.ext <;> dsimp only [bTransform] <;> ring

theorem admissibleCoordinates_bTransform {p : ℝ × ℝ} (hp : AdmissibleCoordinates p) :
    AdmissibleCoordinates (bTransform p) := by
  rcases hp with ⟨hκ0, hκ1, hlam0, hlam1, hsum⟩
  change 0 ≤ p.2 - 1 / 2 ∧ p.2 - 1 / 2 ≤ 1 / 2 ∧
    1 / 2 ≤ p.1 + 1 / 2 ∧ p.1 + 1 / 2 ≤ 1 ∧ (p.2 - 1 / 2) + (p.1 + 1 / 2) ≤ 1
  exact ⟨by linarith only [hlam0], by linarith only [hlam1], by linarith only [hκ0],
    by linarith only [hκ1], by linarith only [hsum]⟩

/-- The coordinate word needed for FINDINGS F3. This identity carries no
claim that the corresponding analytic closure theorems are already proved. -/
theorem bTransform_aTransform_three_half :
    bTransform (aTransform (aTransform (aTransform (1 / 2, 1 / 2)))) = (11 / 30, 16 / 30) := by
  norm_num [aTransform, bTransform]

/-- Arithmetic saving in the proposed circle-error transfer. -/
theorem circleExponent_classical_pair :
    (((11 / 30 : ℝ) + 16 / 30) / (1 + 11 / 30)) = 27 / 41 ∧ (27 / 41 : ℝ) < 2 / 3 := by
  constructor <;> norm_num

end WaveTurbulence.VdCB
