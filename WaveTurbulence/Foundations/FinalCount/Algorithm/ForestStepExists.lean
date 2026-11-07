/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestDispatchStep
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestMoveBranches
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestGapUniform
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DispatchExistence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ProblemComponentSplit
import Mathlib.Tactic

/-! # Every admissible nonempty forest has a source step

Splits and discards come first; a ladder mode continues the primary rule
three at the stored head; otherwise the head component receives the
source dispatch. All thresholds are uniform in both finite carriers.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Set
universe u v

theorem forestSlack_nonladder {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}
    (F : CountingForest.{u,v} V d L γ η w c B)
    (h : ∀ p hp head,F.mode ≠ ForestScanMode.ladder p hp head) : forestSlack F = 0 := by
  unfold forestSlack
  split
  · rename_i p hp head hm
    exact absurd hm (h p hp head)
  · rfl

theorem good_le_fine (γ η L : ℝ) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (hL : 1 ≤ L) :
    ENNReal.ofReal (L^(-5*min γ (1-γ)/8)) ≤ ENNReal.ofReal (L^(-η/2)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hL
  linarith only [hη,hηγ]

theorem forestSlack_ladder {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}
    (F : CountingForest.{u,v} V d L γ η w c B) (p : Problem.{u,v} V d L w c F.gap) (hp : p ∈ F.problems)
    (head : LadderHead p.state) (h : F.mode = .ladder p hp head)
    (h3 : p.state.graph.deg (head.figure.vertex 3) = 4) (h4 : p.state.graph.deg (head.figure.vertex 4) = 4) :
    forestSlack F = 0 := by
  unfold forestSlack
  rw [h]
  simp [h3,h4]

end WaveTurbulence.Mole.AppbAlgorithm
