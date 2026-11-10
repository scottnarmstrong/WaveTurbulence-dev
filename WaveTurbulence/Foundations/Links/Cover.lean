/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.Order.Round

/-!
# Covering balls by unit balls (packet C2, infrastructure)

Statement-independent lemmas used for the localization of decorations (DH23 Lemma A.4,
TARGET Lemma `treelemma` (2)):

* `exists_unit_cover`: in a proper normed group, the ball of radius `R` is covered by finitely many
  closed unit balls; translating gives a cover of any ball of radius `R` by the same number of unit
  balls (`exists_unit_cover_at`);
* `exists_int_center`: on the line, rounding gives an integer within `1/2`.
-/

@[expose] public section

namespace WaveTurbulence.Links

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- The closed ball of radius `R` is covered by finitely many closed unit balls. -/
theorem exists_unit_cover (R : ℝ) : ∃ F : Finset E, ∀ x : E, ‖x‖ ≤ R → ∃ p ∈ F, ‖x - p‖ ≤ 1 := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : E) R) (by norm_num : (0 : ℝ) < 1)
  refine ⟨ht.toFinset, fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : E) R := by simpa using hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcov hx')
  refine ⟨p, ht.mem_toFinset.mpr hp, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hxp
  exact hxp.le

/-- Translated covers: the same finite family of offsets covers every ball of radius `R`. -/
theorem exists_unit_cover_at (R : ℝ) : ∃ F : Finset E, ∀ c x : E, ‖x - c‖ ≤ R →
    ∃ p ∈ F, ‖x - (c + p)‖ ≤ 1 := by
  obtain ⟨F, hF⟩ := exists_unit_cover (E := E) R
  refine ⟨F, fun c x hx => ?_⟩
  obtain ⟨p, hp, hxp⟩ := hF (x - c) hx
  exact ⟨p, hp, by rwa [sub_add_eq_sub_sub]⟩

end WaveTurbulence.Links
