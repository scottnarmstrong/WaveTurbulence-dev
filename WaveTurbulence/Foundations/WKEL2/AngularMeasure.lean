/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantSymmetry
public import WaveTurbulence.Foundations.WKEL2.ResonantPolarFull

/-!
# The symmetric angular resonant measure

Normalize the radial cutoff `|a|,|b| < 1` by `(d-1)^2` and push forward to unit
directions. Each radial integral is `1/(d-1)`, so this is the angular measure
in Corollary 2 of `docs/research/git20-general-d.md`.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Forget the two radii of a momentum pair. -/
@[expose] def pairDirections (p : Mom d × Mom d) : Mom d × Mom d :=
  (unitVec p.1, unitVec p.2)

/-- The direction map is measurable, including at zero. -/
theorem measurable_pairDirections : Measurable (pairDirections : Mom d × Mom d → _) :=
  (measurable_unitVec.comp measurable_fst).prodMk
    (measurable_unitVec.comp measurable_snd)

/-- Angular resonant measure, with radial mass normalized to one. -/
@[expose] def angularMeasure (e : Mom d) : Measure (Mom d × Mom d) :=
  ENNReal.ofReal (((d : ℝ) - 1) ^ 2) •
    Measure.map pairDirections ((resonantMeasure e).restrict (ball 0 1))

/-- Restricting resonant measure to a centered ball preserves swap invariance. -/
theorem map_swap_restrict_resonantMeasure {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    (R : ℝ) :
    Measure.map Prod.swap ((resonantMeasure e).restrict (ball 0 R)) =
      (resonantMeasure e).restrict (ball 0 R) := by
  have hpre : Prod.swap ⁻¹' (ball (0 : Mom d × Mom d) R) = ball 0 R := by
    ext p
    simp only [mem_preimage, mem_ball_zero_iff, Prod.norm_def]
    change max ‖p.2‖ ‖p.1‖ < R ↔ max ‖p.1‖ ‖p.2‖ < R
    rw [max_comm]
  have h := Measure.restrict_map (μ := resonantMeasure e) (s := ball 0 R) measurable_swap measurableSet_ball
  rw [map_swap_resonantMeasure he hd, hpre] at h
  exact h.symm

/-- Symmetry of the angular measure, including exceptional Borel sets. -/
theorem map_swap_angularMeasure {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d) :
    Measure.map Prod.swap (angularMeasure e) = angularMeasure e := by
  rw [angularMeasure, Measure.map_smul (hf := measurable_swap.aemeasurable),
    Measure.map_map measurable_swap measurable_pairDirections]
  have hcomm : (Prod.swap : Mom d × Mom d → Mom d × Mom d) ∘ pairDirections =
      pairDirections ∘ Prod.swap := rfl
  rw [hcomm, ← Measure.map_map measurable_pairDirections measurable_swap,
    map_swap_restrict_resonantMeasure he hd]

/-- Nonnegative Borel symmetry in the angular variables (Corollary 2). -/
theorem lintegral_angular_swap {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {G : Mom d × Mom d → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G (p.2, p.1) ∂angularMeasure e) = ∫⁻ p, G p ∂angularMeasure e := by
  calc
    _ = ∫⁻ p, G p ∂Measure.map Prod.swap (angularMeasure e) :=
      (lintegral_map hG measurable_swap).symm
    _ = _ := by rw [map_swap_angularMeasure he hd]

/-- Angular measure is finite in the dimensions used in the packet. -/
theorem angularMeasure_finite (e : Mom d) (hd : 2 ≤ d) : IsFiniteMeasure (angularMeasure e) := by
  have : IsFiniteMeasure ((resonantMeasure e).restrict (ball 0 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using resonantMeasure_ball_lt_top e hd 1⟩
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

end WaveTurbulence.WKEL2
