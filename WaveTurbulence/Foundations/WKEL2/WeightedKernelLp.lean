/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Lebesgue membership of the Japanese-bracket decay kernel

The nonsingular factor in the two Hölder estimates of research-note Lemma 4.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The decay kernel `⟨k⟩⁻ᵃ` used in the Hölder estimates. -/
@[expose] def japaneseDecay (a : ℝ) (k : Mom d) : ℝ :=
  (1 + ‖k‖ ^ 2) ^ (-a / 2)

/-- The decay kernel is nonnegative. -/
theorem japaneseDecay_nonneg (a : ℝ) (k : Mom d) : 0 ≤ japaneseDecay a k :=
  Real.rpow_nonneg (by positivity) _

/-- For a nonnegative exponent, the decay kernel is bounded by one. -/
theorem japaneseDecay_le_one {a : ℝ} (ha : 0 ≤ a) (k : Mom d) :
    japaneseDecay a k ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [sq_nonneg ‖k‖]) (by linarith only [ha])

/-- Integrability of the Japanese-bracket decay kernel above the dimension. -/
theorem integrable_japaneseDecay (a : ℝ) (ha : (d : ℝ) < a) :
    Integrable (japaneseDecay (d := d) a) :=
  integrable_rpow_neg_one_add_norm_sq (by simpa only [finrank_euclideanSpace_fin] using ha)

/-- The exact `a*p > d` membership criterion needed for the smooth Hölder factor. -/
theorem memLp_japaneseDecay (a p : ℝ) (hp : 0 < p) (ha : (d : ℝ) < a * p) :
    MemLp (japaneseDecay (d := d) a) (ENNReal.ofReal p) := by
  have hc : Continuous (japaneseDecay (d := d) a) := by
    have hb : Continuous (fun k : Mom d => 1 + ‖k‖ ^ 2) := by fun_prop
    exact hb.rpow_const (fun _ => Or.inl (by positivity))
  apply (integrable_norm_rpow_iff hc.aestronglyMeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top).mp
  have hi := integrable_japaneseDecay (d := d) (a * p) ha
  convert hi using 1
  funext k
  rw [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (japaneseDecay_nonneg a k)]
  dsimp only [japaneseDecay]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

end WaveTurbulence.WKEL2
