/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.StdComplexGaussian
public import Mathlib.Probability.HasLaw

/-!
# G5: packaging the Gaussian-law hypotheses of Theorem 1.1

SEAL-PLAN §B.4 G5. The frozen theorem provides measurability and equality of
the pushforward measure separately; Mathlib's `HasLaw` packages those facts.
-/

public section

namespace WaveTurbulence.MainGlue
open MeasureTheory ProbabilityTheory

/-- G5: the precise law package consumed by the landed probability lemmas. -/
theorem hasLaw_stdComplexGaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → ℂ} (hg : Measurable g) (hmap : P.map g = stdComplexGaussian) :
    HasLaw g stdComplexGaussian P := ⟨hg.aemeasurable, hmap⟩

end WaveTurbulence.MainGlue
