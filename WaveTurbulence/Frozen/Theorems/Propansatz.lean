/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Provider.Propansatz

/-!
# propansatz

Wave B tier B1 (WaveB1-Statements.lean), source: T Prop `propansatz`, L689–L707; WAVE-B v2 §4.1; T L819. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B1.1 `propansatz`** (T Prop `propansatz`, L689–L707; + time parameter F7/F27; + L951).
Under (Π), for all probability data of Wave A there are a solution `a`, events `Fev`, two-point
corrections `R, E` and cumulant remainders `Ẽ` such that `AnsatzAt p` holds for every `0 ≤ p ≤ 𝔇`.
Deviations (WAVE-B v2 §4.1): (D1) `R p` is a real `C^{Λ_p}` function on `ℝ^d` with the `ℝ^d` 𝔖-norm
(regularity from the norm bound for `Λ_p ≠ 0`, `contDiff_of_SNormR_lt_top`; stage-3 R1, option B);
(D2) the cumulant of (ansatz1) is written as the moment; (D3) item (2') (intermediate times) is
new, constant `2`; (D4) uniqueness in the classed solution notion (Q16, C1); (D5) measurability
(`Measurable`, C1) and integrability conjuncts added; (D6) the sums of (3)–(4) are the shared
`truncSum` (equal to the source's untruncated sums: `truncSum_untruncated`); (D7, DESIGN Q5)
symmetric events are preimages of invariant sets of initial data.
Beyond the frozen anchors, `main` needs three unfrozen glue lemmas (stage-3 O8): mass conservation for
smooth NLS solutions (T L819), the almost-sure rapid decay of `initialCoeff` (PROB.smoothData), and the
Gaussian moments of the mass `∑ φin(n/L)|g_n|²`. -/
theorem propansatz : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.propansatz
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
