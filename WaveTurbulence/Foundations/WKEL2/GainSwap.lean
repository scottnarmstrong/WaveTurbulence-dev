/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantReflections

/-!
# Exchanging the outside gain slots in the full pairing
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Swap of the two resonant vectors while the output momentum is fixed. -/
theorem lintegral_gain_swap {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {H : Mom d × (Mom d × Mom d) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ q : Mom d × (Mom d × Mom d), H (q.1, (q.2.2, q.2.1))
      ∂volume.prod (resonantMeasure e)) = ∫⁻ q, H q ∂volume.prod (resonantMeasure e) := by
  let := resonantMeasure_finiteOnCompacts e hd
  have hswap : Measurable (fun q : Mom d × (Mom d × Mom d) => H (q.1, (q.2.2, q.2.1))) :=
    hH.comp (measurable_fst.prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd)))
  rw [lintegral_prod _ hswap.aemeasurable, lintegral_prod _ hH.aemeasurable]
  apply lintegral_congr
  intro k
  have hEmbed : Measurable (fun p : Mom d × Mom d => (k, p)) :=
    measurable_const.prodMk measurable_id
  have hK : Measurable (fun p : Mom d × Mom d => H (k, p)) := hH.comp hEmbed
  exact lintegral_resonantMeasure_swap he hd hK

end WaveTurbulence.WKEL2
