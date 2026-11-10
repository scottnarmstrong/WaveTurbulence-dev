/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CutoffPhaseSum
public import WaveTurbulence.Foundations.Sumint.TensorCharacter

/-!
# Measurability and absolute time integrability of the actual cutoff sum

These bounds justify the localized Fourier recombination. They make no
oscillatory-gain claim and impose no regularity in the momentum output.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The independent input character is continuous in every input frequency. -/
theorem continuous_inputCharacter {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) : Continuous (fun ν => inputCharacter D L ν x) := by
  change Continuous (tensorCharacter (fun v => latticePoint L (x v)))
  exact continuous_tensorCharacter _

/-- The cutoff sum is genuinely integrable on each enlarged input-time box. -/
theorem integrableOn_cutoffPhaseSum_enlargedBox {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ) :
    IntegrableOn (cutoffPhaseSum D L γ δ η p ν r t) (enlargedInputTimeBox D c h) := by
  have hi := ((integrableOn_phase_enlargedBox D L γ δ η hη (fun _ => 0) 0 t c h).norm).const_mul
    ((inputCutoffBox L p).card : ℝ)
  apply hi.mono' ((measurable_cutoffPhaseSum D hL γ δ η p ν r t).aestronglyMeasurable.restrict)
  exact ae_of_all _ (norm_cutoffPhaseSum_le D hL γ δ η p ν r t)

/-- Restricting to the static source inequalities preserves actual input-time integrability. -/
theorem integrableOn_cutoffPhaseSum_localDomain {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ) :
    IntegrableOn (cutoffPhaseSum D L γ δ η p ν r t) (localInputTimeDomain D c h) :=
  (integrableOn_cutoffPhaseSum_enlargedBox D hL γ δ η hη p ν r t c h).mono_set Set.inter_subset_left

end WaveTurbulence.Sumint
