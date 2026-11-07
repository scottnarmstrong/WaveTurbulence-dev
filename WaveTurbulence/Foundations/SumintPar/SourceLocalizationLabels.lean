/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.AlternativeLabelFamily
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The actual countable source localization labels

Primary labels are unrestricted integer cells; alternative labels are
exactly the proved finite source family for each primary label.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- The exact primary and admissible alternative cell pairs. -/
@[expose] def SourceLocalizationLabel {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) :=
  Σ a : D.S.VIdx → Fin d → ℤ,
    {b : D.S.VIdx → Fin d → ℤ // b ∈ sourceAlternativeLabels D hD a}

instance {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {N : ℕ}
    (hD : D.Admissible A L γ η N) : Countable (SourceLocalizationLabel D hD) := by
  unfold SourceLocalizationLabel
  infer_instance

instance {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {N : ℕ}
    (hD : D.Admissible A L γ η N) : MeasurableSpace (SourceLocalizationLabel D hD) := ⊤

instance {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {N : ℕ}
    (hD : D.Admissible A L γ η N) : DiscreteMeasurableSpace (SourceLocalizationLabel D hD) := ⟨fun _ => trivial⟩

/-- Nonnegative sums over the literal source label type are the primary sum and finite alternative sums. -/
theorem tsum_sourceLocalizationLabel {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (f : (D.S.VIdx → Fin d → ℤ) → (D.S.VIdx → Fin d → ℤ) → ℝ≥0∞) :
    (∑' j : SourceLocalizationLabel D hD, f j.1 j.2.val) =
      ∑' a, ∑ b ∈ sourceAlternativeLabels D hD a, f a b := by
  classical
  apply (ENNReal.tsum_sigma (fun a (b : {b : D.S.VIdx → Fin d → ℤ // b ∈ sourceAlternativeLabels D hD a}) => f a b.val)).trans
  apply tsum_congr
  intro a
  exact Finset.tsum_subtype' (sourceAlternativeLabels D hD a) (f a)

end WaveTurbulence.SumintPar
