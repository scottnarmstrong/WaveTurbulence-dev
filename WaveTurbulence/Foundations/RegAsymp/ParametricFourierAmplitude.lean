/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FourierAmplitudeSetup

/-! # Joint measurability of the actual amplitude Fourier transform -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT
open scoped FourierTransform

/-- No integrability premise is necessary for parameter measurability of
the Bochner-defined amplitude Fourier transform. -/
theorem stronglyMeasurable_fourierW_parameter {P : Type*} [MeasurableSpace P] {d n : ℕ}
    {W : P → (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hW : StronglyMeasurable (fun p : P × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      W p.1 p.2.1 p.2.2)) :
    StronglyMeasurable (fun p : P × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      fourierW (W p.1) p.2.1 p.2.2) := by
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hp : Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      𝐞 (-(∑ j, (inner ℝ (p.1.1 j) (p.2.1 j) + inner ℝ (p.1.2 j) (p.2.2 j))))) := by
    fun_prop
  have hm : StronglyMeasurable (fun p : (P × ((Fin n → Mom d) × (Fin n → Mom d))) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      𝐞 (-(∑ j, (inner ℝ (p.2.1 j) (p.1.2.1 j) + inner ℝ (p.2.2 j) (p.1.2.2 j)))) •
        W p.1.1 p.2.1 p.2.2) :=
    (hp.stronglyMeasurable.comp_measurable (measurable_snd.prodMk measurable_fst.snd)).smul
      (hW.comp_measurable (measurable_fst.fst.prodMk measurable_snd))
  exact hm.integral_prod_right'

end WaveTurbulence.RegAsymp
