/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction
import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Actual joint-L1 Fubini and linearity for paired inverse profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

private theorem stronglyMeasurable_e2_at (t : Fin 2 → ℝ) :
    StronglyMeasurable (fun lam : ℝ × ℝ => e2 lam (t 0) (t 1)) := by
  apply Continuous.stronglyMeasurable
  unfold e2
  fun_prop

/-- Joint absolute integrability justifies exchanging the actual sample
integral and the original paired temporal inverse profile. -/
theorem pairedInverseProfile_integral_swap {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] {A : (ℝ × ℝ) × U → ℂ}
    (hi : Integrable A (volume.prod μ)) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∫ u, A (lam,u) ∂μ) t =
      ∫ u, pairedInverseProfile (fun lam => A (lam,u)) t ∂μ := by
  have he : StronglyMeasurable (fun q : (ℝ × ℝ) × U => e2 q.1 (t 0) (t 1)) :=
    (stronglyMeasurable_e2_at t).comp_measurable
    (g := fun q : (ℝ × ℝ) × U => q.1) measurable_fst
  have hE := hi.mul_bdd (c := 1) he.aestronglyMeasurable
    (ae_of_all _ (fun q => (norm_e2 q.1 (t 0) (t 1)).le))
  simpa only [pairedInverseProfile,integral_mul_const] using
    integral_integral_swap (f := fun (lam : ℝ × ℝ) (u : U) => A (lam,u)*e2 lam (t 0) (t 1)) hE

/-- Actual joint L1 also makes the inverted profiles integrable over
the sample measure, so the later countable cell sum is a genuine integral. -/
theorem integrable_pairedInverseProfile_samples {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] {A : (ℝ × ℝ) × U → ℂ}
    (hi : Integrable A (volume.prod μ)) (t : Fin 2 → ℝ) :
    Integrable (fun u => pairedInverseProfile (fun lam => A (lam,u)) t) μ := by
  have he : StronglyMeasurable (fun q : (ℝ × ℝ) × U => e2 q.1 (t 0) (t 1)) :=
    (stronglyMeasurable_e2_at t).comp_measurable
      (g := fun q : (ℝ × ℝ) × U => q.1) measurable_fst
  have hE := hi.mul_bdd (c := 1) he.aestronglyMeasurable
    (ae_of_all _ (fun q => (norm_e2 q.1 (t 0) (t 1)).le))
  exact hE.integral_prod_right

/-- Complex scalar extraction is unconditional for the actual Bochner inverse profile. -/
theorem pairedInverseProfile_const_mul (c : ℂ) (F : ℝ × ℝ → ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => c*F lam) t = c*pairedInverseProfile F t := by
  unfold pairedInverseProfile
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro lam
  ring

/-- Actual integrable frequency profiles may be added before inversion. -/
theorem pairedInverseProfile_add {F G : ℝ × ℝ → ℂ} (hF : Integrable F) (hG : Integrable G)
    (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => F lam+G lam) t =
      pairedInverseProfile F t+pairedInverseProfile G t := by
  have he : AEStronglyMeasurable (fun lam => e2 lam (t 0) (t 1)) volume :=
    (stronglyMeasurable_e2_at t).aestronglyMeasurable
  have hb := ae_of_all volume (fun lam => (norm_e2 lam (t 0) (t 1)).le)
  simp only [pairedInverseProfile,add_mul]
  exact integral_add (hF.mul_bdd (c := 1) he hb) (hG.mul_bdd (c := 1) he hb)

/-- A finite family of actual integrable profiles may be summed before inversion. -/
theorem pairedInverseProfile_finsetSum {I : Type*} (S : Finset I) (F : I → ℝ × ℝ → ℂ)
    (hF : ∀ i ∈ S, Integrable (F i)) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∑ i ∈ S, F i lam) t =
      ∑ i ∈ S, pairedInverseProfile (F i) t := by
  have he : AEStronglyMeasurable (fun lam => e2 lam (t 0) (t 1)) volume :=
    (stronglyMeasurable_e2_at t).aestronglyMeasurable
  have hb := ae_of_all volume (fun lam => (norm_e2 lam (t 0) (t 1)).le)
  simp only [pairedInverseProfile,Finset.sum_mul]
  exact integral_finsetSum S (fun i hi => (hF i hi).mul_bdd (c := 1) he hb)

end WaveTurbulence.RegAsymp
