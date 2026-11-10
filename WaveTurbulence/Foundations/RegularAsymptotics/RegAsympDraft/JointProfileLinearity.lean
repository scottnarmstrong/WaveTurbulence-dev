/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfileFubini

/-! # Lawful linearity of actual jointly integrable sample profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

/-- Sample-integrated inverse profiles are additive when both literal
joint source densities are integrable. -/
theorem pairedInverseProfile_integral_add {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] {A B : (ℝ × ℝ) × U → ℂ}
    (hA : Integrable A (volume.prod μ)) (hB : Integrable B (volume.prod μ)) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∫ u, A (lam,u)+B (lam,u) ∂μ) t =
      pairedInverseProfile (fun lam => ∫ u, A (lam,u) ∂μ) t +
        pairedInverseProfile (fun lam => ∫ u, B (lam,u) ∂μ) t := by
  have he : (fun lam => ∫ u, A (lam,u)+B (lam,u) ∂μ) =ᵐ[volume]
      (fun lam => (∫ u, A (lam,u) ∂μ)+(∫ u, B (lam,u) ∂μ)) := by
    filter_upwards [hA.prod_right_ae,hB.prod_right_ae] with lam ha hb
    exact integral_add ha hb
  calc
    _ = pairedInverseProfile (fun lam => (∫ u, A (lam,u) ∂μ)+(∫ u, B (lam,u) ∂μ)) t := by
      unfold pairedInverseProfile
      apply integral_congr_ae
      filter_upwards [he] with lam hl
      rw [hl]
    _ = _ := pairedInverseProfile_add hA.integral_prod_left hB.integral_prod_left t

/-- A finite collection of actual jointly integrable sample densities
may be summed before both source integrals. -/
theorem pairedInverseProfile_integral_finsetSum {U I : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (S : Finset I) (A : I → (ℝ × ℝ) × U → ℂ)
    (hi : ∀ i ∈ S, Integrable (A i) (volume.prod μ)) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∫ u, ∑ i ∈ S, A i (lam,u) ∂μ) t =
      ∑ i ∈ S, pairedInverseProfile (fun lam => ∫ u, A i (lam,u) ∂μ) t := by
  classical
  have he : (fun lam => ∫ u, ∑ i ∈ S, A i (lam,u) ∂μ) =ᵐ[volume]
      (fun lam => ∑ i ∈ S, ∫ u, A i (lam,u) ∂μ) := by
    have ha : ∀ᵐ lam, ∀ i ∈ S, Integrable (fun u => A i (lam,u)) μ :=
      (ae_ball_iff S.countable_toSet).mpr (fun i hi' => (hi i hi').prod_right_ae)
    filter_upwards [ha] with lam hl
    exact integral_finsetSum S hl
  calc
    _ = pairedInverseProfile (fun lam => ∑ i ∈ S, ∫ u, A i (lam,u) ∂μ) t := by
      unfold pairedInverseProfile
      apply integral_congr_ae
      filter_upwards [he] with lam hl
      rw [hl]
    _ = _ := pairedInverseProfile_finsetSum S _ (fun i hi' => (hi i hi').integral_prod_left) t

end WaveTurbulence.RegAsymp
