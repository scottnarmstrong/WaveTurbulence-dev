/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.WeightedKernelAgreement
public import WaveTurbulence.Foundations.Sumint.TimeCellAgreement

/-!
# Genuine integrability and finite linearity of the rectangular extension

The fixed-output rectangle is bounded by its scalar exponential. This
justifies finite linearity before recombining the spatial coefficients.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The actual kernel extension is measurable at every output point. -/
theorem measurable_kernelExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ) (hF : Measurable F) :
    Measurable (kernelExtension D hI c h F) := by
  have hm := ((hF.comp measurable_fst).mul (measurable_exit_exponentialBox D hI)).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (localInputTimeDomain D c h))
  exact hm.measurable

/-- Each native input slice of the rectangle is integrable for an integrable coefficient. -/
theorem integrableOn_kernel_slice {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFi : IntegrableOn F (localInputTimeDomain D c h)) (z : Fin 3 → ℝ) :
    IntegrableOn (fun u => F u*exponentialBox (lowerTimeExit D hI u)
      (upperTimeExit D hI u) (u (firstTime D hI)) z) (localInputTimeDomain D c h) := by
  have hp : Measurable (fun u : D.S.TVar → ℝ => (u,z)) := measurable_id.prodMk measurable_const
  have hm := (measurable_exit_exponentialBox D hI).comp hp
  apply hFi.mul_bdd (c := Real.exp (-z 0+z 1+z 2)) hm.aestronglyMeasurable.restrict
  apply ae_of_all
  intro u
  change ‖exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u)
    (u (firstTime D hI)) z‖ ≤ Real.exp (-z 0+z 1+z 2)
  rw [exponentialBox_eq_ite]
  split_ifs
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  · exact (norm_zero : ‖(0:ℂ)‖ = 0).le.trans (Real.exp_nonneg _)

/-- The rectangular extension commutes with actual finite sums of measurable integrable inputs. -/
theorem kernelExtension_finsetSum {ι : Type*} {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (s : Finset ι) (F : ι → (D.S.TVar → ℝ) → ℂ)
    (hFi : ∀ j ∈ s, IntegrableOn (F j) (localInputTimeDomain D c h)) (z : Fin 3 → ℝ) :
    kernelExtension D hI c h (fun u => ∑ j ∈ s, F j u) z =
      ∑ j ∈ s, kernelExtension D hI c h (F j) z := by
  unfold kernelExtension
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum s (fun j hj => integrableOn_kernel_slice D hI c h (F j) (hFi j hj) z)

/-- Scalar linearity of the complete finite time-cell extension. -/
theorem timeCellExtension_const_mul {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h : ℝ) (a : ℂ) (F : (D.S.TVar → ℝ) → ℂ) (z : Fin 3 → ℝ) :
    timeCellExtension D hI N h (fun u => a*F u) z = a*timeCellExtension D hI N h F z := by
  unfold timeCellExtension
  simp_rw [kernelExtension_const_mul,mul_assoc]
  rw [Finset.mul_sum]

end WaveTurbulence.Sumint
