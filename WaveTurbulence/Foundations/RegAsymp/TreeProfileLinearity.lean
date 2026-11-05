/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeLeadingProfile
public import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Lawful linearity of the actual original-frequency inverse profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

/-- The source unit phase preserves actual temporal integrability. -/
theorem tree_integrable_mul_e2 {A : (ℝ × ℝ) → ℂ} (hA : Integrable A) (t : Fin 2 → ℝ) :
    Integrable (fun lam => A lam*e2 lam (t 0) (t 1)) := by
  exact hA.mul_bdd (c := 1)
    (show Continuous (fun lam : ℝ × ℝ => e2 lam (t 0) (t 1)) by unfold e2; fun_prop).aestronglyMeasurable
    (ae_of_all _ (fun lam => (norm_e2 lam (t 0) (t 1)).le))

/-- Constant multiplication commutes with the actual inverse profile. -/
theorem tree_pairedInverseProfile_const_mul (c : ℂ) (A : (ℝ × ℝ) → ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => c*A lam) t = c*pairedInverseProfile A t := by
  unfold pairedInverseProfile
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by ring)

/-- Addition uses the actual integrability of both original-frequency densities. -/
theorem tree_pairedInverseProfile_add {A B : (ℝ × ℝ) → ℂ}
    (hA : Integrable A) (hB : Integrable B) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => A lam+B lam) t = pairedInverseProfile A t+pairedInverseProfile B t := by
  unfold pairedInverseProfile
  simp only [add_mul]
  exact integral_add (tree_integrable_mul_e2 hA t) (tree_integrable_mul_e2 hB t)

/-- Subtraction uses the actual integrability of both original-frequency densities. -/
theorem tree_pairedInverseProfile_sub {A B : (ℝ × ℝ) → ℂ}
    (hA : Integrable A) (hB : Integrable B) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => A lam-B lam) t = pairedInverseProfile A t-pairedInverseProfile B t := by
  unfold pairedInverseProfile
  simp only [sub_mul]
  exact integral_sub (tree_integrable_mul_e2 hA t) (tree_integrable_mul_e2 hB t)

/-- Every finite family of actual integrable densities commutes with the inverse profile. -/
theorem tree_pairedInverseProfile_finsetSum {ι : Type*} (S : Finset ι)
    (A : ι → (ℝ × ℝ) → ℂ) (hi : ∀ i ∈ S, Integrable (A i)) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => ∑ i ∈ S, A i lam) t = ∑ i ∈ S, pairedInverseProfile (A i) t := by
  unfold pairedInverseProfile
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum S (fun i hiS => tree_integrable_mul_e2 (hi i hiS) t)

end WaveTurbulence.RegAsymp
