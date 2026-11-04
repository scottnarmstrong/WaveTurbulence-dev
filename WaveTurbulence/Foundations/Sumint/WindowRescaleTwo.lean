/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.WindowRescaleGeneral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Positive affine rescaling of two input times

The normal factor has two quadratic time differences with the third
time held fixed. Rescaling the two independent integrations gives the
exact reciprocal square of the time scale.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- Exact rescaling of the iterated two-time rectangle. -/
theorem integral_Icc_affine_two (f : ℝ × ℝ → ℝ) {c a b l u : ℝ}
    (hc : 0 < c) (hab : a ≤ b) (hlu : l ≤ u) (t : ℝ) :
    (∫ s in Icc a b, ∫ s' in Icc l u, f (c*(s-t),c*(s'-t))) =
      c⁻¹*c⁻¹ * (∫ v in Icc (c*(a-t)) (c*(b-t)),
        ∫ w in Icc (c*(l-t)) (c*(u-t)), f (v,w)) := by
  have he (s : ℝ) := integral_Icc_affine (fun w => f (c*(s-t),w)) hc hlu t
  simp_rw [he]
  rw [integral_const_mul,
    integral_Icc_affine (fun v => ∫ w in Icc (c*(l-t)) (c*(u-t)), f (v,w)) hc hab t]
  ring

/-- An affine two-time rectangle contained in a symmetric square is
bounded by its exact reciprocal-square scale times the square integral. -/
theorem integral_Icc_affine_two_le_square (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ z, 0 ≤ f z) {c a b l u B : ℝ} (hc : 0 < c) (hab : a ≤ b)
    (hlu : l ≤ u) (t : ℝ)
    (ha : -B ≤ c*(a-t)) (hb : c*(b-t) ≤ B)
    (hl : -B ≤ c*(l-t)) (hu : c*(u-t) ≤ B) :
    (∫ s in Icc a b, ∫ s' in Icc l u, f (c*(s-t),c*(s'-t))) ≤
      c⁻¹*c⁻¹ * (∫ z : ℝ × ℝ in {z | |z.1| ≤ B ∧ |z.2| ≤ B}, f z) := by
  rw [integral_Icc_affine_two f hc hab hlu t]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr hc.le) (inv_nonneg.mpr hc.le))
  let R := Icc (c*(a-t)) (c*(b-t)) ×ˢ Icc (c*(l-t)) (c*(u-t))
  have hiR : IntegrableOn f R := hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have he : (∫ v in Icc (c*(a-t)) (c*(b-t)),
      ∫ w in Icc (c*(l-t)) (c*(u-t)), f (v,w)) = ∫ z in R, f z := by
    rw [Measure.volume_eq_prod] at hiR ⊢
    exact (setIntegral_prod f hiR).symm
  rw [he]
  have hW : {z : ℝ × ℝ | |z.1| ≤ B ∧ |z.2| ≤ B} = Icc (-B,-B) (B,B) := by
    ext z
    simp only [mem_ofPred_eq,mem_Icc,Prod.le_def,abs_le]
    tauto
  have hiW : IntegrableOn f {z : ℝ × ℝ | |z.1| ≤ B ∧ |z.2| ≤ B} := by
    rw [hW]
    exact hf.integrableOn_Icc
  apply setIntegral_mono_set hiW (ae_of_all _ hn)
  exact ae_of_all _ (fun z hz => ⟨abs_le.mpr ⟨ha.trans hz.1.1,hz.1.2.trans hb⟩,
    abs_le.mpr ⟨hl.trans hz.2.1,hz.2.2.trans hu⟩⟩)

end WaveTurbulence.Sumint
