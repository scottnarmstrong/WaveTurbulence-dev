/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootEnvelope
public import WaveTurbulence.Foundations.Incoh.ReplacementMass
public import WaveTurbulence.Foundations.Incoh.ProductMass

/-!
# The mass of the literal root-link envelope

TARGET (incohproof18). Product-box domination retains every non-root
link mass and replaces only the at most two root links by their trivial bounds.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

private def envelopeComplexFactor {d n : ℕ} (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (i : Fin n) (t : Fin 2 → ℝ) : ℂ :=
  if i ∈ R.rootLinks then (((5 * L) ^ (2 * d) : ℝ) : ℂ) else linkTimeFactor L γ δ (Q i) t

private theorem enorm_envelopeComplexFactor {d n : ℕ} (R : RootCoordinates n) {L : ℝ}
    (hL : 1 ≤ L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (i : Fin n) (t : Fin 2 → ℝ) :
    ‖envelopeComplexFactor R L γ δ Q i t‖ₑ = R.envelopeFactor L γ δ Q i t := by
  by_cases hi : i ∈ R.rootLinks
  · simp only [envelopeComplexFactor, RootCoordinates.envelopeFactor, hi, ite_true]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · simp only [envelopeComplexFactor, RootCoordinates.envelopeFactor, hi, ite_false]

/-- Each literal link box has volume one. -/
theorem volume_linkBox {d : ℕ} (Q : LayerLink d) : volume (linkBox Q) = 1 := by
  simp only [linkBox, Real.volume_Icc_pi, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_sub_cancel_left, ENNReal.ofReal_one, mul_one]

/-- The root envelope has only the selected trivial masses, with all other link masses unchanged. -/
theorem RootCoordinates.lintegral_envelope_le_replacedMass {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (Q : Fin n → LayerLink d) :
    (∫⁻ t, R.envelope L γ δ Q t) ≤ ∏ i, replacedLinkMass L γ δ Q R.rootLinks i := by
  have hLp := zero_lt_one.trans_le hL
  let f := envelopeComplexFactor R L γ δ Q
  have hf (i : Fin n) : IntegrableOn (f i) (linkBox (Q i)) := by
    change IntegrableOn (fun t : Fin 2 → ℝ => if i ∈ R.rootLinks then
      (((5 * L) ^ (2 * d) : ℝ) : ℂ) else linkTimeFactor L γ δ (Q i) t) (linkBox (Q i))
    by_cases hi : i ∈ R.rootLinks
    · simp only [hi, ite_true]
      exact continuous_const.integrableOn_Icc
    · simpa only [hi, ite_false] using integrableOn_linkTimeFactor hLp γ δ (Q i)
  have heq (t : Fin n → Fin 2 → ℝ) :
      R.envelope L γ δ Q t = (univ.pi (fun i => linkBox (Q i))).indicator (fun t => ‖∏ i, f i (t i)‖ₑ) t := by
    unfold RootCoordinates.envelope
    by_cases ht : t ∈ univ.pi (fun i => linkBox (Q i))
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
      apply Finset.prod_congr rfl
      intro i _
      exact (enorm_envelopeComplexFactor R hL γ δ Q i (t i)).symm.trans (ofReal_norm _).symm
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  simp_rw [heq]
  have hbox : MeasurableSet (univ.pi (fun i => linkBox (Q i))) :=
    MeasurableSet.univ_pi fun i => (show MeasurableSet (linkBox (Q i)) from measurableSet_Icc)
  rw [lintegral_indicator hbox]
  apply (lintegral_pi_product_enorm_le (μ := fun _ => volume) (Subset.rfl) hf).trans_eq
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ R.rootLinks
  · simp only [f, envelopeComplexFactor, replacedLinkMass, hi, ite_true]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      lintegral_const, Measure.restrict_apply_univ, volume_linkBox, mul_one]
  · simp only [f, envelopeComplexFactor, replacedLinkMass, hi, ite_false]
    rw [layerLinkMass_eq_ofReal_integral hLp γ δ (Q i)]
    simp_rw [← ofReal_norm]
    exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_linkTimeFactor hLp γ δ (Q i)).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)).symm

end WaveTurbulence.Incoh
