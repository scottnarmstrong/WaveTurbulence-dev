/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurable dependence of literal ordered time integrals

Hard time-order constraints require measurability, not differentiability.
Both endpoints may depend measurably on arbitrary external parameters.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Measurable integrands and endpoints give a measurable oriented interval integral. -/
theorem stronglyMeasurable_intervalIntegral {Z : Type*} [MeasurableSpace Z]
    {F : Z × ℝ → ℂ} (hF : StronglyMeasurable F) {a b : Z → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun z => ∫ u in a z..b z, F (z, u)) := by
  have hs (c d : Z → ℝ) (hc : Measurable c) (hd : Measurable d) :
      MeasurableSet {p : Z × ℝ | c p.1 < p.2 ∧ p.2 ≤ d p.1} :=
    (measurableSet_lt (hc.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hd.comp measurable_fst))
  have hi (c d : Z → ℝ) (hc : Measurable c) (hd : Measurable d) :
      StronglyMeasurable (fun z => ∫ u in Ioc (c z) (d z), F (z, u)) := by
    have h := (hF.indicator (hs c d hc hd)).integral_prod_right' (ν := (volume : Measure ℝ))
    convert h using 1
    funext z
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => rfl)
  exact (hi a b ha hb).sub (hi b a hb ha)

/-- Ordered integration preserves measurable dependence, including hard interval fibers. -/
theorem stronglyMeasurable_orderedIntegral (n : ℕ) :
    ∀ {Z : Type*} [MeasurableSpace Z] {F : Z × (Fin n → ℝ) → ℂ}
      {a b : Z → ℝ}, StronglyMeasurable F → Measurable a → Measurable b →
      StronglyMeasurable (fun z => Fourier.orderedIntegral n (fun v => F (z, v)) (b z) (a z)) := by
  induction n with
  | zero =>
    intro Z _ F a b hF _ _
    exact hF.comp_measurable (measurable_id.prodMk measurable_const)
  | succ n ih =>
    intro Z _ F a b hF ha hb
    change StronglyMeasurable (fun z => ∫ u in a z..b z,
      Fourier.orderedIntegral n (fun v => F (z, Fin.cons u v)) u (a z))
    apply stronglyMeasurable_intervalIntegral (F := fun p : Z × ℝ =>
      Fourier.orderedIntegral n (fun v => F (p.1, Fin.cons p.2 v)) p.2 (a p.1))
      (a := a) (b := b) ?_ ha hb
    apply ih (F := fun p : (Z × ℝ) × (Fin n → ℝ) => F (p.1.1, Fin.cons p.1.2 p.2))
      (a := fun p : Z × ℝ => a p.1) (b := fun p : Z × ℝ => p.2)
    · apply hF.comp_measurable
      apply (measurable_fst.comp measurable_fst).prodMk
      apply Measurable.of_eval
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact measurable_snd.comp measurable_fst
      · simp only [Fin.cons_succ]
        exact (measurable_pi_apply i).comp measurable_snd
    · exact ha.comp measurable_fst
    · exact measurable_snd

end WaveTurbulence.Incoh
