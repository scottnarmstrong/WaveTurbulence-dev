/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RectangleMeasurable
public import WaveTurbulence.Foundations.Incoh.PhaseMeasurable
public import WaveTurbulence.Foundations.Incoh.UniversalRectanglePhase

/-!
# Joint measurability of rectangular phase kernels

This verifies the kernel measurability used in the internal-clock mixture
rather than adding it as an estimate field to the tree carrier.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Literal rectangular ordered phase kernels depend measurably on all their parameters. -/
theorem stronglyMeasurable_rectangleOrderedKernel {P : Type*} [MeasurableSpace P]
    {χ : ℝ → ℝ} (hχ : Measurable χ) {m : ℕ} (i j : Fin m)
    {phase : P → Fin m → ℝ} (hp : Measurable phase)
    {a b : P → Fin 2 → ℝ} (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun z : (Fin 2 → ℝ) × P =>
      Fourier.weightedOrderedIntegral m χ χ
        (Fourier.balancedCutoffAmplitude χ (phase z.2) (rectangleIndicator (a z.2) (b z.2)) i j) z.1) := by
  have hF : Measurable (fun z : P × (Fin 2 → ℝ) => rectangleIndicator (a z.1) (b z.1) z.2) :=
    measurable_rectangleIndicator_comp (ha.comp measurable_fst) (hb.comp measurable_fst) measurable_snd
  have hA := measurable_balancedCutoffAmplitude hχ hp hF i j
  apply stronglyMeasurable_weightedOrderedIntegral_comp hχ
    (F := fun z : ((Fin 2 → ℝ) × P) × (Fin m → ℝ) =>
      Fourier.balancedCutoffAmplitude χ (phase z.1.2) (rectangleIndicator (a z.1.2) (b z.1.2)) i j z.2)
    ?_ measurable_fst
  exact (hA.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable

@[fun_prop] theorem measurable_rectanglePhaseLower : Measurable rectanglePhaseLower := by
  unfold rectanglePhaseLower
  apply Measurable.of_eval
  intro j
  fin_cases j <;> fun_prop

@[fun_prop] theorem measurable_rectanglePhaseUpper : Measurable rectanglePhaseUpper := by
  unfold rectanglePhaseUpper
  apply Measurable.of_eval
  intro j
  fin_cases j <;> fun_prop

/-- Joint time/parameter measurability of the universal triangular family. -/
theorem stronglyMeasurable_universalRectangleU {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun z : (Fin 2 → ℝ) × Mom 6 => universalRectangleU χ z.1 z.2) := by
  have he : (fun z : (Fin 2 → ℝ) × Mom 6 => universalRectangleU χ z.1 z.2) =
      (fun z => Fourier.weightedOrderedIntegral 2 χ χ
        (Fourier.balancedCutoffAmplitude χ ![z.2 0, -z.2 0]
          (rectangleIndicator (rectanglePhaseLower z.2) (rectanglePhaseUpper z.2)) 0 1) z.1) := by
    funext z
    unfold universalRectangleU
    exact congrFun (Fourier.cutoffU_eq_balanced χ (fun p : Mom 6 => p 0)
      (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) z.2) z.1
  rw [he]
  exact stronglyMeasurable_rectangleOrderedKernel (m := 2) (phase := fun p : Mom 6 => ![p 0, -p 0])
    (a := rectanglePhaseLower) (b := rectanglePhaseUpper) hχ 0 1 (by fun_prop)
    measurable_rectanglePhaseLower measurable_rectanglePhaseUpper

/-- Joint time/parameter measurability of the universal fourfold family. -/
theorem stronglyMeasurable_universalRectangleV {χ : ℝ → ℝ} (hχ : Measurable χ) :
    StronglyMeasurable (fun z : (Fin 2 → ℝ) × Mom 6 => universalRectangleV χ z.1 z.2) := by
  have he : (fun z : (Fin 2 → ℝ) × Mom 6 => universalRectangleV χ z.1 z.2) =
      (fun z => Fourier.weightedOrderedIntegral 4 χ χ
        (Fourier.balancedCutoffAmplitude χ ![z.2 0, -z.2 0, z.2 1, -z.2 1]
          (rectangleIndicator (rectanglePhaseLower z.2) (rectanglePhaseUpper z.2)) 1 2) z.1) := by
    funext z
    unfold universalRectangleV
    exact congrFun (Fourier.cutoffV_eq_balanced χ (fun p : Mom 6 => p 0) (fun p : Mom 6 => p 1)
      (fun t p => rectangleIndicator (rectanglePhaseLower p) (rectanglePhaseUpper p) t) z.2) z.1
  rw [he]
  exact stronglyMeasurable_rectangleOrderedKernel (m := 4) (phase := fun p : Mom 6 => ![p 0, -p 0, p 1, -p 1])
    (a := rectanglePhaseLower) (b := rectanglePhaseUpper) hχ 1 2 (by fun_prop)
    measurable_rectanglePhaseLower measurable_rectanglePhaseUpper

end WaveTurbulence.Incoh
