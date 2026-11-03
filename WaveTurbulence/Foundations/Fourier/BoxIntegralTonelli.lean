/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra
import Mathlib.Tactic

/-!
# Tonelli identities for coordinate boxes

The last coordinate may be integrated first. This identifies the lower
and mixed boundary-face integrals with the same full amplitude integral.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

private theorem measurable_fin_cons (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) :=
  (contDiff_fin_cons n).continuous.measurable

private theorem measurable_fin_snoc (n : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) := by
  apply Measurable.of_eval
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]; exact measurable_snd
  · simp only [Fin.snoc_castSucc]; fun_prop

/-- Box integration preserves measurable parameter dependence. -/
theorem measurable_boxIntegral_parameter (n : ℕ) (R : ℝ) :
    ∀ {E : Type*} [MeasurableSpace E] {f : E × (Fin n → ℝ) → ℝ≥0∞},
      Measurable f → Measurable (fun w => boxIntegral n (fun v => f (w, v)) R) := by
  induction n with
  | zero =>
    intro E _ f hf
    exact hf.comp (measurable_id.prodMk measurable_const)
  | succ n ih =>
    intro E _ f hf
    have hg : Measurable (fun p : (E × ℝ) × (Fin n → ℝ) => f (p.1.1, Fin.cons p.1.2 p.2)) :=
      hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_fin_cons n).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hm := ih hg
    exact hm.lintegral_prod_right'

/-- Tonelli moves the last box coordinate outside all earlier coordinates. -/
theorem boxIntegral_snoc (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) :
    boxIntegral (n + 1) f R =
      ∫⁻ s in Set.Icc (-R) R, boxIntegral n (fun v => f (Fin.snoc v s)) R := by
  induction n with
  | zero =>
    change (∫⁻ u in Set.Icc (-R) R, f (Fin.cons u Fin.elim0)) =
      ∫⁻ u in Set.Icc (-R) R, f (Fin.snoc Fin.elim0 u)
    apply lintegral_congr
    intro u
    congr 1
    ext i
    fin_cases i
    rfl
  | succ n ih =>
    change (∫⁻ u in Set.Icc (-R) R, boxIntegral (n + 1) (fun v => f (Fin.cons u v)) R) = _
    have hstep (u : ℝ) := ih (f := fun v => f (Fin.cons u v)) (hf.comp ((measurable_fin_cons (n + 1)).comp
      (measurable_const.prodMk measurable_id)))
    simp_rw [hstep]
    have hm : Measurable (fun p : ℝ × ℝ => boxIntegral n
        (fun v => f (Fin.cons p.1 (Fin.snoc v p.2))) R) := by
      apply measurable_boxIntegral_parameter n R
        (f := fun p : (ℝ × ℝ) × (Fin n → ℝ) => f (Fin.cons p.1.1 (Fin.snoc p.2 p.1.2)))
      exact hf.comp ((measurable_fin_cons (n + 1)).comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_fin_snoc n).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
    rw [lintegral_lintegral_swap (f := fun u s : ℝ => boxIntegral n
      (fun v => f (Fin.cons u (Fin.snoc v s))) R)
      (μ := volume.restrict (Set.Icc (-R) R)) (ν := volume.restrict (Set.Icc (-R) R)) hm.aemeasurable]
    apply lintegral_congr
    intro s
    change (∫⁻ u in Set.Icc (-R) R, boxIntegral n (fun v => f (Fin.cons u (Fin.snoc v s))) R) =
      ∫⁻ u in Set.Icc (-R) R, boxIntegral n (fun v => f (Fin.snoc (Fin.cons u v) s)) R
    apply lintegral_congr
    intro u
    apply congrArg (fun g => boxIntegral n g R)
    funext v
    rw [Fin.cons_snoc_eq_snoc_cons]

end WaveTurbulence.Fourier
