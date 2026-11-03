/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BoxIntegralTonelli
import Mathlib.Tactic

/-!
# Output-time integration of the boundary-face box bounds

The upper and lower faces cost one unused endpoint interval. The mixed
face uses both endpoints as amplitude coordinates and costs no extra width.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Integrating the upper-face box marginal costs the unused lower endpoint width. -/
theorem box_upper_face_marginal {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      boxIntegral n (fun v => f (Fin.cons (t 0) v)) R) =
      volume (Icc (-R) R) * boxIntegral (n + 1) f R := by
  have hm : Measurable (fun t : Fin 2 → ℝ => boxIntegral n (fun v => f (Fin.cons (t 0) v)) R) := by
    apply measurable_boxIntegral_parameter n R
      (f := fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => f (Fin.cons (p.1 0) p.2))
    have hp : Measurable (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => (p.1 0, p.2)) :=
      ((measurable_pi_apply (0 : Fin 2)).comp measurable_fst).prodMk measurable_snd
    exact hf.comp (by simpa only [Function.comp_def] using (measurable_fin_cons n).comp hp)
  rw [lintegral_two_coordinates_box hm R]
  change (∫⁻ u in Icc (-R) R, ∫⁻ _s in Icc (-R) R, boxIntegral n (fun v => f (Fin.cons u v)) R) = _
  simp only [lintegral_const, Measure.restrict_apply_univ]
  rw [lintegral_mul_const' _ _ isCompact_Icc.measure_lt_top.ne]
  change boxIntegral (n + 1) f R * volume (Icc (-R) R) = _
  exact mul_comm _ _

/-- Integrating the lower-face marginal costs the unused upper endpoint width. -/
theorem box_lower_face_marginal {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      boxIntegral n (fun v => f (Fin.snoc v (t 1))) R) =
      volume (Icc (-R) R) * boxIntegral (n + 1) f R := by
  have hm : Measurable (fun t : Fin 2 → ℝ => boxIntegral n (fun v => f (Fin.snoc v (t 1))) R) := by
    apply measurable_boxIntegral_parameter n R
      (f := fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => f (Fin.snoc p.2 (p.1 1)))
    exact hf.comp ((measurable_fin_snoc n).comp
      (measurable_snd.prodMk ((measurable_pi_apply (1 : Fin 2)).comp measurable_fst)))
  rw [lintegral_two_coordinates_box hm R]
  change (∫⁻ _u in Icc (-R) R, ∫⁻ s in Icc (-R) R, boxIntegral n (fun v => f (Fin.snoc v s)) R) = _
  rw [lintegral_const, Measure.restrict_apply_univ, ← boxIntegral_snoc n hf R]
  exact mul_comm _ _

/-- Integrating the mixed face recovers the amplitude's full box integral exactly. -/
theorem box_mixed_face_marginal {n : ℕ} {f : (Fin (n + 2) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      boxIntegral n (fun v => f (Fin.cons (t 0) (Fin.snoc v (t 1)))) R) =
      boxIntegral (n + 2) f R := by
  have hm : Measurable (fun t : Fin 2 → ℝ =>
      boxIntegral n (fun v => f (Fin.cons (t 0) (Fin.snoc v (t 1)))) R) := by
    apply measurable_boxIntegral_parameter n R
      (f := fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => f (Fin.cons (p.1 0) (Fin.snoc p.2 (p.1 1))))
    have hs : Measurable (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => (Fin.snoc p.2 (p.1 1) : Fin (n + 1) → ℝ)) :=
      (measurable_fin_snoc n).comp
        (measurable_snd.prodMk ((measurable_pi_apply (1 : Fin 2)).comp measurable_fst))
    have hp : Measurable (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => (p.1 0, (Fin.snoc p.2 (p.1 1) : Fin (n + 1) → ℝ))) :=
      ((measurable_pi_apply (0 : Fin 2)).comp measurable_fst).prodMk hs
    exact hf.comp (by simpa only [Function.comp_def] using (measurable_fin_cons (n + 1)).comp hp)
  rw [lintegral_two_coordinates_box hm R]
  change (∫⁻ u in Icc (-R) R, ∫⁻ s in Icc (-R) R,
    boxIntegral n (fun v => f (Fin.cons u (Fin.snoc v s))) R) = _
  have he (u : ℝ) := boxIntegral_snoc n
    (f := fun v => f (Fin.cons u v))
    (hf.comp ((measurable_fin_cons (n + 1)).comp (measurable_const.prodMk measurable_id))) R
  simp_rw [← he]
  rfl

end WaveTurbulence.Fourier
