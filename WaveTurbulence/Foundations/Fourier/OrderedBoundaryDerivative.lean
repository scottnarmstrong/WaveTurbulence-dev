/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedParameterDerivative
import Mathlib.Tactic

/-!
# Lower boundary faces of ordered time integrals

Leibniz differentiation removes the last integration variable. This
complements the upper-face formula and supplies the mixed time derivative
without introducing oscillation-frequency factors.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The lower-endpoint derivative is minus the last boundary face. -/
theorem hasDerivAt_orderedIntegral_lower (n : ℕ) :
    ∀ {F : (Fin (n + 1) → ℝ) → ℂ}, ContDiff ℝ ∞ F → ∀ t s : ℝ,
      HasDerivAt (fun z => orderedIntegral (n + 1) F t z)
        (-orderedIntegral n (fun v => F (Fin.snoc v s)) t s) s := by
  induction n with
  | zero =>
    intro F hF t s
    have hc : Continuous (fun u : ℝ => F (Fin.cons u Fin.elim0)) :=
      (hF.comp ((contDiff_fin_cons 0).comp (contDiff_id.prodMk contDiff_const))).continuous
    have h := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable s t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    have he : (Fin.snoc (Fin.elim0 : Fin 0 → ℝ) s : Fin 1 → ℝ) = Fin.cons s Fin.elim0 := by
      ext i
      fin_cases i
      rfl
    change HasDerivAt (fun z => ∫ u in z..t, F (Fin.cons u Fin.elim0))
      (-F (Fin.snoc Fin.elim0 s)) s
    rw [he]
    exact h
  | succ n ih =>
    intro F hF t s
    let G : ℝ × ℝ → ℂ := fun p =>
      orderedIntegral (n + 1) (fun v => F (Fin.cons p.2 v)) p.2 p.1
    have hG : ContDiff ℝ ∞ G := by
      apply contDiff_orderedIntegral (n + 1)
        (F := fun p : (ℝ × ℝ) × (Fin (n + 1) → ℝ) => F (Fin.cons p.1.2 p.2))
        (a := fun p : ℝ × ℝ => p.1) (b := fun p : ℝ × ℝ => p.2)
      · exact hF.comp ((contDiff_fin_cons (n + 1)).comp
          ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
      · exact contDiff_fst
      · exact contDiff_snd
    have h := hasDerivAt_intervalIntegral hG contDiff_id contDiff_const s
      (b := fun _ => t)
    have heval (u : ℝ) : fderiv ℝ G (s, u) (1, 0) =
        -orderedIntegral n (fun v => F (Fin.cons u (Fin.snoc v s))) u s := by
      have hF' : ContDiff ℝ ∞ (fun v : Fin (n + 1) → ℝ => F (Fin.cons u v)) :=
        hF.comp ((contDiff_fin_cons (n + 1)).comp (contDiff_const.prodMk contDiff_id))
      exact (hasDerivAt_parameter_slice hG s u).unique (ih hF' u s)
    simp only [deriv_const, deriv_id, id_eq, zero_smul, one_smul, add_zero] at h
    have hz : G (s, s) = 0 := orderedIntegral_self n _ s
    rw [hz, sub_zero] at h
    convert h using 1
    · rfl
    · change -orderedIntegral (n + 1) (fun v => F (Fin.snoc v s)) t s =
        ∫ u in s..t, fderiv ℝ G (s, u) (1, 0)
      simp_rw [heval]
      rw [intervalIntegral.integral_neg]
      congr 1
      change (∫ u in s..t, orderedIntegral n
        (fun v => F (Fin.snoc (Fin.cons u v) s)) u s) =
        ∫ u in s..t, orderedIntegral n (fun v => F (Fin.cons u (Fin.snoc v s))) u s
      apply intervalIntegral.integral_congr
      intro u _
      have hf : (fun v : Fin n → ℝ => F (Fin.snoc (Fin.cons u v) s)) =
          (fun v : Fin n → ℝ => F (Fin.cons u (Fin.snoc v s))) := by
        funext v
        rw [Fin.cons_snoc_eq_snoc_cons]
      exact congrArg (fun A => orderedIntegral n A u s) hf

end WaveTurbulence.Fourier
