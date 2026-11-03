/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedIntegral
public import WaveTurbulence.Foundations.Fourier.LeibnizInterval
import Mathlib.Tactic

/-!
# Differentiating the amplitude of an ordered integral

With endpoints held fixed, parameter derivatives pass through each
ordered integration. Together with translation covariance this differentiates
simultaneous time translations without differentiating difference phases.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The first-variable directional derivative of a smooth product-domain function. -/
theorem hasDerivAt_parameter_slice {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : ℝ × P → ℂ} (hG : ContDiff ℝ ∞ G) (w : ℝ) (v : P) :
    HasDerivAt (fun z => G (z, v)) (fderiv ℝ G (w, v) (1, 0)) w :=
  (hG.differentiable (by simp) (w, v)).hasFDerivAt.comp_hasDerivAt w
    ((hasDerivAt_id w).prodMk (hasDerivAt_const w v))

/-- Fixed-endpoint ordered integration commutes with an amplitude parameter derivative. -/
theorem hasDerivAt_orderedIntegral_parameter (n : ℕ) :
    ∀ {G : ℝ × (Fin n → ℝ) → ℂ}, ContDiff ℝ ∞ G → ∀ w t s : ℝ,
      HasDerivAt (fun z => orderedIntegral n (fun v => G (z, v)) t s)
        (orderedIntegral n (fun v => fderiv ℝ G (w, v) (1, 0)) t s) w := by
  induction n with
  | zero =>
    intro G hG w t s
    exact hasDerivAt_parameter_slice hG w Fin.elim0
  | succ n ih =>
    intro G hG w t s
    let H : ℝ × ℝ → ℂ := fun p =>
      orderedIntegral n (fun v => G (p.1, Fin.cons p.2 v)) p.2 s
    have hH : ContDiff ℝ ∞ H := by
      apply contDiff_orderedIntegral n
        (F := fun p : (ℝ × ℝ) × (Fin n → ℝ) => G (p.1.1, Fin.cons p.1.2 p.2))
        (a := fun _ => s) (b := fun p : ℝ × ℝ => p.2)
      · apply hG.comp
        apply (contDiff_fst.comp contDiff_fst).prodMk
        apply contDiff_pi.mpr
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact contDiff_snd.comp contDiff_fst
        · simp only [Fin.cons_succ]; fun_prop
      · exact contDiff_const
      · exact contDiff_snd
    have h := hasDerivAt_fixed_interval hH w s t
    change HasDerivAt (fun z => orderedIntegral (n + 1) (fun v => G (z, v)) t s)
      (∫ u in s..t, fderiv ℝ H (w, u) (1, 0)) w at h
    convert h using 1
    change (∫ u in s..t, orderedIntegral n
      (fun v => fderiv ℝ G (w, Fin.cons u v) (1, 0)) u s) = _
    apply intervalIntegral.integral_congr
    intro u _
    let Gu : ℝ × (Fin n → ℝ) → ℂ := fun p => G (p.1, Fin.cons u p.2)
    have hGu : ContDiff ℝ ∞ Gu := by
      apply hG.comp
      apply contDiff_fst.prodMk
      apply contDiff_pi.mpr
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact contDiff_const
      · simp only [Fin.cons_succ]; fun_prop
    have hval : (fun v => fderiv ℝ Gu (w, v) (1, 0)) =
        (fun v => fderiv ℝ G (w, Fin.cons u v) (1, 0)) := by
      funext v
      exact (hasDerivAt_parameter_slice hGu w v).unique
        (hasDerivAt_parameter_slice hG w (Fin.cons u v))
    have hinner := ih hGu w u s
    rw [hval] at hinner
    exact hinner.unique (hasDerivAt_parameter_slice hH w u)

end WaveTurbulence.Fourier
