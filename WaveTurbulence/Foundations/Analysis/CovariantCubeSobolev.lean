/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CubeSobolev
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# The elementary inequality with imaginary shifts

The shifted version of DH21 (10.5) used at TARGET L2004 follows by a
unimodular change of phase. A coefficient `c` with zero real part represents
`π i 𝔏`. Constants do not depend on these coefficients.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

/-- The unit-interval elementary inequality with an arbitrary imaginary
constant shift of the derivative. -/
theorem enorm_le_interval_covariant_sobolev {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    {c : ℂ} (hc : c.re = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖f t‖ₑ ≤ (∫⁻ s in Icc (0 : ℝ) 1, ‖f s‖ₑ) +
      ∫⁻ s in Icc (0 : ℝ) 1, ‖deriv f s - c * f s‖ₑ := by
  let g : ℝ → ℂ := fun s => Complex.exp (-c * (s : ℂ)) * f s
  have hlin : ContDiff ℝ 1 (fun s : ℝ => -c * (s : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have hg : ContDiff ℝ 1 g := hlin.cexp.mul hf
  have hn (s : ℝ) : ‖Complex.exp (-c * (s : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, hc, neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]
  have hgn (s : ℝ) : ‖g s‖ₑ = ‖f s‖ₑ := by
    simp only [g, ← ofReal_norm, norm_mul, hn, one_mul]
  have hd (s : ℝ) : deriv g s =
      Complex.exp (-c * (s : ℂ)) * (deriv f s - c * f s) := by
    have hl : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c) s := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
        (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-c)
    have hh := hl.cexp.mul ((hf.differentiable (by norm_num)) s).hasDerivAt
    have hh' : HasDerivAt g
        (Complex.exp (-c * (s : ℂ)) * -c * f s +
          Complex.exp (-c * (s : ℂ)) * deriv f s) s := by
      convert hh using 1
    rw [hh'.deriv]
    ring
  have hdn (s : ℝ) : ‖deriv g s‖ₑ = ‖deriv f s - c * f s‖ₑ := by
    rw [hd, enorm_mul, ← ofReal_norm, hn, ENNReal.ofReal_one, one_mul]
  simpa only [hgn, hdn] using enorm_le_interval_sobolev_L1 hg ht

/-- The iterated sum of the `L¹` norms of mixed covariant derivatives
`∏_{i∈A} (∂ᵢ-cᵢ)f`. Every coordinate occurs at most once. -/
@[expose] noncomputable def cubeCovariantSobolevL1 : (n : ℕ) →
    (Fin n → ℂ) → ((Fin n → ℝ) → ℂ) → ℝ≥0∞
  | 0, _, f => ‖f (fun i => Fin.elim0 i)‖ₑ
  | n + 1, c, f =>
      (∫⁻ t in Icc (0 : ℝ) 1,
        cubeCovariantSobolevL1 n (Fin.tail c) (fun x => f (Fin.cons t x))) +
      ∫⁻ t in Icc (0 : ℝ) 1, cubeCovariantSobolevL1 n (Fin.tail c)
        (fun x => deriv (fun s => f (Fin.cons s x)) t - c 0 * f (Fin.cons t x))

/-- Shifted DH21 (10.5), in iterated-integral form, as used at TARGET L2004.
Take `cᵢ = π i 𝔏ᵢ`. The constant is one and is uniform in all shifts. -/
theorem enorm_le_cubeCovariantSobolevL1 : ∀ (n : ℕ) {f : (Fin n → ℝ) → ℂ},
    ContDiff ℝ ∞ f → ∀ (c : Fin n → ℂ), (∀ i, (c i).re = 0) →
      ∀ x, (∀ i, x i ∈ Icc (0 : ℝ) 1) → ‖f x‖ₑ ≤ cubeCovariantSobolevL1 n c f := by
  intro n
  induction n with
  | zero =>
      intro f _ _ _ x _
      exact le_of_eq (congrArg (fun y => ‖f y‖ₑ) (Subsingleton.elim _ _))
  | succ n ih =>
      intro f hf c hc x hx
      have hs := enorm_le_interval_covariant_sobolev
        ((hf.comp (contDiff_cons_curve (Fin.tail x))).of_le (by simp)) (hc 0) (hx 0)
      simp only [Function.comp_apply, Fin.cons_self_tail] at hs
      refine hs.trans (add_le_add ?_ ?_)
      · apply lintegral_mono
        intro t
        exact ih (hf.comp (contDiff_cons_const t)) (Fin.tail c)
          (fun i => hc i.succ) (Fin.tail x) (fun i => hx i.succ)
      · apply lintegral_mono
        intro t
        exact ih ((contDiff_deriv_cons hf t).sub
          (contDiff_const.mul (hf.comp (contDiff_cons_const t)))) (Fin.tail c)
          (fun i => hc i.succ) (Fin.tail x) (fun i => hx i.succ)

end WaveTurbulence.Analysis
