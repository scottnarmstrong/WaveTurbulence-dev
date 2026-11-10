/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Chi0Gevrey
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-!
# Fourier estimates for the fixed cutoff

The quantitative Gevrey estimate supplies uniform integration-by-parts
bounds at every derivative order. The scalar cutoff is cast to `ℂ` before
taking its Fourier transform, with the phase convention of TARGET L579.
-/

public section

open MeasureTheory Set
open scoped FourierTransform ContDiff

namespace WaveTurbulence.Fourier

/-- The scalar cutoff viewed as a complex-valued function. -/
@[expose] noncomputable def chi0Complex (x : ℝ) : ℂ := chi0 x

@[fun_prop] theorem chi0Complex_contDiff : ContDiff ℝ ∞ chi0Complex := by
  unfold chi0Complex
  exact Complex.ofRealCLM.contDiff.comp chi0_contDiff

private theorem chi0Complex_iteratedDeriv (n : ℕ) :
    iteratedDeriv n chi0Complex = fun x => ((iteratedDeriv n chi0 x : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd := ((chi0_contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n)) x).hasDerivAt
    simpa only [iteratedDeriv_succ] using hd.ofReal_comp.deriv

private theorem compact_iteratedDeriv {f : ℝ → ℂ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

private theorem tsupport_iteratedDeriv {f : ℝ → ℂ} (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

private theorem chi0Complex_tsupport : tsupport chi0Complex ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hh
  have he : chi0Complex x = 0 := by
    unfold chi0Complex
    rw [chi0_eq_zero (by
      by_contra h
      have ha := abs_lt.mp (lt_of_not_ge h)
      exact hh ⟨ha.1.le, ha.2.le⟩), Complex.ofReal_zero]
  exact hx he

/-- All derivatives of the compactly supported smooth cutoff are integrable. -/
theorem chi0Complex_iteratedDeriv_integrable (n : ℕ) :
    Integrable (iteratedDeriv n chi0Complex) := by
  have hc : HasCompactSupport chi0Complex :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (fun x hx => by
      by_contra h
      exact hx (chi0Complex_tsupport (subset_closure h)))
  exact (chi0Complex_contDiff.continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (compact_iteratedDeriv hc n)

/-- A uniform `L¹` estimate for every derivative, including order zero. -/
theorem chi0Complex_integral_norm_iteratedDeriv_le (n : ℕ) :
    (∫ x, ‖iteratedDeriv n chi0Complex x‖) ≤
      2 * Real.exp 4 * (16 + 16 * Real.exp 2) ^ n * (Nat.factorial (2 * n) : ℝ) := by
  have hb (x : ℝ) : ‖iteratedDeriv n chi0Complex x‖ ≤
      Real.exp 4 * (16 + 16 * Real.exp 2) ^ n * (Nat.factorial (2 * n) : ℝ) := by
    rw [chi0Complex_iteratedDeriv]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using chi0_gevreyTwoBound n x
  have hs : Function.support (fun x => ‖iteratedDeriv n chi0Complex x‖) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    apply chi0Complex_tsupport
    apply tsupport_iteratedDeriv n
    apply subset_closure
    simpa only [Function.mem_support, norm_ne_zero_iff] using hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-1 : ℝ) 1)
    (fun x hx => by by_contra h; exact hx (hs h))]
  have h := norm_setIntegral_le_of_norm_le_const_ae
    (μ := (volume : Measure ℝ)) (s := Icc (-1 : ℝ) 1)
    (f := fun x => ‖iteratedDeriv n chi0Complex x‖) (by simp)
    (ae_of_all _ (fun x => (by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hb x)))
  have hn : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, ‖iteratedDeriv n chi0Complex x‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hn] at h
  simpa [Real.volume_Icc, Measure.real, ENNReal.toReal_ofNat, one_add_one_eq_two, mul_assoc, mul_comm, mul_left_comm] using h

/-- Integration by parts at arbitrary order, with the explicit Gevrey
constants from F41. -/
theorem chi0_fourier_moment_le (n : ℕ) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ n * ‖𝓕 chi0Complex ξ‖ ≤
      2 * Real.exp 4 * (16 + 16 * Real.exp 2) ^ n * (Nat.factorial (2 * n) : ℝ) := by
  have he := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) chi0Complex_contDiff
    (fun m _ => chi0Complex_iteratedDeriv_integrable m) (n := n) (by simp)
  have hh := (Real.norm_fourier_le_integral_norm (iteratedDeriv n chi0Complex) ξ).trans
    (chi0Complex_integral_norm_iteratedDeriv_le n)
  rw [he, norm_smul, norm_pow] at hh
  simpa [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_assoc] using hh

end WaveTurbulence.Fourier
