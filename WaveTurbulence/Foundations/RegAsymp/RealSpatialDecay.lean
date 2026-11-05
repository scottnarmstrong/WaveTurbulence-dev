/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay
public import WaveTurbulence.Foundations.WKE.CollisionOp
public import Mathlib.Analysis.Complex.OperatorNorm

/-! # Ordinary real polynomial decay from the actual finite source spatial norm -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh
open scoped ContDiff

variable {d : ℕ}

/-- The source momentum bracket controls the ordinary polynomial weight
with only a fixed dimensional-free factor2 per derivative weight. -/
theorem one_add_norm_le_two_momentumBracket (x : Mom d) :
    1+‖x‖ ≤ 2*Fourier.momentumBracket x := by
  have h1 := one_le_momentumBracket x
  have hn : ‖x‖ ≤ Fourier.momentumBracket x := by
    unfold Fourier.momentumBracket
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
  linarith

/-- Weighted source bounds imply ordinary polynomial decay, without
requiring infinite smoothness or compact support. -/
theorem decayBound_of_momentumBracket {M : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {f : Mom d → ℝ} (hf : ∀ x, |f x| ≤ B/Fourier.momentumBracket x^M) :
    DecayBound ((2:ℝ)^M*B) (M:ℝ) f := by
  intro x
  apply (hf x).trans
  have hp : 0 < Fourier.momentumBracket x^M := pow_pos
    (zero_lt_one.trans_le (one_le_momentumBracket x)) M
  have hq : 0 < (1+‖x‖)^M := pow_pos (by positivity) M
  have hh : (1+‖x‖)^M ≤ (2:ℝ)^M*Fourier.momentumBracket x^M := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) (one_add_norm_le_two_momentumBracket x) M
  rw [Real.rpow_neg (by positivity),Real.rpow_natCast,← div_eq_mul_inv]
  apply (div_le_div_iff₀ hp hq).mpr
  have hm := mul_le_mul_of_nonneg_left hh hB
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hm

/-- Real source inputs inherit their actual finite smoothness from the
landed norm of the complexification. -/
theorem contDiff_real_of_spatialNorm {K M : ℕ} {f : Mom d → ℝ} {B : ℝ}
    (hK : 0 < K) (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B) :
    ContDiff ℝ K f := by
  have hc := (Complex.reCLM.contDiff).comp (contDiff_of_spatialNorm_le hK hf)
  simpa only [Function.comp_def,Complex.reCLM_apply,Complex.ofReal_re] using hc

/-- Finite source smoothness provides actual continuous derivatives and
ordinary polynomial bounds for both the input and its first derivative. -/
theorem realSpatial_firstOrder_decay {K M : ℕ} {f : Mom d → ℝ} {B : ℝ}
    (hK : 0 < K) (hB : 0 ≤ B)
    (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B) :
    Continuous f ∧ Continuous (fderiv ℝ f) ∧
      (∀ x, HasFDerivAt f (fderiv ℝ f x) x) ∧
      DecayBound ((2:ℝ)^M*B) (M:ℝ) f ∧
      DecayBound ((2:ℝ)^M*((d:ℝ)*B)) (M:ℝ) (fun x => ‖fderiv ℝ f x‖) := by
  have hc := contDiff_real_of_spatialNorm hK hf
  have hcc := contDiff_of_spatialNorm_le hK hf
  have hkne : (K:ℕ∞ω) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hdif := hc.differentiable hkne
  have hcdif := hcc.differentiable hkne
  refine ⟨hc.continuous,hc.continuous_fderiv hkne,
    fun x => hdif.differentiableAt.hasFDerivAt,?_,?_⟩
  · apply decayBound_of_momentumBracket hB
    intro x
    have hh := norm_iteratedFDeriv_le_of_spatialNorm hB hf (j := 0) (Nat.zero_le K) x
    simpa only [norm_iteratedFDeriv_zero,pow_zero,one_mul,Complex.norm_real,Real.norm_eq_abs] using hh
  · apply decayBound_of_momentumBracket (mul_nonneg (Nat.cast_nonneg _) hB)
    intro x
    rw [abs_norm]
    have he : fderiv ℝ f x = Complex.reCLM.comp (fderiv ℝ (fun x => (f x:ℂ)) x) := by
      have hh := Complex.reCLM.hasFDerivAt.comp x hcdif.differentiableAt.hasFDerivAt
      have hh' : HasFDerivAt f (Complex.reCLM.comp (fderiv ℝ (fun x => (f x:ℂ)) x)) x := by
        simpa only [Function.comp_def,Complex.reCLM_apply,Complex.ofReal_re] using hh
      exact hh'.fderiv
    rw [he]
    have hh := norm_iteratedFDeriv_le_of_spatialNorm hB hf (j := 1) (by omega) x
    have hnorm := ContinuousLinearMap.opNorm_comp_le Complex.reCLM (fderiv ℝ (fun x => (f x:ℂ)) x)
    rw [Complex.reCLM_norm,one_mul] at hnorm
    apply hnorm.trans
    simpa only [norm_iteratedFDeriv_one,pow_one,mul_div_assoc] using hh

/-- Increasing the constant preserves ordinary polynomial decay. -/
theorem decayBound_mono_const {C D N : ℝ} {f : Mom d → ℝ}
    (h : DecayBound C N f) (hCD : C ≤ D) : DecayBound D N f := by
  intro x
  exact (h x).trans (mul_le_mul_of_nonneg_right hCD (by positivity))

/-- A single explicit finite-input constant bounds both a real function
and its actual first derivative, as required by the binary PV class. -/
theorem realSpatial_common_firstOrder_decay {K M : ℕ} {f : Mom d → ℝ} {B : ℝ}
    (hK : 0 < K) (hB : 0 ≤ B)
    (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B) :
    Continuous f ∧ Continuous (fderiv ℝ f) ∧
      (∀ x, HasFDerivAt f (fderiv ℝ f x) x) ∧
      DecayBound ((2:ℝ)^M*((1+(d:ℝ))*B)) (M:ℝ) f ∧
      DecayBound ((2:ℝ)^M*((1+(d:ℝ))*B)) (M:ℝ) (fun x => ‖fderiv ℝ f x‖) := by
  obtain ⟨hc,hd,hf',hfb,hdb⟩ := realSpatial_firstOrder_decay hK hB hf
  refine ⟨hc,hd,hf',decayBound_mono_const hfb ?_,decayBound_mono_const hdb ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_mul_of_one_le_left hB (le_add_of_nonneg_right (Nat.cast_nonneg d))
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith : (d:ℝ) ≤ 1+(d:ℝ)) hB

end WaveTurbulence.RegAsymp
