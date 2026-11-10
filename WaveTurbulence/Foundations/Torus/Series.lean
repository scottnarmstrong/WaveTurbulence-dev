/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Inversion
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Smooth periodic functions from rapidly decaying coefficients

The second identity of TARGET (1.2) (L286) synthesizes a function from coefficients:
`torusSeries L c x = L^{-d/2} ∑ₙ c(n) e^{2πi (n/L)·x}`.

* `contDiff_torusSeries`: for rapidly decaying `c` the series is smooth;
* `isTorusPeriodic_torusSeries`, `continuous_torusSeries`, `hasSum_torusSeries`;
* `torusFourierCoeff_torusSeries`: for absolutely summable `c` the coefficients of the series are
  `c`;
* `torusSeries_torusFourierCoeff`: a smooth periodic function is the series of its coefficients.

Together with `isRapidDecay_torusFourierCoeff` this identifies smooth `L`-periodic functions with
rapidly decaying coefficient families.
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped ContDiff

namespace WaveTurbulence

variable {d : ℕ} {L : ℝ}

/-- The Fourier series `L^{-d/2} ∑ₙ c(n) e^{2πi (n/L)·x}` with coefficients `c`
(TARGET (1.2), second identity). -/
@[expose] def torusSeries (L : ℝ) (c : (Fin d → ℤ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ * ∑' n, c n * torusChar L n x

theorem isTorusPeriodic_torusSeries (hL : L ≠ 0) (c : (Fin d → ℤ) → ℂ) :
    IsTorusPeriodic L (torusSeries L c) := by
  intro j x
  simp only [torusSeries, isTorusPeriodic_torusChar hL _ j x]

theorem continuous_torusSeries {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) :
    Continuous (torusSeries L c) :=
  continuous_const.mul (continuous_tsum (fun n => continuous_const.mul (continuous_torusChar L n))
    hc (fun n x => by simp))

/-- The coefficients of the series `torusSeries L c` are `c`, for absolutely summable `c`. -/
theorem torusFourierCoeff_torusSeries (hL : 0 < L) {c : (Fin d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖) (n : Fin d → ℤ) :
    torusFourierCoeff L (torusSeries L c) n = c n := by
  classical
  have hne : ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.rpow_pos_of_pos hL _).ne'
  rw [show torusSeries L c = fun x => ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
      ∑' m, c m * torusChar L m x from rfl, torusFourierCoeff_const_mul]
  have hint : ∀ m, IntegrableOn (fun x => c m * torusChar L m x)
      (Icc (0 : Fin d → ℝ) (fun _ => L)) := fun m =>
    (continuous_const.mul (continuous_torusChar L m)).integrableOn_Icc
  have hnorm : ∀ m, ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), ‖c m * torusChar L m x‖ =
      L ^ d * ‖c m‖ := by
    intro m
    simp only [norm_mul, norm_torusChar, mul_one, setIntegral_const, smul_eq_mul,
      volume_real_Icc_torus hL.le]
  rw [torusFourierCoeff_tsum hint (by simp_rw [hnorm]; exact hc.mul_left _)]
  simp_rw [torusFourierCoeff_const_mul, torusFourierCoeff_torusChar hL]
  rw [tsum_eq_single n (fun m hm => by simp [hm])]
  simp only [ite_true]
  field_simp

/-! ### Smoothness -/

section Smooth

/-- The real-linear phase `x ↦ 2πi (n/L)·x`, so that `torusChar L n = exp ∘ torusPhase L n`. -/
def torusPhase (L : ℝ) (n : Fin d → ℤ) : (Fin d → ℝ) →L[ℝ] ℂ :=
  (∑ j, (2 * Real.pi * ((n j : ℝ) / L)) • ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin d => ℝ) j).smulRight I

theorem torusPhase_apply (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    torusPhase L n x = ((2 * Real.pi * ∑ j, (n j : ℝ) / L * x j : ℝ) : ℂ) * I := by
  simp only [torusPhase, ContinuousLinearMap.smulRight_apply, FunLike.coe_sum,
    Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Complex.real_smul]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem torusChar_eq_exp_torusPhase (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    torusChar L n x = exp (torusPhase L n x) := by
  rw [torusPhase_apply]
  rfl

theorem norm_torusPhase_le (hL : 0 < L) (n : Fin d → ℤ) :
    ‖torusPhase L n‖ ≤ 2 * Real.pi * d / L * ‖n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [torusPhase_apply, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc 2 * Real.pi * |∑ j, (n j : ℝ) / L * x j|
      ≤ 2 * Real.pi * ∑ j, |(n j : ℝ) / L * x j| := by gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * Real.pi * ∑ _j : Fin d, ‖n‖ / L * ‖x‖ := by
        gcongr with j
        rw [abs_mul, abs_div, abs_of_pos hL, ← Int.norm_eq_abs, ← Real.norm_eq_abs]
        gcongr
        · exact norm_le_pi_norm n j
        · exact norm_le_pi_norm x j
    _ = 2 * Real.pi * d / L * ‖n‖ * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem contDiff_const_mul_torusChar (L : ℝ) (c : ℂ) (n : Fin d → ℤ) :
    ContDiff ℝ ∞ (fun x => c * torusChar L n x) := by
  simp_rw [torusChar_eq_exp_torusPhase]
  exact contDiff_const.mul (torusPhase L n).contDiff.cexp

/-- The `k`-th derivative of `x ↦ c e^{2πi (n/L)·x}` is bounded by `‖c‖ ‖torusPhase L n‖^k`. -/
theorem norm_iteratedFDeriv_const_mul_torusChar_le (L : ℝ) (c : ℂ) (n : Fin d → ℤ) (k : ℕ)
    (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => c * torusChar L n x) x‖ ≤ ‖c‖ * ‖torusPhase L n‖ ^ k := by
  set φ := torusPhase L n
  set B : ℂ →L[ℝ] ((Fin d → ℝ) →L[ℝ] ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight φ
  have hB : ‖B‖ ≤ ‖φ‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
    simp only [B, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
    rw [mul_comm]
  have hderiv : fderiv ℝ (fun x => c * torusChar L n x) = fun y => B (c * torusChar L n y) := by
    funext y
    simp_rw [torusChar_eq_exp_torusPhase]
    rw [((φ.hasFDerivAt.cexp).const_mul c).fderiv]
    ext v
    simp [B, φ, smul_smul]
  induction k generalizing x with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    simp
  | succ k ih =>
    rw [← norm_iteratedFDeriv_fderiv, hderiv]
    calc ‖iteratedFDeriv ℝ k (fun y => B (c * torusChar L n y)) x‖
        = ‖iteratedFDeriv ℝ k (B ∘ fun y => c * torusChar L n y) x‖ := rfl
      _ ≤ ‖B‖ * ‖iteratedFDeriv ℝ k (fun y => c * torusChar L n y) x‖ :=
          B.norm_iteratedFDeriv_comp_left (contDiff_const_mul_torusChar L c n).contDiffAt
            (by exact_mod_cast le_top)
      _ ≤ ‖φ‖ * (‖c‖ * ‖φ‖ ^ k) := by gcongr; exact ih x
      _ = ‖c‖ * ‖φ‖ ^ (k + 1) := by ring

/-- Rapidly decaying coefficients define a smooth function (TARGET (1.2), second identity). -/
theorem contDiff_torusSeries (hL : 0 < L) {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) :
    ContDiff ℝ ∞ (torusSeries L c) := by
  set K := 2 * Real.pi * d / L
  have hK : 0 ≤ K := by positivity
  have h := contDiff_tsum (𝕜 := ℝ) (N := ⊤) (f := fun n x => c n * torusChar L n x)
    (v := fun k n => K ^ k * (‖c n‖ * (1 + ‖n‖) ^ k))
    (fun n => contDiff_const_mul_torusChar L (c n) n)
    (fun k _ => (hc.summable_norm_mul_pow k).mul_left _)
    (fun k n x _ => by
      refine (norm_iteratedFDeriv_const_mul_torusChar_le L (c n) n k x).trans ?_
      calc ‖c n‖ * ‖torusPhase L n‖ ^ k ≤ ‖c n‖ * (K * (1 + ‖n‖)) ^ k := by
            gcongr
            calc ‖torusPhase L n‖ ≤ K * ‖n‖ := norm_torusPhase_le hL n
              _ ≤ K * (1 + ‖n‖) := by gcongr; linarith
        _ = K ^ k * (‖c n‖ * (1 + ‖n‖) ^ k) := by rw [mul_pow]; ring)
  exact contDiff_const.mul h

end Smooth

end WaveTurbulence
