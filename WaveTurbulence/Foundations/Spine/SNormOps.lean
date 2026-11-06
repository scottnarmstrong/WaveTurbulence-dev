/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormRealPart
public import WaveTurbulence.Foundations.Spine.CoordinateMonomialNorm
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivativeNorm
/-! AMEND6' (design P*): the three elementary norm estimates for the pair-type slopes: sums with a scalar multiple,
multiplication by a coordinate (the root linear form), and one coordinate derivative. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset
open scoped ENNReal

theorem SNorm_clm_bound {d A B : ℕ} (T : ℂ →L[ℝ] ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ z, ‖T z‖ ≤ c * ‖z‖) (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C) :
    SNorm A B (T ∘ f) ≤ ENNReal.ofReal (c * C) := by
  apply SNorm_le_of_momentum_bounds _ (T.contDiff.comp hf)
  intro n hn ρ x
  have he : Fourier.momentumDerivative ρ (T ∘ f) x = T (Fourier.momentumDerivative ρ f x) := by
    unfold Fourier.momentumDerivative
    rw [T.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hn)]
    rfl
  rw [he]
  calc jbr x ^ B * ‖T (Fourier.momentumDerivative ρ f x)‖
      ≤ jbr x ^ B * (c * ‖Fourier.momentumDerivative ρ f x‖) :=
        mul_le_mul_of_nonneg_left (hT _) (pow_nonneg (jbr_pos x).le B)
    _ = c * (jbr x ^ B * ‖Fourier.momentumDerivative ρ f x‖) := by ring
    _ ≤ c * C := mul_le_mul_of_nonneg_left (SNorm_momentum_pointwise f hf C hC h hn ρ x) hc

/-- Real scalar multiples: `‖μ f‖ <= |μ| ‖f‖`. -/
theorem SNormR_smul_le {d A B : ℕ} (μ : ℝ) (f : Mom d → ℝ) (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C)
    (h : SNormR A B f ≤ ENNReal.ofReal C) :
    SNormR A B (fun x => μ * f x) ≤ ENNReal.ofReal (|μ| * C) := by
  let T : ℂ →L[ℝ] ℂ := (μ : ℝ) • ContinuousLinearMap.id ℝ ℂ
  have hc' : ContDiff ℝ A (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have := SNorm_clm_bound (A := A) (B := B) T |μ| (abs_nonneg μ) (fun z => by
    simp only [T, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs]
    exact le_rfl) (fun x => (f x : ℂ)) hc' C hC h
  unfold SNormR
  convert this using 2
  funext x
  simp [T]

/-- Sums with a scalar multiple. -/
theorem SNormR_add_smul_le {d A B : ℕ} (f g : Mom d → ℝ) (μ : ℝ) (hf : ContDiff ℝ A f) (hg : ContDiff ℝ A g)
    (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hf' : SNormR A B f ≤ ENNReal.ofReal Cf)
    (hg' : SNormR A B g ≤ ENNReal.ofReal Cg) :
    SNormR A B (fun x => f x + μ * g x) ≤ ENNReal.ofReal (Cf + |μ| * Cg) := by
  have hg2 := SNormR_smul_le μ g hg Cg hCg hg'
  have hgc : ContDiff ℝ A (fun x => μ * g x) := contDiff_const.mul hg
  have hs := SNorm_finset_sum_bound (A := A) (B := B) (univ : Finset Bool)
    (fun b => if b then (fun x => (f x : ℂ)) else (fun x => ((μ * g x : ℝ) : ℂ)))
    (fun b => if b then Cf else |μ| * Cg)
    (fun b _ => by cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;>
      exact Complex.ofRealCLM.contDiff.comp (by assumption))
    (fun b _ => by cases b <;> simp [hCf, mul_nonneg (abs_nonneg μ) hCg])
    (fun b _ => by cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;> assumption)
  unfold SNormR
  convert hs using 2
  · funext x
    simp [Fintype.sum_bool]
  · simp [Fintype.sum_bool]

/-- Multiplication by `c x_i`, `|c| <= 1` (the root linear form): costs one power of decay. -/
theorem SNormR_coord_mul_le {d A B : ℕ} (hd : 1 ≤ d) (i : Fin d) (c : ℝ) (hc : |c| ≤ 1) (f : Mom d → ℝ)
    (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C) (h : SNormR A (B + 1) f ≤ ENNReal.ofReal C) :
    SNormR A B (fun x => c * x i * f x) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * C) := by
  have hc' : ContDiff ℝ A (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have h1 := SNorm_coordinateWord_mul (A := A) (B := B) hd [i] (fun x => (f x : ℂ)) hc' C hC
    (by rw [List.length_singleton]; exact h)
  simp only [List.length_singleton, pow_one] at h1
  have h2 := SNorm_clm_bound (A := A) (B := B) ((c : ℝ) • ContinuousLinearMap.id ℝ ℂ) |c| (abs_nonneg c)
    (fun z => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs]
      exact le_rfl)
    (fun x => coordinateWord [i] x * (f x : ℂ))
    ((contDiff_coordinateWord [i] A).mul hc') _ (by positivity) h1
  have hfun : (fun x : Mom d => (((c * x i * f x : ℝ)) : ℂ)) =
      ((c : ℝ) • ContinuousLinearMap.id ℝ ℂ) ∘ (fun x => coordinateWord [i] x * (f x : ℂ)) := by
    funext x
    simp [coordinateWord, complexCoordinate]
    ring
  unfold SNormR
  rw [hfun]
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hp : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A * C := by positivity
  calc |c| * ((2 : ℝ) ^ A * (d : ℝ) ^ A * C) ≤ 1 * ((2 : ℝ) ^ A * (d : ℝ) ^ A * C) :=
        mul_le_mul_of_nonneg_right hc hp
    _ = _ := one_mul _

end WaveTurbulence.LGSpine
