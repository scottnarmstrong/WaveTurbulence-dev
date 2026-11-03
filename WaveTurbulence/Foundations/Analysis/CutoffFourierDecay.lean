/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffPrimitiveBounds
public import WaveTurbulence.Foundations.Analysis.CauchyConvolution
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Quadratic Fourier decay of cutoff primitives

At bounded frequencies, two derivatives give a uniform quadratic envelope.
The constant below is an actual integral expression in the fixed cutoff.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Analysis

/-- Compact support is preserved by every ordinary derivative. -/
theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ k : ℕ, HasCompactSupport (iteratedDeriv k f) := by
  intro k
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem integrable_norm_mul_one_add_abs {f : ℝ → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun t : ℝ => ‖f t‖ * (|t| + 1)) := by
  have hc : Continuous (fun t : ℝ => ‖f t‖ * (|t| + 1)) := by fun_prop
  have hcs : HasCompactSupport (fun t : ℝ => ‖f t‖ * (|t| + 1)) := by
    convert hs.norm.mul_right (f' := fun t : ℝ => |t| + 1) using 1
  exact hc.integrable_of_hasCompactSupport hcs

/-- The cutoff time-integration Fourier kernel. -/
@[expose] noncomputable def cutoffTimeKernel (χ : ℝ → ℂ) (a t q : ℝ) : ℂ :=
  𝓕 (cutoffPrimitive χ a q) t

/-- Uniform bounded-frequency constant, depending only on the cutoff. -/
@[expose] noncomputable def cutoffSmallFrequencyConstant (χ : ℝ → ℂ) : ℝ :=
  (∫ t : ℝ, ‖χ t‖ * (|t| + 1)) + (4 * Real.pi ^ 2)⁻¹ *
    ((∫ t : ℝ, ‖deriv (deriv χ) t‖ * (|t| + 1)) +
      2 * (∫ t : ℝ, ‖deriv χ t‖) + 2 * Real.pi * (∫ t : ℝ, ‖χ t‖))

theorem cutoffSmallFrequencyConstant_nonneg (χ : ℝ → ℂ) :
    0 ≤ cutoffSmallFrequencyConstant χ := by
  unfold cutoffSmallFrequencyConstant
  positivity

/-- Uniform quadratic decay of the cutoff time kernel for `|q| ≤ 1`. -/
theorem norm_cutoffTimeKernel_le_of_abs_le_one {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) {a q : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hq : |q| ≤ 1) (t : ℝ) :
    ‖cutoffTimeKernel χ a t q‖ ≤ cutoffSmallFrequencyConstant χ * cauchyWeight t := by
  have hχ' := (contDiff_infty_iff_deriv.mp hχ).2
  have hχ'' := (contDiff_infty_iff_deriv.mp hχ').2
  have hi0 := hχ.continuous.integrable_of_hasCompactSupport (μ := volume) hs
  have hi1 := hχ'.continuous.integrable_of_hasCompactSupport (μ := volume) hs.deriv
  have hw0 := integrable_norm_mul_one_add_abs hχ.continuous hs
  have hw2 := integrable_norm_mul_one_add_abs hχ''.continuous hs.deriv.deriv
  have hfc := contDiff_cutoffPrimitive hχ a q
  have hfs := hasCompactSupport_cutoffPrimitive hs a q
  have hfi (k : ℕ) : Integrable (iteratedDeriv k (cutoffPrimitive χ a q)) :=
    (hfc.continuous_iteratedDeriv k (by simp)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv hfs k)
  have h0 : (∫ s : ℝ, ‖cutoffPrimitive χ a q s‖) ≤ ∫ s : ℝ, ‖χ s‖ * (|s| + 1) :=
    integral_mono (by simpa only [iteratedDeriv_zero] using (hfi 0).norm) hw0
      (norm_cutoffPrimitive_le χ ha q)
  have hib : Integrable (fun s : ℝ => ‖deriv (deriv χ) s‖ * (|s| + 1) +
      2 * ‖deriv χ s‖ + 2 * Real.pi * ‖χ s‖) :=
    (hw2.add (hi1.norm.const_mul 2)).add (hi0.norm.const_mul (2 * Real.pi))
  have hdeq : iteratedDeriv 2 (cutoffPrimitive χ a q) =
      deriv (deriv (cutoffPrimitive χ a q)) := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have h2 : (∫ s : ℝ, ‖iteratedDeriv 2 (cutoffPrimitive χ a q) s‖) ≤
      (∫ s : ℝ, ‖deriv (deriv χ) s‖ * (|s| + 1)) + 2 * (∫ s : ℝ, ‖deriv χ s‖) +
        2 * Real.pi * (∫ s : ℝ, ‖χ s‖) := by
    calc
      _ ≤ ∫ s : ℝ, ‖deriv (deriv χ) s‖ * (|s| + 1) +
          2 * ‖deriv χ s‖ + 2 * Real.pi * ‖χ s‖ := by
        apply integral_mono (hfi 2).norm hib
        intro s
        rw [hdeq]
        exact norm_deriv_deriv_cutoffPrimitive_le hχ ha hq s
      _ = _ := by
        rw [integral_add
          (f := fun s : ℝ => ‖deriv (deriv χ) s‖ * (|s| + 1) + 2 * ‖deriv χ s‖)
          (g := fun s : ℝ => 2 * Real.pi * ‖χ s‖)
          (hw2.add (hi1.norm.const_mul 2)) (hi0.norm.const_mul (2 * Real.pi)),
          integral_add (f := fun s : ℝ => ‖deriv (deriv χ) s‖ * (|s| + 1))
            (g := fun s : ℝ => 2 * ‖deriv χ s‖) hw2 (hi1.norm.const_mul 2),
          integral_const_mul, integral_const_mul]
  have hh := Real.one_add_sq_mul_norm_fourier_le (hfc.of_le (by norm_num))
    (fun k _ => hfi k) t
  have hbound : (1 + t ^ 2) * ‖cutoffTimeKernel χ a t q‖ ≤ cutoffSmallFrequencyConstant χ :=
    hh.trans (add_le_add h0 (mul_le_mul_of_nonneg_left h2 (by positivity)))
  rw [cauchyWeight, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr (by
    simpa only [mul_comm] using hbound)

end WaveTurbulence.Analysis
