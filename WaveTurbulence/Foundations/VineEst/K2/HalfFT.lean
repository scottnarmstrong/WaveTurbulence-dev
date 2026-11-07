/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! # W2-KIND2 Lemma A (1): half-line Fourier transforms of smooth compactly supported functions

`hft g μ = ∫_{x>0} g(x) e^{-2πi μ x} dx`.  For `g ∈ C²_c`: `hft g μ = g(0)/(2πiμ) + g'(0)/(2πiμ)² + hft g'' μ / (2πiμ)²` (two integrations by parts),
and `‖hft g μ‖ ≤ ∫|g|`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology Complex
open scoped ContDiff

/-- The character `e^{-2πi μ x}`. -/
noncomputable def ex (μ x : ℝ) : ℂ := Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ))) * (x : ℂ))

theorem norm_ex (μ x : ℝ) : ‖ex μ x‖ = 1 := by
  unfold ex
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem continuous_ex (μ : ℝ) : Continuous (ex μ) := by
  unfold ex; fun_prop

theorem ex_zero (μ : ℝ) : ex μ 0 = 1 := by simp [ex]

theorem hasDerivAt_ex (μ x : ℝ) :
    HasDerivAt (ex μ) (-(2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ)) * ex μ x) x := by
  unfold ex
  have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have h1 := (h0.const_mul (-(2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ)))).cexp
  convert h1 using 1
  ring

/-- The half-line transform. -/
noncomputable def hft (g : ℝ → ℂ) (μ : ℝ) : ℂ := ∫ x in Ioi (0 : ℝ), g x * ex μ x

theorem norm_hft_le (g : ℝ → ℂ) (μ : ℝ) : ‖hft g μ‖ ≤ ∫ x in Ioi (0 : ℝ), ‖g x‖ := by
  unfold hft
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp [norm_ex]

theorem integrableOn_mul_ex {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (μ : ℝ) (s : Set ℝ) :
    IntegrableOn (fun x => g x * ex μ x) s := by
  refine Integrable.integrableOn ?_
  have h : Continuous fun x => g x * ex μ x := hg.mul (continuous_ex μ)
  refine h.integrable_of_hasCompactSupport ?_
  exact hc.mul_right

/-- **One integration by parts.** -/
theorem hft_ibp {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) {μ : ℝ} (hμ : μ ≠ 0) :
    hft g μ = g 0 / (2 * (Real.pi : ℂ) * Complex.I * μ) + hft (deriv g) μ / (2 * (Real.pi : ℂ) * Complex.I * μ) := by
  have hk : (2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
    simp [*, Complex.I_ne_zero]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  set k : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ) with hkdef
  have hg' : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hc' : HasCompactSupport (deriv g) := hc.deriv
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => ex μ y / (-k)) (ex μ x) x := by
    intro x _
    have := (hasDerivAt_ex μ x).div_const (-k)
    convert this using 1
    rw [hkdef]
    field_simp
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (deriv g x) x := fun x _ =>
    ((hg.differentiable one_ne_zero) x).hasDerivAt
  have h1 : IntegrableOn (g * ex μ) (Ioi (0 : ℝ)) := integrableOn_mul_ex hg.continuous hc μ _
  have h2 : IntegrableOn (deriv g * fun y => ex μ y / (-k)) (Ioi (0 : ℝ)) := by
    have this : IntegrableOn (fun x => deriv g x * ex μ x / -k) (Ioi (0 : ℝ)) :=
      (integrableOn_mul_ex hg' hc' μ (Ioi (0 : ℝ))).div_const (-k)
    exact this.congr_fun (fun x _ => by simp [Pi.mul_def, mul_div_assoc]) measurableSet_Ioi
  have h0 : Tendsto (g * fun y => ex μ y / (-k)) (𝓝[>] (0 : ℝ)) (𝓝 (g 0 * (ex μ 0 / (-k)))) := by
    have : Continuous (g * fun y => ex μ y / (-k)) := hg.continuous.mul ((continuous_ex μ).div_const _)
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (g * fun y => ex μ y / (-k)) atTop (𝓝 0) := by
    have : (g * fun y => ex μ y / (-k)) =ᶠ[atTop] fun _ => 0 := by
      obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
      filter_upwards [eventually_gt_atTop (R)] with x hx
      have : g x = 0 := by
        by_contra hne
        have hmem : x ∈ tsupport g := subset_tsupport _ hne
        have := hR hmem
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
        linarith [le_abs_self x]
      simp [this]
    exact tendsto_const_nhds.congr' this.symm
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (u := g) (u' := deriv g) (v := fun y => ex μ y / (-k)) (v' := ex μ)
    hu hv h1 h2 h0 hinf
  have e : ∀ x : ℝ, deriv g x * (ex μ x / -k) = -(deriv g x * ex μ x / k) := fun x => by field_simp
  unfold hft
  rw [key]
  simp only [ex_zero, e, integral_neg, integral_div]
  field_simp
  ring


theorem ex_add (a b x : ℝ) : ex a x * ex b x = ex (a + b) x := by
  unfold ex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ex_neg_arg (a x : ℝ) : ex a (-x) = ex (-a) x := by
  unfold ex
  congr 1
  push_cast
  ring

theorem contDiff_deriv_of_two {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 (deriv g) := by
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) g := by rwa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]
  exact ((contDiff_succ_iff_deriv (n := 1)).1 h2).2.2

/-- Second-order expansion of the half-line transform. -/
theorem hft_expand {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) {μ : ℝ} (hμ : μ ≠ 0) :
    hft g μ = g 0 / (2 * (Real.pi : ℂ) * Complex.I * μ) +
      (deriv g 0 / (2 * (Real.pi : ℂ) * Complex.I * μ) ^ 2 +
        hft (deriv (deriv g)) μ / (2 * (Real.pi : ℂ) * Complex.I * μ) ^ 2) := by
  have h1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv g) := contDiff_deriv_of_two hg
  rw [hft_ibp h1 hc hμ, hft_ibp hd hc.deriv hμ]
  ring

theorem norm_two_pi_I_mul (μ : ℝ) : ‖2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ)‖ = 2 * Real.pi * |μ| := by
  simp [Complex.norm_mul, abs_of_pos Real.pi_pos]

/-- The constant of the second-order remainder. -/
noncomputable def cb2 (g : ℝ → ℂ) : ℝ := ‖deriv g 0‖ + ∫ x, ‖deriv (deriv g) x‖

theorem norm_remainder_le {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) {μ : ℝ} (hμ : μ ≠ 0) :
    ‖deriv g 0 / (2 * (Real.pi : ℂ) * Complex.I * μ) ^ 2 + hft (deriv (deriv g)) μ / (2 * (Real.pi : ℂ) * Complex.I * μ) ^ 2‖ ≤
      cb2 g / (2 * Real.pi * |μ|) ^ 2 := by
  have hd2 : Continuous (deriv (deriv g)) := (contDiff_deriv_of_two hg).continuous_deriv le_rfl
  have hint : Integrable (fun x => ‖deriv (deriv g) x‖) := by
    have : HasCompactSupport (deriv (deriv g)) := hc.deriv.deriv
    exact (hd2.integrable_of_hasCompactSupport this).norm
  have hs2 : ‖(2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ)) ^ 2‖ = (2 * Real.pi * |μ|) ^ 2 := by
    rw [norm_pow, norm_two_pi_I_mul]
  have hpos : 0 < (2 * Real.pi * |μ|) ^ 2 := by
    have := abs_pos.2 hμ; positivity
  calc _ = ‖(deriv g 0 + hft (deriv (deriv g)) μ) / (2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ)) ^ 2‖ := by rw [← add_div]
    _ = ‖deriv g 0 + hft (deriv (deriv g)) μ‖ / (2 * Real.pi * |μ|) ^ 2 := by rw [norm_div, hs2]
    _ ≤ cb2 g / (2 * Real.pi * |μ|) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ hpos.le
        refine (norm_add_le _ _).trans ?_
        unfold cb2
        refine add_le_add le_rfl ((norm_hft_le _ _).trans ?_)
        exact setIntegral_le_integral hint (Eventually.of_forall fun x => norm_nonneg _)

end WaveTurbulence.VineEstS5C.P4.W2.K2
