/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.DeltaReading
public import WaveTurbulence.Frozen.Defs.CollisionOp
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The collision operator: well-definedness, decomposition, delta reading

For continuous inputs with `|φᵢ(y)| ≤ C (1 + |y|)^{-N}`, `N > 2d`, `d ≥ 2`:

* every integrand in `collisionOp φ₁ φ₂ φ₃ k` is integrable (`integrable_collisionIntegrand_perp`,
  `integrable_collisionOp_outer`), so no Bochner junk value enters;
* `𝒦 = 𝒦₀ - 𝒦₁ + 𝒦₂ - 𝒦₃` (`collisionOp_eq_sum`), with `𝒦ⱼ` the four terms of TARGET
  (schappend1)–(schappend4) (L2493–L2508) written as in (schappend5) (L2512);
* the **delta reading** (`tendsto_mollified_collisionOp`, `tendsto_mollified_collisionOp_k`):
  `𝒦(φ₁, φ₂, φ₃)(k)` is the limit as `ε → 0⁺` of the mollified integrals with
  `δ(2⟨ℓ₁, ℓ₃⟩)` (resp. `δ(|k₁|² - |k₂|² + |k₃|² - |k|²)`, `k₂ = k₁ + k₃ - k`) replaced by
  `ψ_ε = ε⁻¹ ψ(·/ε)`, for any continuous compactly supported `ψ` with `∫ ψ = 1`
  (GIT20, Kin8.tex L981).
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence

variable {d : ℕ}

/-- The integrand of `collisionOp` (the DRAFT body), as a kernel in `(ℓ₁, x)`. -/
@[expose] noncomputable def collisionIntegrand (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d)
    (ℓ₁ x : Mom d) : ℝ :=
  φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + x) * φ₃ (k + x)
    - φ₁ k * φ₂ (k + ℓ₁ + x) * φ₃ (k + x)
    + φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + x)
    - φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + x) * φ₃ k

theorem collisionOp_eq_deltaInt (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) :
    collisionOp φ₁ φ₂ φ₃ k = deltaInt (collisionIntegrand φ₁ φ₂ φ₃ k) := rfl

/-- The kernels of the four terms `𝒦ⱼ` (TARGET (schappend1)–(schappend4) in the variables of
(schappend5)): `j = 0` gain term, `j = 1, 2, 3` the terms with `φⱼ` evaluated at `k`. -/
@[expose] noncomputable def collisionKernel (j : Fin 4) (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d)
    (ℓ₁ x : Mom d) : ℝ :=
  match j with
  | 0 => φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + x) * φ₃ (k + x)
  | 1 => φ₁ k * φ₂ (k + ℓ₁ + x) * φ₃ (k + x)
  | 2 => φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + x)
  | 3 => φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + x) * φ₃ k

/-- The terms `𝒦ⱼ(φ₁, φ₂, φ₃)(k)`, `j = 0, …, 3`, of TARGET (schappend1)–(schappend4). -/
@[expose] noncomputable def collisionTerm (j : Fin 4) (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) : ℝ :=
  deltaInt (collisionKernel j φ₁ φ₂ φ₃ k)

theorem collisionIntegrand_eq (φ₁ φ₂ φ₃ : Mom d → ℝ) (k ℓ₁ x : Mom d) :
    collisionIntegrand φ₁ φ₂ φ₃ k ℓ₁ x =
      collisionKernel 0 φ₁ φ₂ φ₃ k ℓ₁ x - collisionKernel 1 φ₁ φ₂ φ₃ k ℓ₁ x
        + collisionKernel 2 φ₁ φ₂ φ₃ k ℓ₁ x - collisionKernel 3 φ₁ φ₂ φ₃ k ℓ₁ x := rfl

/-! ### Decay bounds -/

/-- `|φ(y)| ≤ C (1 + |y|)^{-N}` for all `y`. -/
@[expose] def DecayBound (C N : ℝ) (φ : Mom d → ℝ) : Prop :=
  ∀ y, |φ y| ≤ C * (1 + ‖y‖) ^ (-N)

theorem one_add_norm_rpow_neg_le_one {x : Mom d} {N : ℝ} (hN : 0 ≤ N) :
    (1 + ‖x‖) ^ (-N) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)

theorem one_add_norm_rpow_neg_anti {x : Mom d} {N N' : ℝ} (h : N' ≤ N) :
    (1 + ‖x‖) ^ (-N) ≤ (1 + ‖x‖) ^ (-N') :=
  Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (by linarith)

theorem DecayBound.C_nonneg {C N : ℝ} {φ : Mom d → ℝ} (h : DecayBound C N φ) : 0 ≤ C :=
  (mul_nonneg_iff_of_pos_right (by positivity)).mp ((abs_nonneg _).trans (h 0))

theorem DecayBound.abs_le {C N : ℝ} {φ : Mom d → ℝ} (h : DecayBound C N φ) (hN : 0 ≤ N)
    (y : Mom d) : |φ y| ≤ C :=
  (h y).trans (mul_le_of_le_one_right h.C_nonneg (one_add_norm_rpow_neg_le_one hN))

/-- Peetre-type splitting: `(1+|a+ℓ|)^{-N} (1+|a|)^{-N} ≤ (1+|ℓ|)^{-N/2} (1+|a|)^{-N/2}`. -/
theorem one_add_norm_rpow_neg_mul_le (a ℓ : Mom d) {N : ℝ} (hN : 0 ≤ N) :
    (1 + ‖a + ℓ‖) ^ (-N) * (1 + ‖a‖) ^ (-N) ≤
      (1 + ‖ℓ‖) ^ (-(N / 2)) * (1 + ‖a‖) ^ (-(N / 2)) := by
  have h1 : 0 < 1 + ‖a + ℓ‖ := by positivity
  have h2 : 0 < 1 + ‖a‖ := by positivity
  have hℓ : 1 + ‖ℓ‖ ≤ (1 + ‖a + ℓ‖) * (1 + ‖a‖) := by
    have : ‖ℓ‖ ≤ ‖a + ℓ‖ + ‖a‖ := by
      calc ‖ℓ‖ = ‖(a + ℓ) - a‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖a + ℓ‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (a + ℓ), norm_nonneg a]
  have e : (1 + ‖a + ℓ‖) ^ (-N) * (1 + ‖a‖) ^ (-N) =
      ((1 + ‖a + ℓ‖) * (1 + ‖a‖)) ^ (-(N / 2)) *
        ((1 + ‖a + ℓ‖) ^ (-(N / 2)) * (1 + ‖a‖) ^ (-(N / 2))) := by
    rw [Real.mul_rpow h1.le h2.le]
    have hs : -N = -(N / 2) + -(N / 2) := by ring
    rw [hs, Real.rpow_add h1, Real.rpow_add h2]
    ring
  rw [e]
  have hA : ((1 + ‖a + ℓ‖) * (1 + ‖a‖)) ^ (-(N / 2)) ≤ (1 + ‖ℓ‖) ^ (-(N / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hℓ (by linarith)
  have hB : (1 + ‖a + ℓ‖) ^ (-(N / 2)) ≤ 1 :=
    one_add_norm_rpow_neg_le_one (by linarith)
  calc ((1 + ‖a + ℓ‖) * (1 + ‖a‖)) ^ (-(N / 2)) *
        ((1 + ‖a + ℓ‖) ^ (-(N / 2)) * (1 + ‖a‖) ^ (-(N / 2)))
      ≤ (1 + ‖ℓ‖) ^ (-(N / 2)) * (1 * (1 + ‖a‖) ^ (-(N / 2))) := by
        gcongr
    _ = _ := by ring

theorem integrableOn_ball_inv_norm (hd : 2 ≤ d) :
    IntegrableOn (fun x : Mom d => ‖x‖⁻¹) (Metric.ball 0 1) := by
  have hfin : Module.finrank ℝ (Mom d) = d := finrank_euclideanSpace_fin
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by omega) ?_ ?_ ?_
  · rw [hfin]; exact_mod_cast (by omega : 1 < d)
  · refine Eventually.of_forall fun x => ?_
    rw [Real.rpow_neg_one, norm_inv, norm_norm, one_mul]
  · exact (measurable_norm.inv).aestronglyMeasurable

/-- `|ℓ|⁻¹ (1 + |c + ℓ|)^{-M} ≤ 1_{|ℓ| < 1} |ℓ|⁻¹ + (1 + |c + ℓ|)^{-M}` for `M ≥ 0`. -/
theorem inv_norm_mul_one_add_norm_le {M : ℝ} (hM : 0 ≤ M) (c ℓ : Mom d) :
    ‖ℓ‖⁻¹ * (1 + ‖c + ℓ‖) ^ (-M) ≤
      (Metric.ball (0 : Mom d) 1).indicator (fun x => ‖x‖⁻¹) ℓ + (1 + ‖c + ℓ‖) ^ (-M) := by
  have hr0 : 0 ≤ (1 + ‖c + ℓ‖) ^ (-M) := by positivity
  have hr1 : (1 + ‖c + ℓ‖) ^ (-M) ≤ 1 := one_add_norm_rpow_neg_le_one hM
  by_cases hℓ : ℓ ∈ Metric.ball (0 : Mom d) 1
  · rw [indicator_of_mem hℓ]
    have : ‖ℓ‖⁻¹ * (1 + ‖c + ℓ‖) ^ (-M) ≤ ‖ℓ‖⁻¹ :=
      mul_le_of_le_one_right (by positivity) hr1
    linarith
  · rw [indicator_of_notMem hℓ, zero_add]
    have h1 : 1 ≤ ‖ℓ‖ := by simpa using hℓ
    have : ‖ℓ‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc ‖ℓ‖⁻¹ * (1 + ‖c + ℓ‖) ^ (-M) ≤ 1 * (1 + ‖c + ℓ‖) ^ (-M) :=
          mul_le_mul_of_nonneg_right this hr0
      _ = _ := one_mul _

/-- `ℓ ↦ |ℓ|⁻¹ (1 + |c + ℓ|)^{-M}` is integrable on `ℝ^d` for `d ≥ 2`, `M > d`. -/
theorem integrable_inv_norm_mul_one_add_norm (hd : 2 ≤ d) {M : ℝ} (hM : (d : ℝ) < M)
    (c : Mom d) : Integrable (fun ℓ : Mom d => ‖ℓ‖⁻¹ * (1 + ‖c + ℓ‖) ^ (-M)) := by
  have hfin : Module.finrank ℝ (Mom d) = d := finrank_euclideanSpace_fin
  have hfr : (Module.finrank ℝ (Mom d) : ℝ) < M := by rw [hfin]; exact hM
  have hdec := (integrable_one_add_norm (E := Mom d) (μ := volume) hfr).comp_add_left c
  have hdom : Integrable (fun ℓ : Mom d =>
      (Metric.ball (0 : Mom d) 1).indicator (fun x => ‖x‖⁻¹) ℓ + (1 + ‖c + ℓ‖) ^ (-M)) :=
    ((integrableOn_ball_inv_norm hd).integrable_indicator measurableSet_ball).add hdec
  refine hdom.mono' ?_ (Eventually.of_forall fun ℓ => ?_)
  · exact (measurable_norm.inv.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (by positivity))]
    exact inv_norm_mul_one_add_norm_le (le_trans (Nat.cast_nonneg d) hM.le) c ℓ

/-! ### Each kernel is a `DeltaKernel` -/

section Kernels

variable {φ₁ φ₂ φ₃ : Mom d → ℝ} {C N : ℝ}

/-- Standing hypotheses on the inputs: continuous with `|φᵢ| ≤ C (1 + |y|)^{-N}`, `N > 2d`. -/
structure CollisionInputs (φ₁ φ₂ φ₃ : Mom d → ℝ) (C N : ℝ) : Prop where
  cont₁ : Continuous φ₁
  cont₂ : Continuous φ₂
  cont₃ : Continuous φ₃
  decay₁ : DecayBound C N φ₁
  decay₂ : DecayBound C N φ₂
  decay₃ : DecayBound C N φ₃
  two_d_lt : 2 * (d : ℝ) < N

namespace CollisionInputs

theorem N_nonneg (h : CollisionInputs φ₁ φ₂ φ₃ C N) : 0 ≤ N := by
  have := h.two_d_lt
  have : (0 : ℝ) ≤ 2 * d := by positivity
  linarith

theorem dim_lt (h : CollisionInputs φ₁ φ₂ φ₃ C N) : (d : ℝ) < N / 2 := by
  have := h.two_d_lt; linarith

theorem C_nonneg (h : CollisionInputs φ₁ φ₂ φ₃ C N) : 0 ≤ C := h.decay₁.C_nonneg

theorem continuous_kernel (h : CollisionInputs φ₁ φ₂ φ₃ C N) (j : Fin 4) (k : Mom d) :
    Continuous (Function.uncurry (collisionKernel j φ₁ φ₂ φ₃ k)) := by
  have c₁ := h.cont₁; have c₂ := h.cont₂; have c₃ := h.cont₃
  fin_cases j
  · exact (c₁.comp (by fun_prop)).mul (c₂.comp (by fun_prop)) |>.mul (c₃.comp (by fun_prop))
  · exact (continuous_const.mul (c₂.comp (by fun_prop))).mul (c₃.comp (by fun_prop))
  · exact ((c₁.comp (by fun_prop)).mul continuous_const).mul (c₃.comp (by fun_prop))
  · exact ((c₁.comp (by fun_prop)).mul (c₂.comp (by fun_prop))).mul continuous_const

/-- The weight `A` for kernel `j`. -/
@[expose] noncomputable def kernelWeight (C N : ℝ) (k : Mom d) (j : Fin 4) (ℓ : Mom d) : ℝ :=
  match j with
  | 1 => C ^ 3 * (1 + ‖ℓ‖) ^ (-(N / 2))
  | _ => C ^ 3 * (1 + ‖k + ℓ‖) ^ (-(N / 2))

/-- The shift `b` for kernel `j`. -/
@[expose] def kernelShift (k : Mom d) (j : Fin 4) (ℓ : Mom d) : Mom d :=
  match j with
  | 3 => k + ℓ
  | _ => k

theorem abs_mul3_le {x y z C : ℝ} (hx : |x| ≤ C) (hy : |y| ≤ C) (hz : |z| ≤ C) :
    |x * y * z| ≤ C * C * C := by
  rw [abs_mul, abs_mul]
  have h0 : 0 ≤ C := (abs_nonneg _).trans hx
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) h0) hz (abs_nonneg _) (by positivity)

theorem kernel_bound (h : CollisionInputs φ₁ φ₂ φ₃ C N) (j : Fin 4) (k ℓ x : Mom d) :
    |collisionKernel j φ₁ φ₂ φ₃ k ℓ x| ≤
      kernelWeight C N k j ℓ * (1 + ‖kernelShift k j ℓ + x‖) ^ (-(N / 2)) := by
  have hN := h.N_nonneg
  have hC := h.C_nonneg
  have hN2 : N / 2 ≤ N := by linarith
  have b₁ := h.decay₁; have b₂ := h.decay₂; have b₃ := h.decay₃
  have u₁ := h.decay₁.abs_le hN; have u₂ := h.decay₂.abs_le hN; have u₃ := h.decay₃.abs_le hN
  fin_cases j
  · -- `φ₁(k+ℓ) φ₂(k+ℓ+x) φ₃(k+x)`
    show |φ₁ (k + ℓ) * φ₂ (k + ℓ + x) * φ₃ (k + x)| ≤
      C ^ 3 * (1 + ‖k + ℓ‖) ^ (-(N / 2)) * (1 + ‖k + x‖) ^ (-(N / 2))
    rw [abs_mul, abs_mul]
    calc |φ₁ (k + ℓ)| * |φ₂ (k + ℓ + x)| * |φ₃ (k + x)|
        ≤ (C * (1 + ‖k + ℓ‖) ^ (-N)) * C * (C * (1 + ‖k + x‖) ^ (-N)) := by
          gcongr
          · exact b₁ _
          · exact u₂ _
          · exact b₃ _
      _ ≤ (C * (1 + ‖k + ℓ‖) ^ (-(N / 2))) * C * (C * (1 + ‖k + x‖) ^ (-(N / 2))) := by
          gcongr <;> exact le_add_of_nonneg_right (norm_nonneg _)
      _ = _ := by ring
  · -- `φ₁(k) φ₂(k+ℓ+x) φ₃(k+x)`
    show |φ₁ k * φ₂ (k + ℓ + x) * φ₃ (k + x)| ≤
      C ^ 3 * (1 + ‖ℓ‖) ^ (-(N / 2)) * (1 + ‖k + x‖) ^ (-(N / 2))
    rw [abs_mul, abs_mul]
    have hp := one_add_norm_rpow_neg_mul_le (k + x) ℓ hN
    have e : k + x + ℓ = k + ℓ + x := by abel
    rw [e] at hp
    calc |φ₁ k| * |φ₂ (k + ℓ + x)| * |φ₃ (k + x)|
        ≤ C * (C * (1 + ‖k + ℓ + x‖) ^ (-N)) * (C * (1 + ‖k + x‖) ^ (-N)) := by
          gcongr
          · exact u₁ _
          · exact b₂ _
          · exact b₃ _
      _ = C ^ 3 * ((1 + ‖k + ℓ + x‖) ^ (-N) * (1 + ‖k + x‖) ^ (-N)) := by ring
      _ ≤ C ^ 3 * ((1 + ‖ℓ‖) ^ (-(N / 2)) * (1 + ‖k + x‖) ^ (-(N / 2))) := by gcongr
      _ = _ := by ring
  · -- `φ₁(k+ℓ) φ₂(k) φ₃(k+x)`
    show |φ₁ (k + ℓ) * φ₂ k * φ₃ (k + x)| ≤
      C ^ 3 * (1 + ‖k + ℓ‖) ^ (-(N / 2)) * (1 + ‖k + x‖) ^ (-(N / 2))
    rw [abs_mul, abs_mul]
    calc |φ₁ (k + ℓ)| * |φ₂ k| * |φ₃ (k + x)|
        ≤ (C * (1 + ‖k + ℓ‖) ^ (-N)) * C * (C * (1 + ‖k + x‖) ^ (-N)) := by
          gcongr
          · exact b₁ _
          · exact u₂ _
          · exact b₃ _
      _ ≤ (C * (1 + ‖k + ℓ‖) ^ (-(N / 2))) * C * (C * (1 + ‖k + x‖) ^ (-(N / 2))) := by
          gcongr <;> exact le_add_of_nonneg_right (norm_nonneg _)
      _ = _ := by ring
  · -- `φ₁(k+ℓ) φ₂(k+ℓ+x) φ₃(k)`
    show |φ₁ (k + ℓ) * φ₂ (k + ℓ + x) * φ₃ k| ≤
      C ^ 3 * (1 + ‖k + ℓ‖) ^ (-(N / 2)) * (1 + ‖k + ℓ + x‖) ^ (-(N / 2))
    rw [abs_mul, abs_mul]
    calc |φ₁ (k + ℓ)| * |φ₂ (k + ℓ + x)| * |φ₃ k|
        ≤ (C * (1 + ‖k + ℓ‖) ^ (-N)) * (C * (1 + ‖k + ℓ + x‖) ^ (-N)) * C := by
          gcongr
          · exact b₁ _
          · exact b₂ _
          · exact u₃ _
      _ ≤ (C * (1 + ‖k + ℓ‖) ^ (-(N / 2))) * (C * (1 + ‖k + ℓ + x‖) ^ (-(N / 2))) * C := by
          gcongr <;> exact le_add_of_nonneg_right (norm_nonneg _)
      _ = _ := by ring

theorem integrable_kernelWeight (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d) (j : Fin 4)
    (k : Mom d) : Integrable (fun ℓ : Mom d => ‖ℓ‖⁻¹ * kernelWeight C N k j ℓ) := by
  have hM := h.dim_lt
  fin_cases j
  · simpa [kernelWeight, mul_left_comm] using
      (integrable_inv_norm_mul_one_add_norm hd hM k).const_mul (C ^ 3)
  · simpa [kernelWeight, mul_left_comm] using
      (integrable_inv_norm_mul_one_add_norm hd hM 0).const_mul (C ^ 3)
  · simpa [kernelWeight, mul_left_comm] using
      (integrable_inv_norm_mul_one_add_norm hd hM k).const_mul (C ^ 3)
  · simpa [kernelWeight, mul_left_comm] using
      (integrable_inv_norm_mul_one_add_norm hd hM k).const_mul (C ^ 3)

/-- Each kernel `𝒦ⱼ` is a `DeltaKernel`. -/
theorem deltaKernel (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d) (j : Fin 4) (k : Mom d) :
    DeltaKernel (collisionKernel j φ₁ φ₂ φ₃ k) (kernelWeight C N k j) (kernelShift k j)
      (N / 2) where
  cont := h.continuous_kernel j k
  bound := h.kernel_bound j k
  dim := h.dim_lt
  integrable := h.integrable_kernelWeight hd j k

end CollisionInputs

end Kernels

/-! ### Well-definedness and decomposition -/

section Main

variable {φ₁ φ₂ φ₃ : Mom d → ℝ} {C N : ℝ}

/-- **No junk, inner level.** For `ℓ₁ ≠ 0` the hyperplane integrand of `collisionOp` is
integrable on `ℓ₁^⊥` (and so is each of the four terms). -/
theorem integrable_collisionKernel_perp (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    (j : Fin 4) (k : Mom d) {ℓ₁ : Mom d} (hℓ : ℓ₁ ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ ℓ₁)ᗮ => collisionKernel j φ₁ φ₂ φ₃ k ℓ₁ w) :=
  (h.deltaKernel hd j k).integrable_perp hℓ

theorem integrable_collisionIntegrand_perp (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    (k : Mom d) {ℓ₁ : Mom d} (hℓ : ℓ₁ ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ ℓ₁)ᗮ => collisionIntegrand φ₁ φ₂ φ₃ k ℓ₁ w) := by
  have i := fun j => integrable_collisionKernel_perp h hd j k hℓ
  simp_rw [collisionIntegrand_eq]
  exact (((i 0).sub (i 1)).add (i 2)).sub (i 3)

theorem integral_collisionIntegrand_perp (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    (k : Mom d) {ℓ₁ : Mom d} (hℓ : ℓ₁ ≠ 0) :
    ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionIntegrand φ₁ φ₂ φ₃ k ℓ₁ w =
      (∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 0 φ₁ φ₂ φ₃ k ℓ₁ w)
        - (∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 1 φ₁ φ₂ φ₃ k ℓ₁ w)
        + (∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 2 φ₁ φ₂ φ₃ k ℓ₁ w)
        - (∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 3 φ₁ φ₂ φ₃ k ℓ₁ w) := by
  have i := fun j => integrable_collisionKernel_perp h hd j k hℓ
  simp_rw [collisionIntegrand_eq]
  rw [integral_sub ?_ (i 3), integral_add ?_ (i 2), integral_sub (i 0) (i 1)]
  · exact (i 0).sub (i 1)
  · exact ((i 0).sub (i 1)).add (i 2)

/-- The outer integrand of the term `𝒦ⱼ` is integrable. -/
theorem integrable_collisionTerm_outer (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    (j : Fin 4) (k : Mom d) :
    Integrable (fun ℓ₁ : Mom d =>
      (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel j φ₁ φ₂ φ₃ k ℓ₁ w) :=
  (h.deltaKernel hd j k).integrable_outer (by omega)

/-- **No junk, outer level.** The outer integrand of `collisionOp` is integrable on `ℝ^d`. -/
theorem integrable_collisionOp_outer (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    (k : Mom d) :
    Integrable (fun ℓ₁ : Mom d =>
      (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionIntegrand φ₁ φ₂ φ₃ k ℓ₁ w) := by
  have i := fun j => integrable_collisionTerm_outer h hd j k
  refine ((((i 0).sub (i 1)).add (i 2)).sub (i 3)).congr ?_
  filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with ℓ hℓ
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [integral_collisionIntegrand_perp h hd k hℓ]
  ring

/-- **Decomposition** `𝒦 = 𝒦₀ - 𝒦₁ + 𝒦₂ - 𝒦₃` (TARGET L2491). -/
theorem collisionOp_eq_sum (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d) (k : Mom d) :
    collisionOp φ₁ φ₂ φ₃ k =
      collisionTerm 0 φ₁ φ₂ φ₃ k - collisionTerm 1 φ₁ φ₂ φ₃ k
        + collisionTerm 2 φ₁ φ₂ φ₃ k - collisionTerm 3 φ₁ φ₂ φ₃ k := by
  have i := fun j => integrable_collisionTerm_outer h hd j k
  have hcongr : collisionOp φ₁ φ₂ φ₃ k = ∫ ℓ₁ : Mom d,
      ((2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 0 φ₁ φ₂ φ₃ k ℓ₁ w)
      - ((2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 1 φ₁ φ₂ φ₃ k ℓ₁ w)
      + ((2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 2 φ₁ φ₂ φ₃ k ℓ₁ w)
      - ((2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, collisionKernel 3 φ₁ φ₂ φ₃ k ℓ₁ w) := by
    rw [collisionOp_eq_deltaInt, deltaInt]
    refine integral_congr_ae ?_
    filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with ℓ hℓ
    rw [integral_collisionIntegrand_perp h hd k hℓ]
    ring
  rw [hcongr, integral_sub ?_ (i 3), integral_add ?_ (i 2), integral_sub (i 0) (i 1)]
  · rfl
  · exact (i 0).sub (i 1)
  · exact ((i 0).sub (i 1)).add (i 2)

end Main

end WaveTurbulence
