/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.CollisionOp
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Characterization of `collisionOp` by mollifying the energy delta

The DRAFT definition `collisionOp` reads `δ(2⟨ℓ₁, ℓ₃⟩)` as `(2|ℓ₁|)⁻¹` times the hyperplane
measure on `ℓ₁^⊥`. We confirm this reading: for continuous inputs with `(1 + |y|)^{-N}` decay,
`N > 2d`, `d ≥ 2`, and any continuous compactly supported `ψ` with `∫ ψ = 1`,

* `tendsto_mollified_collisionOp`: `𝒦(φ₁,φ₂,φ₃)(k) = lim_{ε→0⁺} ∫∫ [integrand](ℓ₁,ℓ₃)
  ψ_ε(2⟨ℓ₁,ℓ₃⟩) dℓ₃ dℓ₁` (TARGET (schappend5), L2512);
* `tendsto_mollified_collisionOp_k`: the same in the variables of (COL) (TARGET L301–L307),
  `k₂ = k₁ + k₃ - k` and `δ(|k₁|² - |k₂|² + |k₃|² - |k|²)` replaced by `ψ_ε`;
* `collisionInputs_of_schwartz`: Schwartz inputs satisfy the hypotheses for every `N`.

The mollifier convention `ψ_ε = ε⁻¹ ψ(·/ε)`, `∫ ψ = 1` is that of GIT20 (Kin8.tex L981).
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence

variable {d : ℕ}

namespace DeltaKernel

variable {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}

theorem integrable_mollified_right (hK : DeltaKernel F A b M) {ψ : ℝ → ℝ}
    (hψ : IsMollifier ψ) (ε : ℝ) (ℓ : Mom d) :
    Integrable (fun x => F ℓ x * mollifier ψ ε (2 * ⟪ℓ, x⟫_ℝ)) := by
  obtain ⟨C, hC⟩ := hψ.exists_bound_mollifier ε
  refine (hK.integrable_right ℓ).mul_bdd (c := C) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((hψ.continuous_mollifier ε).comp
      (continuous_const.mul (continuous_const.inner continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hC _

theorem integrable_molInner (hK : DeltaKernel F A b M) (hd : 0 < d) {ψ : ℝ → ℝ}
    (hψ : IsMollifier ψ) {ε : ℝ} (hε : 0 < ε) : Integrable (molInner ψ ε F) := by
  refine (hK.integrable.const_mul (2⁻¹ * (∫ y, |ψ y|) * hypConst d M)).mono'
    (hK.stronglyMeasurable_molInner hψ ε).aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero hd] with ℓ hℓ
  rw [Real.norm_eq_abs]
  refine (hK.abs_molInner_le hψ hε hℓ).trans_eq ?_
  rw [mul_inv]; ring

end DeltaKernel

namespace IsMollifier

variable {ψ : ℝ → ℝ}

/-- The reflection `x ↦ ψ(-x)` of a mollifier is a mollifier. -/
theorem comp_neg (hψ : IsMollifier ψ) : IsMollifier (fun x => ψ (-x)) where
  cont := hψ.cont.comp continuous_neg
  compact := hψ.compact.comp_homeomorph (Homeomorph.neg ℝ)
  integral_eq_one := by
    have h := Measure.integral_comp_mul_left (fun x => ψ x) (-1)
    simp only [neg_mul, one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
    rw [h]
    exact hψ.integral_eq_one

end IsMollifier

section Main

variable {φ₁ φ₂ φ₃ : Mom d → ℝ} {C N : ℝ}

/-- **Delta reading of `collisionOp`** (in the variables `ℓ₁, ℓ₃` of TARGET (schappend5)). -/
theorem tendsto_mollified_collisionOp (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) (k : Mom d) :
    Tendsto (fun ε => ∫ ℓ₁ : Mom d, ∫ ℓ₃ : Mom d,
        (φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + ℓ₃) * φ₃ (k + ℓ₃)
          - φ₁ k * φ₂ (k + ℓ₁ + ℓ₃) * φ₃ (k + ℓ₃)
          + φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + ℓ₃)
          - φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + ℓ₃) * φ₃ k) * (ε⁻¹ * ψ (2 * ⟪ℓ₁, ℓ₃⟫_ℝ / ε)))
      (𝓝[>] 0) (𝓝 (collisionOp φ₁ φ₂ φ₃ k)) := by
  have hd0 : 0 < d := by omega
  have hK := fun j => h.deltaKernel hd j k
  have hT : Tendsto (fun ε =>
      (∫ ℓ₁, molInner ψ ε (collisionKernel 0 φ₁ φ₂ φ₃ k) ℓ₁)
        - (∫ ℓ₁, molInner ψ ε (collisionKernel 1 φ₁ φ₂ φ₃ k) ℓ₁)
        + (∫ ℓ₁, molInner ψ ε (collisionKernel 2 φ₁ φ₂ φ₃ k) ℓ₁)
        - (∫ ℓ₁, molInner ψ ε (collisionKernel 3 φ₁ φ₂ φ₃ k) ℓ₁)) (𝓝[>] 0)
      (𝓝 (collisionOp φ₁ φ₂ φ₃ k)) := by
    rw [collisionOp_eq_sum h hd k]
    exact ((((hK 0).tendsto_integral_molInner hd0 hψ).sub
      ((hK 1).tendsto_integral_molInner hd0 hψ)).add
        ((hK 2).tendsto_integral_molInner hd0 hψ)).sub
          ((hK 3).tendsto_integral_molInner hd0 hψ)
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have io := fun j => (hK j).integrable_molInner hd0 hψ hε
  have e1 : ∫ ℓ₁, (molInner ψ ε (collisionKernel 0 φ₁ φ₂ φ₃ k) ℓ₁
      - molInner ψ ε (collisionKernel 1 φ₁ φ₂ φ₃ k) ℓ₁
      + molInner ψ ε (collisionKernel 2 φ₁ φ₂ φ₃ k) ℓ₁
      - molInner ψ ε (collisionKernel 3 φ₁ φ₂ φ₃ k) ℓ₁) =
      (∫ ℓ₁, molInner ψ ε (collisionKernel 0 φ₁ φ₂ φ₃ k) ℓ₁)
        - (∫ ℓ₁, molInner ψ ε (collisionKernel 1 φ₁ φ₂ φ₃ k) ℓ₁)
        + (∫ ℓ₁, molInner ψ ε (collisionKernel 2 φ₁ φ₂ φ₃ k) ℓ₁)
        - (∫ ℓ₁, molInner ψ ε (collisionKernel 3 φ₁ φ₂ φ₃ k) ℓ₁) := by
    rw [integral_sub ?_ (io 3), integral_add ?_ (io 2), integral_sub (io 0) (io 1)]
    · exact (io 0).sub (io 1)
    · exact ((io 0).sub (io 1)).add (io 2)
  rw [← e1]
  refine integral_congr_ae (Eventually.of_forall fun ℓ₁ => ?_)
  have ii := fun j => (hK j).integrable_mollified_right hψ ε ℓ₁
  have e2 : ∫ ℓ₃, (collisionKernel 0 φ₁ φ₂ φ₃ k ℓ₁ ℓ₃ * mollifier ψ ε (2 * ⟪ℓ₁, ℓ₃⟫_ℝ)
      - collisionKernel 1 φ₁ φ₂ φ₃ k ℓ₁ ℓ₃ * mollifier ψ ε (2 * ⟪ℓ₁, ℓ₃⟫_ℝ)
      + collisionKernel 2 φ₁ φ₂ φ₃ k ℓ₁ ℓ₃ * mollifier ψ ε (2 * ⟪ℓ₁, ℓ₃⟫_ℝ)
      - collisionKernel 3 φ₁ φ₂ φ₃ k ℓ₁ ℓ₃ * mollifier ψ ε (2 * ⟪ℓ₁, ℓ₃⟫_ℝ)) =
      molInner ψ ε (collisionKernel 0 φ₁ φ₂ φ₃ k) ℓ₁
        - molInner ψ ε (collisionKernel 1 φ₁ φ₂ φ₃ k) ℓ₁
        + molInner ψ ε (collisionKernel 2 φ₁ φ₂ φ₃ k) ℓ₁
        - molInner ψ ε (collisionKernel 3 φ₁ φ₂ φ₃ k) ℓ₁ := by
    simp only [molInner]
    rw [integral_sub ?_ (ii 3), integral_add ?_ (ii 2), integral_sub (ii 0) (ii 1)]
    · exact (ii 0).sub (ii 1)
    · exact ((ii 0).sub (ii 1)).add (ii 2)
  beta_reduce
  rw [← e2]
  refine integral_congr_ae (Eventually.of_forall fun ℓ₃ => ?_)
  simp only [collisionKernel, mollifier]
  ring

theorem norm_sq_resonance (k ℓ₁ ℓ₃ : Mom d) :
    ‖k + ℓ₁‖ ^ 2 - ‖k + ℓ₁ + (k + ℓ₃) - k‖ ^ 2 + ‖k + ℓ₃‖ ^ 2 - ‖k‖ ^ 2 =
      -(2 * ⟪ℓ₁, ℓ₃⟫_ℝ) := by
  have e : k + ℓ₁ + (k + ℓ₃) - k = (k + ℓ₁) + ℓ₃ := by abel
  rw [e, norm_add_sq_real (k + ℓ₁) ℓ₃, norm_add_sq_real k ℓ₃, inner_add_left]
  ring

/-- **Delta reading of `collisionOp`** in the variables of (COL) (TARGET L301–L307): after
integrating out `δ(k₁ - k₂ + k₃ - k)` (`k₂ = k₁ + k₃ - k`), the energy delta
`δ(|k₁|² - |k₂|² + |k₃|² - |k|²)` is the limit of `ψ_ε`. -/
theorem tendsto_mollified_collisionOp_k (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d)
    {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) (k : Mom d) :
    Tendsto (fun ε => ∫ k₁ : Mom d, ∫ k₃ : Mom d,
        (φ₁ k₁ * φ₂ (k₁ + k₃ - k) * φ₃ k₃
          - φ₁ k * φ₂ (k₁ + k₃ - k) * φ₃ k₃
          + φ₁ k₁ * φ₂ k * φ₃ k₃
          - φ₁ k₁ * φ₂ (k₁ + k₃ - k) * φ₃ k) *
          (ε⁻¹ * ψ ((‖k₁‖ ^ 2 - ‖k₁ + k₃ - k‖ ^ 2 + ‖k₃‖ ^ 2 - ‖k‖ ^ 2) / ε)))
      (𝓝[>] 0) (𝓝 (collisionOp φ₁ φ₂ φ₃ k)) := by
  refine (tendsto_mollified_collisionOp h hd hψ.comp_neg k).congr (fun ε => ?_)
  symm
  rw [← integral_add_left_eq_self _ k]
  refine integral_congr_ae (Eventually.of_forall fun ℓ₁ => ?_)
  simp only
  rw [← integral_add_left_eq_self _ k]
  refine integral_congr_ae (Eventually.of_forall fun ℓ₃ => ?_)
  simp only
  rw [norm_sq_resonance k ℓ₁ ℓ₃, neg_div]
  have e : k + ℓ₁ + (k + ℓ₃) - k = k + ℓ₁ + ℓ₃ := by abel
  rw [e]

end Main

/-! ### Schwartz inputs -/

theorem decayBound_of_schwartz (f : 𝓢(Mom d, ℝ)) (N : ℝ) :
    ∃ C, DecayBound C N (fun y => f y) := by
  set n : ℕ := ⌈N⌉₊
  set S : ℝ := 2 ^ n * (Finset.Iic (n, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  refine ⟨S, fun y => ?_⟩
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n, 0)) le_rfl le_rfl f y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h1 : |f y| ≤ S * ((1 + ‖y‖) ^ n)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith [mul_comm ((1 + ‖y‖) ^ n) |f y|]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y])
      (by linarith [Nat.le_ceil N])
  · exact mul_nonneg (by positivity) (apply_nonneg _ _)

theorem DecayBound.mono_C {C C' N : ℝ} {φ : Mom d → ℝ} (h : DecayBound C N φ) (hC : C ≤ C') :
    DecayBound C' N φ :=
  fun y => (h y).trans (mul_le_mul_of_nonneg_right hC (by positivity))

/-- Schwartz inputs satisfy the standing hypotheses `CollisionInputs` for every `N > 2d`. -/
theorem collisionInputs_of_schwartz (f₁ f₂ f₃ : 𝓢(Mom d, ℝ)) {N : ℝ} (hN : 2 * (d : ℝ) < N) :
    ∃ C, CollisionInputs (fun y => f₁ y) (fun y => f₂ y) (fun y => f₃ y) C N := by
  obtain ⟨C₁, h₁⟩ := decayBound_of_schwartz f₁ N
  obtain ⟨C₂, h₂⟩ := decayBound_of_schwartz f₂ N
  obtain ⟨C₃, h₃⟩ := decayBound_of_schwartz f₃ N
  refine ⟨max C₁ (max C₂ C₃), f₁.continuous, f₂.continuous, f₃.continuous,
    h₁.mono_C (le_max_left _ _), h₂.mono_C ((le_max_left _ _).trans (le_max_right _ _)),
    h₃.mono_C ((le_max_right _ _).trans (le_max_right _ _)), hN⟩

/-- **Delta reading for Schwartz inputs.** -/
theorem tendsto_mollified_collisionOp_schwartz (hd : 2 ≤ d) (f₁ f₂ f₃ : 𝓢(Mom d, ℝ))
    {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) (k : Mom d) :
    Tendsto (fun ε => ∫ k₁ : Mom d, ∫ k₃ : Mom d,
        (f₁ k₁ * f₂ (k₁ + k₃ - k) * f₃ k₃
          - f₁ k * f₂ (k₁ + k₃ - k) * f₃ k₃
          + f₁ k₁ * f₂ k * f₃ k₃
          - f₁ k₁ * f₂ (k₁ + k₃ - k) * f₃ k) *
          (ε⁻¹ * ψ ((‖k₁‖ ^ 2 - ‖k₁ + k₃ - k‖ ^ 2 + ‖k₃‖ ^ 2 - ‖k‖ ^ 2) / ε)))
      (𝓝[>] 0) (𝓝 (collisionOp f₁ f₂ f₃ k)) := by
  obtain ⟨C, hC⟩ := collisionInputs_of_schwartz f₁ f₂ f₃
    (by linarith : 2 * (d : ℝ) < 2 * d + 1)
  exact tendsto_mollified_collisionOp_k hC hd hψ k

end WaveTurbulence
