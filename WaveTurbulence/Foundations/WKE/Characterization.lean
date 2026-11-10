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

end IsMollifier

section Main

variable {φ₁ φ₂ φ₃ : Mom d → ℝ} {C N : ℝ}

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

end WaveTurbulence
