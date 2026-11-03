/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Characterization
public import WaveTurbulence.Foundations.WKE.Trilinear

/-!
# The resonant integral

The two deltas in TARGET (C.5) and DH21 Proposition 7.7 (L1814–L1837) are read
using the hyperplane measure fixed by D6. The kernel takes the three momenta
as separate arguments. `tendsto_mollified_resonantIntegral_k` characterizes this
reading by mollification of the energy delta, including its negative sign.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-- The kernel after eliminating momentum conservation and translating by `k`. -/
@[expose] def resonantKernel (Ψ : Mom d → Mom d → Mom d → ℝ) (k ℓ x : Mom d) : ℝ :=
  Ψ (k + ℓ) (k + ℓ + x) (k + x)

/-- Integration against `δ(k₁-k₂+k₃-k)δ(|k₁|²-|k₂|²+|k₃|²-|k|²)`.
The hyperplane normalization is the one in the frozen `collisionOp`. -/
@[expose] noncomputable def resonantIntegral (Ψ : Mom d → Mom d → Mom d → ℝ)
    (k : Mom d) : ℝ :=
  deltaInt (resonantKernel Ψ k)

theorem resonantIntegral_eq (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) :
    resonantIntegral Ψ k = ∫ ℓ : Mom d, (2 * ‖ℓ‖)⁻¹ *
      ∫ w : ↥(ℝ ∙ ℓ)ᗮ, Ψ (k + ℓ) (k + ℓ + w) (k + w) := rfl

/-- The frozen cubic collision operator is a special case of the resonant integral. -/
theorem collisionOp_eq_resonantIntegral (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) :
    collisionOp φ₁ φ₂ φ₃ k = resonantIntegral (fun k₁ k₂ k₃ =>
      φ₁ k₁ * φ₂ k₂ * φ₃ k₃ - φ₁ k * φ₂ k₂ * φ₃ k₃
        + φ₁ k₁ * φ₂ k * φ₃ k₃ - φ₁ k₁ * φ₂ k₂ * φ₃ k) k := rfl

/-- Each positive collision term is also a resonant integral. -/
theorem collisionTerm_zero_eq_resonantIntegral (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) :
    collisionTerm 0 φ₁ φ₂ φ₃ k =
      resonantIntegral (fun k₁ k₂ k₃ => φ₁ k₁ * φ₂ k₂ * φ₃ k₃) k := rfl

/-- General delta reading in the translated variables. -/
theorem tendsto_mollified_resonantIntegral
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel (resonantKernel Ψ k) A b M) (hd : 0 < d)
    {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) :
    Tendsto (fun ε => ∫ ℓ : Mom d, ∫ x : Mom d,
      Ψ (k + ℓ) (k + ℓ + x) (k + x) * mollifier ψ ε (2 * ⟪ℓ, x⟫_ℝ))
      (𝓝[>] 0) (𝓝 (resonantIntegral Ψ k)) :=
  hK.tendsto_integral_molInner hd hψ

/-- General delta reading in the original momentum variables. No evenness of the
mollifier is needed: reflection accounts for the sign of the energy resonance. -/
theorem tendsto_mollified_resonantIntegral_k
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel (resonantKernel Ψ k) A b M) (hd : 0 < d)
    {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) :
    Tendsto (fun ε => ∫ k₁ : Mom d, ∫ k₃ : Mom d,
      Ψ k₁ (k₁ + k₃ - k) k₃ *
        mollifier ψ ε (‖k₁‖ ^ 2 - ‖k₁ + k₃ - k‖ ^ 2 + ‖k₃‖ ^ 2 - ‖k‖ ^ 2))
      (𝓝[>] 0) (𝓝 (resonantIntegral Ψ k)) := by
  refine (tendsto_mollified_resonantIntegral hK hd hψ.comp_neg).congr (fun ε => ?_)
  symm
  rw [← integral_add_left_eq_self _ k]
  refine integral_congr_ae (Eventually.of_forall fun ℓ => ?_)
  simp only
  rw [← integral_add_left_eq_self _ k]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_sq_resonance k ℓ x]
  have e : k + ℓ + (k + x) - k = k + ℓ + x := by abel
  simp only [e, mollifier, neg_div]

/-- A bound by a polynomially decaying profile in each free momentum suffices
for both levels of integrability. The centers `a,b` can depend on `k`. -/
theorem deltaKernel_resonant_of_decay
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k a b : Mom d} {C M : ℝ}
    (hd : 2 ≤ d) (hM : (d : ℝ) < M)
    (hc : Continuous (Function.uncurry (resonantKernel Ψ k)))
    (hb : ∀ ℓ x, |resonantKernel Ψ k ℓ x| ≤
      C * (1 + ‖a + ℓ‖) ^ (-M) * (1 + ‖b + x‖) ^ (-M)) :
    DeltaKernel (resonantKernel Ψ k) (fun ℓ => C * (1 + ‖a + ℓ‖) ^ (-M))
      (fun _ => b) M where
  cont := hc
  bound := hb
  dim := hM
  integrable := by
    simpa only [mul_left_comm _ C] using
      (integrable_inv_norm_mul_one_add_norm hd hM a).const_mul C

/-- Absolute bound with the same singular radial integral as the WKE estimates. -/
theorem abs_resonantIntegral_le
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel (resonantKernel Ψ k) A b M) (hd : 0 < d) :
    |resonantIntegral Ψ k| ≤
      (2⁻¹ * hypConst d M) * ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * A ℓ := by
  rw [resonantIntegral, deltaInt, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hK.integrable.const_mul _) ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have h := hK.abs_sliceInt_le hℓ 0
  simp only [sliceInt, zero_smul, zero_add] at h
  calc (2 * ‖ℓ‖)⁻¹ * |∫ w : ↥(ℝ ∙ ℓ)ᗮ, resonantKernel Ψ k ℓ w|
      ≤ (2 * ‖ℓ‖)⁻¹ * (A ℓ * hypConst d M) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [mul_inv]; ring

/-- Uniform polynomial-decay bound, independent of the centers of the profiles. -/
theorem abs_resonantIntegral_le_of_decay
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k a b : Mom d} {C M : ℝ}
    (hd : 2 ≤ d) (hM : (d : ℝ) < M) (hC : 0 ≤ C)
    (hc : Continuous (Function.uncurry (resonantKernel Ψ k)))
    (hb : ∀ ℓ x, |resonantKernel Ψ k ℓ x| ≤
      C * (1 + ‖a + ℓ‖) ^ (-M) * (1 + ‖b + x‖) ^ (-M)) :
    |resonantIntegral Ψ k| ≤ (2⁻¹ * hypConst d M) * C * invNormConst d M := by
  have hK := deltaKernel_resonant_of_decay hd hM hc hb
  have hi := integral_inv_norm_mul_one_add_norm_le hd hM a
  have h := abs_resonantIntegral_le hK (by omega)
  have he : (∫ ℓ : Mom d, ‖ℓ‖⁻¹ * (C * (1 + ‖a + ℓ‖) ^ (-M))) =
      C * ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * (1 + ‖a + ℓ‖) ^ (-M) := by
    rw [← integral_const_mul]
    congr 1
    funext ℓ
    ring
  rw [he, ← mul_assoc] at h
  exact h.trans (mul_le_mul_of_nonneg_left hi
    (mul_nonneg (mul_nonneg (by norm_num) (hypConst_nonneg d M)) hC))

/-- The inner hyperplane integral is an honest Bochner integral away from `ℓ = 0`. -/
theorem integrable_resonantIntegral_perp
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel (resonantKernel Ψ k) A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => Ψ (k + ℓ) (k + ℓ + w) (k + w)) :=
  hK.integrable_perp hℓ

/-- The outer integral is also an honest Bochner integral. -/
theorem integrable_resonantIntegral_outer
    {Ψ : Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}
    (hK : DeltaKernel (resonantKernel Ψ k) A b M) (hd : 0 < d) :
    Integrable (fun ℓ : Mom d => (2 * ‖ℓ‖)⁻¹ *
      ∫ w : ↥(ℝ ∙ ℓ)ᗮ, Ψ (k + ℓ) (k + ℓ + w) (k + w)) :=
  hK.integrable_outer hd

end WaveTurbulence
