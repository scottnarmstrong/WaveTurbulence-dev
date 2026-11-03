/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Multilinear
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Leibniz rule for the collision operator

TARGET (schappend6) (L2506–L2508): `∇𝒦ⱼ(φ₁,φ₂,φ₃) = 𝒦ⱼ(∇φ₁,φ₂,φ₃) + 𝒦ⱼ(φ₁,∇φ₂,φ₃) +
𝒦ⱼ(φ₁,φ₂,∇φ₃)`. We prove it for Schwartz inputs as a Fréchet derivative
(`hasFDerivAt_collisionTerm`): `k ↦ 𝒦ⱼ(φ₁,φ₂,φ₃)(k)` is differentiable and its derivative in the
direction `v` is `𝒦ⱼ(∂ᵥφ₁,φ₂,φ₃) + 𝒦ⱼ(φ₁,∂ᵥφ₂,φ₃) + 𝒦ⱼ(φ₁,φ₂,∂ᵥφ₃)`.

The proof avoids differentiating under the hyperplane integral: by translation invariance
`𝒦ⱼ(φ)(k + h) = 𝒦ⱼ(φ(· + h))(k)`, and by telescoping and the weighted-sup trilinear bound
(`abs_collisionTerm_le`), the remainder is `O(|h|²)` because the weighted Taylor remainders
`φ(· + h) - φ - ∂ₕφ` are `O(|h|²)` in `L^∞_{2d+1}`.
-/

public section

open MeasureTheory Set Filter Topology Asymptotics
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence

variable {d : ℕ}

/-! ### Admissible inputs -/

/-- A continuous input with `(1 + |y|)^{-N}` decay. -/
@[expose] def Admissible (N : ℝ) (f : Mom d → ℝ) : Prop :=
  Continuous f ∧ ∃ C, DecayBound C N f

namespace Admissible

variable {N : ℝ} {f g : Mom d → ℝ}

theorem sub (hf : Admissible N f) (hg : Admissible N g) :
    Admissible N (fun y => f y - g y) := by
  obtain ⟨cf, C, hC⟩ := hf
  obtain ⟨cg, C', hC'⟩ := hg
  refine ⟨cf.sub cg, C + C', fun y => ?_⟩
  calc |f y - g y| ≤ |f y| + |g y| := abs_sub _ _
    _ ≤ C * (1 + ‖y‖) ^ (-N) + C' * (1 + ‖y‖) ^ (-N) := add_le_add (hC y) (hC' y)
    _ = (C + C') * (1 + ‖y‖) ^ (-N) := by ring

theorem deltaIntegrable {f₁ f₂ f₃ : Mom d → ℝ} (hd : 2 ≤ d) (hN : 2 * (d : ℝ) < N)
    (h₁ : Admissible N f₁) (h₂ : Admissible N f₂) (h₃ : Admissible N f₃) (j : Fin 4)
    (k : Mom d) : DeltaIntegrable (collisionKernel j f₁ f₂ f₃ k) := by
  obtain ⟨c₁, C₁, b₁⟩ := h₁
  obtain ⟨c₂, C₂, b₂⟩ := h₂
  obtain ⟨c₃, C₃, b₃⟩ := h₃
  exact (CollisionInputs.of c₁ c₂ c₃ b₁ b₂ b₃ hN).deltaIntegrable hd j k

end Admissible

/-- Telescoping for admissible inputs. -/
theorem collisionTerm_telescope (hd : 2 ≤ d) {N : ℝ} (hN : 2 * (d : ℝ) < N)
    {a₁ a₂ a₃ b₁ b₂ b₃ : Mom d → ℝ} (ha₁ : Admissible N a₁) (ha₂ : Admissible N a₂)
    (ha₃ : Admissible N a₃) (hb₁ : Admissible N b₁) (hb₂ : Admissible N b₂)
    (hb₃ : Admissible N b₃) (j : Fin 4) (k : Mom d) :
    collisionTerm j a₁ a₂ a₃ k - collisionTerm j b₁ b₂ b₃ k =
      collisionTerm j (fun y => a₁ y - b₁ y) a₂ a₃ k
        + collisionTerm j b₁ (fun y => a₂ y - b₂ y) a₃ k
        + collisionTerm j b₁ b₂ (fun y => a₃ y - b₃ y) k := by
  have hd0 : 0 < d := by omega
  have I := fun {f₁ f₂ f₃ : Mom d → ℝ} (h₁ : Admissible N f₁) (h₂ : Admissible N f₂)
    (h₃ : Admissible N f₃) => Admissible.deltaIntegrable hd hN h₁ h₂ h₃ j k
  have i₁ := I (ha₁.sub hb₁) ha₂ ha₃
  have i₂ := I hb₁ (ha₂.sub hb₂) ha₃
  have i₃ := I hb₁ hb₂ (ha₃.sub hb₃)
  simp only [collisionTerm]
  rw [← (I ha₁ ha₂ ha₃).deltaInt_sub (I hb₁ hb₂ hb₃) hd0,
    ← i₁.deltaInt_add i₂ hd0, ← (i₁.add i₂ hd0).deltaInt_add i₃ hd0]
  exact deltaInt_congr fun ℓ x => collisionKernel_sub j k ℓ x

/-- The pointwise trilinear bound at weight `s₀ = 2d + 1`. -/
@[expose] noncomputable def trilinA (d : ℕ) : ℝ :=
  3 * tameConst d (2 * d + 1) * 3 ^ (2 * (d : ℝ) + 1)

theorem abs_collisionTerm_le_trilinA (hd : 2 ≤ d) {f₁ f₂ f₃ : Mom d → ℝ} {C₁ C₂ C₃ : ℝ}
    (h₁ : DecayBound C₁ (2 * d + 1) f₁) (h₂ : DecayBound C₂ (2 * d + 1) f₂)
    (h₃ : DecayBound C₃ (2 * d + 1) f₃) (j : Fin 4) (k : Mom d) :
    |collisionTerm j f₁ f₂ f₃ k| ≤ trilinA d * (C₁ * C₂ * C₃) := by
  have h := abs_collisionTerm_le hd (by linarith) h₁ h₂ h₃ j k
  have h1 : 1 ≤ (1 + ‖k‖) ^ (2 * (d : ℝ) + 1) :=
    Real.one_le_rpow (by linarith [norm_nonneg k]) (by positivity)
  have : |collisionTerm j f₁ f₂ f₃ k| ≤ (1 + ‖k‖) ^ (2 * (d : ℝ) + 1) *
      |collisionTerm j f₁ f₂ f₃ k| := le_mul_of_one_le_left (abs_nonneg _) h1
  rw [trilinA]; linarith

/-! ### Weighted Taylor estimates for Schwartz functions -/

theorem exists_norm_le_of_schwartz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : 𝓢(Mom d, F)) (N : ℝ) : ∃ C, 0 ≤ C ∧ ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-N) := by
  set n : ℕ := ⌈N⌉₊
  set S : ℝ := 2 ^ n * (Finset.Iic (n, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨S, hS, fun y => ?_⟩
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n, 0)) le_rfl le_rfl f y
  rw [norm_iteratedFDeriv_zero] at hb
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h1 : ‖f y‖ ≤ S * ((1 + ‖y‖) ^ n)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith [mul_comm ((1 + ‖y‖) ^ n) ‖f y‖]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hS)
  rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y])
    (by linarith [Nat.le_ceil N])

/-- Peetre: `(1 + |z|)^{-N} ≤ 2^N (1 + |y|)^{-N}` when `|z - y| ≤ 1`. -/
theorem one_add_norm_rpow_neg_le_of_dist {y z : Mom d} (h : ‖z - y‖ ≤ 1) {N : ℝ} (hN : 0 ≤ N) :
    (1 + ‖z‖) ^ (-N) ≤ 2 ^ N * (1 + ‖y‖) ^ (-N) := by
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hz : 0 < 1 + ‖z‖ := by positivity
  have key : 1 + ‖y‖ ≤ 2 * (1 + ‖z‖) := by
    have := norm_sub_le_norm_sub_add_norm_sub y z 0
    have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
      calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
    rw [norm_sub_rev] at h2
    linarith [norm_nonneg z]
  rw [Real.rpow_neg hz.le, Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + ‖z‖) ^ N)⁻¹ * (1 + ‖y‖) ^ N ≤ ((1 + ‖z‖) ^ N)⁻¹ * (2 * (1 + ‖z‖)) ^ N :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le key hN) (by positivity)
    _ = 2 ^ N := by
        rw [Real.mul_rpow (by norm_num) hz.le]
        field_simp

/-- Weighted Taylor estimates for a Schwartz function, uniform in `|h| ≤ 1`. -/
theorem schwartz_taylor (φ : 𝓢(Mom d, ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    ∃ B, 0 ≤ B ∧ ∀ h : Mom d, ‖h‖ ≤ 1 →
      DecayBound B s (fun y => φ (y + h)) ∧
      DecayBound (B * ‖h‖) s (fun y => φ (y + h) - φ y) ∧
      DecayBound (B * ‖h‖ ^ 2) s (fun y => φ (y + h) - φ y - fderiv ℝ φ y h) ∧
      DecayBound (B * ‖h‖) s (fun y => fderiv ℝ φ y h) := by
  set Dφ := SchwartzMap.fderivCLM ℝ (Mom d) ℝ φ
  set D2φ := SchwartzMap.fderivCLM ℝ (Mom d) (Mom d →L[ℝ] ℝ) Dφ
  have hD : ∀ y, Dφ y = fderiv ℝ φ y := fun y => SchwartzMap.fderivCLM_apply ℝ φ y
  have hD2 : ∀ y, D2φ y = fderiv ℝ (fderiv ℝ φ) y := by
    intro y
    rw [SchwartzMap.fderivCLM_apply, show (⇑Dφ) = fderiv ℝ ⇑φ from funext hD]
  obtain ⟨C₀, hC₀, b₀⟩ := exists_norm_le_of_schwartz φ s
  obtain ⟨C₁, hC₁, b₁⟩ := exists_norm_le_of_schwartz Dφ s
  obtain ⟨C₂, hC₂, b₂⟩ := exists_norm_le_of_schwartz D2φ s
  have h2s : (0 : ℝ) ≤ 2 ^ s := by positivity
  refine ⟨2 ^ s * (C₀ + C₁ + C₂), by positivity, fun h hh => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro y
    have hz : ‖(y + h) - y‖ ≤ 1 := by rwa [add_sub_cancel_left]
    calc |φ (y + h)| = ‖φ (y + h)‖ := (Real.norm_eq_abs _).symm
      _ ≤ C₀ * (1 + ‖y + h‖) ^ (-s) := b₀ _
      _ ≤ C₀ * (2 ^ s * (1 + ‖y‖) ^ (-s)) :=
          mul_le_mul_of_nonneg_left (one_add_norm_rpow_neg_le_of_dist hz hs) hC₀
      _ ≤ 2 ^ s * (C₀ + C₁ + C₂) * (1 + ‖y‖) ^ (-s) := by
          have : 0 ≤ 2 ^ s * (C₁ + C₂) * (1 + ‖y‖) ^ (-s) := by positivity
          linarith [show C₀ * (2 ^ s * (1 + ‖y‖) ^ (-s)) + 2 ^ s * (C₁ + C₂) * (1 + ‖y‖) ^ (-s)
            = 2 ^ s * (C₀ + C₁ + C₂) * (1 + ‖y‖) ^ (-s) by ring]
  · intro y
    beta_reduce
    have hball : ∀ z ∈ Metric.closedBall y ‖h‖, ‖fderiv ℝ φ z‖ ≤ C₁ * 2 ^ s * (1 + ‖y‖) ^ (-s) := by
      intro z hzm
      have hz : ‖z - y‖ ≤ 1 := (mem_closedBall_iff_norm.mp hzm).trans hh
      rw [← hD z]
      calc ‖Dφ z‖ ≤ C₁ * (1 + ‖z‖) ^ (-s) := b₁ z
        _ ≤ C₁ * (2 ^ s * (1 + ‖y‖) ^ (-s)) :=
            mul_le_mul_of_nonneg_left (one_add_norm_rpow_neg_le_of_dist hz hs) hC₁
        _ = _ := by ring
    have hmv := (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => φ.differentiableAt) hball (Metric.mem_closedBall_self (norm_nonneg h))
      (by simp : y + h ∈ Metric.closedBall y ‖h‖)
    rw [add_sub_cancel_left] at hmv
    rw [← Real.norm_eq_abs]
    calc ‖φ (y + h) - φ y‖ ≤ C₁ * 2 ^ s * (1 + ‖y‖) ^ (-s) * ‖h‖ := hmv
      _ ≤ 2 ^ s * (C₀ + C₁ + C₂) * ‖h‖ * (1 + ‖y‖) ^ (-s) := by
          have : 0 ≤ 2 ^ s * (C₀ + C₂) * ‖h‖ * (1 + ‖y‖) ^ (-s) := by positivity
          linarith [show C₁ * 2 ^ s * (1 + ‖y‖) ^ (-s) * ‖h‖ + 2 ^ s * (C₀ + C₂) * ‖h‖ *
            (1 + ‖y‖) ^ (-s) = 2 ^ s * (C₀ + C₁ + C₂) * ‖h‖ * (1 + ‖y‖) ^ (-s) by ring]
  · intro y
    beta_reduce
    -- `g z = φ z - Dφ(y) z` has derivative `Dφ z - Dφ y`
    set g : Mom d → ℝ := fun z => φ z - fderiv ℝ φ y z
    have hgd : ∀ z, HasFDerivAt g (fderiv ℝ φ z - fderiv ℝ φ y) z := fun z =>
      (φ.differentiableAt.hasFDerivAt).sub (fderiv ℝ φ y).hasFDerivAt
    have hball2 : ∀ z ∈ Metric.closedBall y ‖h‖,
        ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ C₂ * 2 ^ s * (1 + ‖y‖) ^ (-s) := by
      intro z hzm
      have hz : ‖z - y‖ ≤ 1 := (mem_closedBall_iff_norm.mp hzm).trans hh
      rw [← hD2 z]
      calc ‖D2φ z‖ ≤ C₂ * (1 + ‖z‖) ^ (-s) := b₂ z
        _ ≤ C₂ * (2 ^ s * (1 + ‖y‖) ^ (-s)) :=
            mul_le_mul_of_nonneg_left (one_add_norm_rpow_neg_le_of_dist hz hs) hC₂
        _ = _ := by ring
    have hDdiff : ∀ z, DifferentiableAt ℝ (fderiv ℝ φ) z := by
      intro z
      have : (fderiv ℝ φ) = fun z => Dφ z := funext fun z => (hD z).symm
      rw [this]; exact Dφ.differentiableAt
    have hgball : ∀ z ∈ Metric.closedBall y ‖h‖,
        ‖fderiv ℝ g z‖ ≤ C₂ * 2 ^ s * (1 + ‖y‖) ^ (-s) * ‖h‖ := by
      intro z hzm
      rw [(hgd z).fderiv]
      have hmv2 := (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hDdiff z) hball2 (Metric.mem_closedBall_self (norm_nonneg h)) hzm
      exact hmv2.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hzm)
        (by positivity))
    have hmv := (convex_closedBall y ‖h‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hgd z).differentiableAt) hgball
      (Metric.mem_closedBall_self (norm_nonneg h))
      (by simp : y + h ∈ Metric.closedBall y ‖h‖)
    have e : g (y + h) - g y = φ (y + h) - φ y - fderiv ℝ φ y h := by
      simp only [g, map_add]; ring
    rw [e, add_sub_cancel_left] at hmv
    rw [← Real.norm_eq_abs]
    calc ‖φ (y + h) - φ y - fderiv ℝ φ y h‖ ≤ C₂ * 2 ^ s * (1 + ‖y‖) ^ (-s) * ‖h‖ * ‖h‖ := hmv
      _ ≤ 2 ^ s * (C₀ + C₁ + C₂) * ‖h‖ ^ 2 * (1 + ‖y‖) ^ (-s) := by
          have : 0 ≤ 2 ^ s * (C₀ + C₁) * ‖h‖ ^ 2 * (1 + ‖y‖) ^ (-s) := by positivity
          linarith [show C₂ * 2 ^ s * (1 + ‖y‖) ^ (-s) * ‖h‖ * ‖h‖ + 2 ^ s * (C₀ + C₁) *
            ‖h‖ ^ 2 * (1 + ‖y‖) ^ (-s) = 2 ^ s * (C₀ + C₁ + C₂) * ‖h‖ ^ 2 * (1 + ‖y‖) ^ (-s)
            by ring]
  · intro y
    beta_reduce
    rw [← Real.norm_eq_abs, ← hD y]
    calc ‖Dφ y h‖ ≤ ‖Dφ y‖ * ‖h‖ := (Dφ y).le_opNorm h
      _ ≤ C₁ * (1 + ‖y‖) ^ (-s) * ‖h‖ := mul_le_mul_of_nonneg_right (b₁ y) (norm_nonneg h)
      _ ≤ 2 ^ s * (C₀ + C₁ + C₂) * ‖h‖ * (1 + ‖y‖) ^ (-s) := by
          have hw : 0 ≤ ‖h‖ * (1 + ‖y‖) ^ (-s) := by positivity
          have h1 : (1 : ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) hs
          have hc : C₁ ≤ 2 ^ s * (C₀ + C₁ + C₂) := by nlinarith
          calc C₁ * (1 + ‖y‖) ^ (-s) * ‖h‖ = C₁ * (‖h‖ * (1 + ‖y‖) ^ (-s)) := by ring
            _ ≤ 2 ^ s * (C₀ + C₁ + C₂) * (‖h‖ * (1 + ‖y‖) ^ (-s)) :=
                mul_le_mul_of_nonneg_right hc hw
            _ = _ := by ring

/-! ### The remainder bound -/

theorem abs_add3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

theorem DecayBound.zero_sub {N : ℝ} (f : Mom d → ℝ) : DecayBound 0 N (fun y => f y - f y) :=
  fun y => by simp

/-- The second-order remainder of `𝒦ⱼ` along a perturbation `a = b + D + O(t²)`:
`|𝒦ⱼ(a) - 𝒦ⱼ(b) - Σᵢ 𝒦ⱼ(…, Dᵢ, …)| ≤ 6 · trilinA d · B³ t²`. -/
theorem abs_collisionTerm_remainder_le (hd : 2 ≤ d) {a₁ a₂ a₃ b₁ b₂ b₃ D₁ D₂ D₃ : Mom d → ℝ}
    {B t : ℝ} (hB : 0 ≤ B)
    (ha₁ : Admissible (2 * d + 1) a₁) (ha₂ : Admissible (2 * d + 1) a₂)
    (ha₃ : Admissible (2 * d + 1) a₃) (hb₁ : Admissible (2 * d + 1) b₁)
    (hb₂ : Admissible (2 * d + 1) b₂) (hb₃ : Admissible (2 * d + 1) b₃)
    (hD₁ : Admissible (2 * d + 1) D₁) (hD₂ : Admissible (2 * d + 1) D₂)
    (hD₃ : Admissible (2 * d + 1) D₃)
    (ba₂ : DecayBound B (2 * d + 1) a₂) (ba₃ : DecayBound B (2 * d + 1) a₃)
    (bb₁ : DecayBound B (2 * d + 1) b₁) (bb₂ : DecayBound B (2 * d + 1) b₂)
    (bD₁ : DecayBound (B * t) (2 * d + 1) D₁) (bD₂ : DecayBound (B * t) (2 * d + 1) D₂)
    (bδ₂ : DecayBound (B * t) (2 * d + 1) (fun y => a₂ y - b₂ y))
    (bδ₃ : DecayBound (B * t) (2 * d + 1) (fun y => a₃ y - b₃ y))
    (br₁ : DecayBound (B * t ^ 2) (2 * d + 1) (fun y => a₁ y - b₁ y - D₁ y))
    (br₂ : DecayBound (B * t ^ 2) (2 * d + 1) (fun y => a₂ y - b₂ y - D₂ y))
    (br₃ : DecayBound (B * t ^ 2) (2 * d + 1) (fun y => a₃ y - b₃ y - D₃ y))
    (j : Fin 4) (k : Mom d) :
    |collisionTerm j a₁ a₂ a₃ k - collisionTerm j b₁ b₂ b₃ k
      - (collisionTerm j D₁ b₂ b₃ k + collisionTerm j b₁ D₂ b₃ k + collisionTerm j b₁ b₂ D₃ k)|
      ≤ 6 * trilinA d * B ^ 3 * t ^ 2 := by
  have hN : 2 * (d : ℝ) < 2 * d + 1 := by linarith
  have T1 := collisionTerm_telescope hd hN ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ j k
  have T2 := collisionTerm_telescope hd hN (ha₁.sub hb₁) ha₂ ha₃ hD₁ hb₂ hb₃ j k
  have T3 := collisionTerm_telescope hd hN hb₁ (ha₂.sub hb₂) ha₃ hb₁ hD₂ hb₃ j k
  have T4 := collisionTerm_telescope hd hN hb₁ hb₂ (ha₃.sub hb₃) hb₁ hb₂ hD₃ j k
  rw [show collisionTerm j a₁ a₂ a₃ k - collisionTerm j b₁ b₂ b₃ k
      - (collisionTerm j D₁ b₂ b₃ k + collisionTerm j b₁ D₂ b₃ k + collisionTerm j b₁ b₂ D₃ k) =
      (collisionTerm j (fun y => (fun y => a₁ y - b₁ y) y - D₁ y) a₂ a₃ k
        + collisionTerm j D₁ (fun y => a₂ y - b₂ y) a₃ k
        + collisionTerm j D₁ b₂ (fun y => a₃ y - b₃ y) k)
      + (collisionTerm j (fun y => b₁ y - b₁ y) (fun y => a₂ y - b₂ y) a₃ k
        + collisionTerm j b₁ (fun y => (fun y => a₂ y - b₂ y) y - D₂ y) a₃ k
        + collisionTerm j b₁ D₂ (fun y => a₃ y - b₃ y) k)
      + (collisionTerm j (fun y => b₁ y - b₁ y) b₂ (fun y => a₃ y - b₃ y) k
        + collisionTerm j b₁ (fun y => b₂ y - b₂ y) (fun y => a₃ y - b₃ y) k
        + collisionTerm j b₁ b₂ (fun y => (fun y => a₃ y - b₃ y) y - D₃ y) k)
      by linear_combination T1 + T2 + T3 + T4]
  have A := fun {f₁ f₂ f₃ : Mom d → ℝ} {C₁ C₂ C₃ : ℝ} (h₁ : DecayBound C₁ (2 * d + 1) f₁)
    (h₂ : DecayBound C₂ (2 * d + 1) f₂) (h₃ : DecayBound C₃ (2 * d + 1) f₃) =>
    abs_collisionTerm_le_trilinA hd h₁ h₂ h₃ j k
  have z₁ := DecayBound.zero_sub (N := 2 * d + 1) b₁
  have z₂ := DecayBound.zero_sub (N := 2 * d + 1) b₂
  have e1 := A br₁ ba₂ ba₃
  have e2 := A bD₁ bδ₂ ba₃
  have e3 := A bD₁ bb₂ bδ₃
  have e4 := A z₁ bδ₂ ba₃
  have e5 := A bb₁ br₂ ba₃
  have e6 := A bb₁ bD₂ bδ₃
  have e7 := A z₁ bb₂ bδ₃
  have e8 := A bb₁ z₂ bδ₃
  have e9 := A bb₁ bb₂ br₃
  refine (abs_add3_le _ _ _).trans ?_
  refine (add_le_add (add_le_add (abs_add3_le _ _ _) (abs_add3_le _ _ _))
    (abs_add3_le _ _ _)).trans ?_
  have hA0 : 0 ≤ trilinA d := by
    have := (abs_nonneg _).trans e9
    have hp : 0 ≤ B * B * (B * t ^ 2) := by positivity
    rcases hp.eq_or_lt with h0 | h0
    · rw [trilinA, tameConst]
      have := hypConst_nonneg d ((2 * d + 1) / 2)
      have : 0 ≤ invNormConst d ((2 * d + 1) / 2) := by
        unfold invNormConst
        refine add_nonneg (setIntegral_nonneg measurableSet_ball fun x _ => by positivity)
          (integral_nonneg fun x => by positivity)
      positivity
    · exact (mul_nonneg_iff_of_pos_right h0).mp this
  have key : trilinA d * (B * t ^ 2 * B * B) + trilinA d * (B * t * (B * t) * B)
      + trilinA d * (B * t * B * (B * t)) + (trilinA d * (0 * (B * t) * B)
      + trilinA d * (B * (B * t ^ 2) * B) + trilinA d * (B * (B * t) * (B * t)))
      + (trilinA d * (0 * B * (B * t)) + trilinA d * (B * 0 * (B * t))
      + trilinA d * (B * B * (B * t ^ 2))) = 6 * trilinA d * B ^ 3 * t ^ 2 := by ring
  rw [← key]
  gcongr

/-! ### Linearity in the direction and the Leibniz rule -/

section SlotLinear

variable {f g a₂ a₃ a₁ : Mom d → ℝ}

theorem collisionKernel_add_one (j : Fin 4) (k ℓ x : Mom d) :
    collisionKernel j (fun y => f y + g y) a₂ a₃ k ℓ x =
      collisionKernel j f a₂ a₃ k ℓ x + collisionKernel j g a₂ a₃ k ℓ x := by
  fin_cases j <;> simp only [collisionKernel] <;> ring

theorem collisionKernel_add_two (j : Fin 4) (k ℓ x : Mom d) :
    collisionKernel j a₁ (fun y => f y + g y) a₃ k ℓ x =
      collisionKernel j a₁ f a₃ k ℓ x + collisionKernel j a₁ g a₃ k ℓ x := by
  fin_cases j <;> simp only [collisionKernel] <;> ring

theorem collisionKernel_add_three (j : Fin 4) (k ℓ x : Mom d) :
    collisionKernel j a₁ a₂ (fun y => f y + g y) k ℓ x =
      collisionKernel j a₁ a₂ f k ℓ x + collisionKernel j a₁ a₂ g k ℓ x := by
  fin_cases j <;> simp only [collisionKernel] <;> ring

end SlotLinear

theorem admissible_schwartz (φ : 𝓢(Mom d, ℝ)) (N : ℝ) : Admissible N φ := by
  obtain ⟨C, -, hC⟩ := exists_norm_le_of_schwartz φ N
  exact ⟨φ.continuous, C, fun y => by rw [← Real.norm_eq_abs]; exact hC y⟩

theorem admissible_fderiv (φ : 𝓢(Mom d, ℝ)) (N : ℝ) (v : Mom d) :
    Admissible N (fun y => fderiv ℝ φ y v) := by
  set Dφ := SchwartzMap.fderivCLM ℝ (Mom d) ℝ φ
  have e : (fun y => fderiv ℝ φ y v) = fun y => Dφ y v := by
    funext y; rw [SchwartzMap.fderivCLM_apply]
  rw [e]
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_schwartz Dφ N
  refine ⟨Dφ.continuous.clm_apply continuous_const, C * ‖v‖, fun y => ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖Dφ y v‖ ≤ ‖Dφ y‖ * ‖v‖ := (Dφ y).le_opNorm v
    _ ≤ C * (1 + ‖y‖) ^ (-N) * ‖v‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg v)
    _ = C * ‖v‖ * (1 + ‖y‖) ^ (-N) := by ring

/-- The Leibniz expression `𝒦ⱼ(∂ᵥφ₁,φ₂,φ₃) + 𝒦ⱼ(φ₁,∂ᵥφ₂,φ₃) + 𝒦ⱼ(φ₁,φ₂,∂ᵥφ₃)` at `k`. -/
@[expose] noncomputable def leibnizDir (j : Fin 4) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) (k v : Mom d) : ℝ :=
  collisionTerm j (fun y => fderiv ℝ φ₁ y v) φ₂ φ₃ k
    + collisionTerm j φ₁ (fun y => fderiv ℝ φ₂ y v) φ₃ k
    + collisionTerm j φ₁ φ₂ (fun y => fderiv ℝ φ₃ y v) k

theorem leibnizDir_add (hd : 2 ≤ d) (j : Fin 4) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) (k v w : Mom d) :
    leibnizDir j φ₁ φ₂ φ₃ k (v + w) = leibnizDir j φ₁ φ₂ φ₃ k v + leibnizDir j φ₁ φ₂ φ₃ k w := by
  have hN : 2 * (d : ℝ) < 2 * d + 1 := by linarith
  have hd0 : 0 < d := by omega
  have S := fun φ : 𝓢(Mom d, ℝ) => admissible_schwartz φ (2 * d + 1)
  have D := fun (φ : 𝓢(Mom d, ℝ)) v => admissible_fderiv φ (2 * d + 1) v
  have I := fun {f₁ f₂ f₃ : Mom d → ℝ} (h₁ : Admissible (2 * d + 1) f₁)
    (h₂ : Admissible (2 * d + 1) f₂) (h₃ : Admissible (2 * d + 1) f₃) =>
    Admissible.deltaIntegrable hd hN h₁ h₂ h₃ j k
  have e : ∀ φ : 𝓢(Mom d, ℝ), (fun y => fderiv ℝ φ y (v + w)) =
      fun y => fderiv ℝ φ y v + fderiv ℝ φ y w := fun φ => funext fun y => map_add _ v w
  simp only [leibnizDir, e, collisionTerm]
  rw [deltaInt_congr fun ℓ x => collisionKernel_add_one j k ℓ x,
    deltaInt_congr fun ℓ x => collisionKernel_add_two j k ℓ x,
    deltaInt_congr fun ℓ x => collisionKernel_add_three j k ℓ x,
    (I (D φ₁ v) (S φ₂) (S φ₃)).deltaInt_add (I (D φ₁ w) (S φ₂) (S φ₃)) hd0,
    (I (S φ₁) (D φ₂ v) (S φ₃)).deltaInt_add (I (S φ₁) (D φ₂ w) (S φ₃)) hd0,
    (I (S φ₁) (S φ₂) (D φ₃ v)).deltaInt_add (I (S φ₁) (S φ₂) (D φ₃ w)) hd0]
  ring

theorem leibnizDir_smul (j : Fin 4) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) (k : Mom d) (c : ℝ) (v : Mom d) :
    leibnizDir j φ₁ φ₂ φ₃ k (c • v) = c * leibnizDir j φ₁ φ₂ φ₃ k v := by
  have e : ∀ φ : 𝓢(Mom d, ℝ), (fun y => fderiv ℝ φ y (c • v)) =
      fun y => c * fderiv ℝ φ y v := fun φ => funext fun y => by rw [map_smul, smul_eq_mul]
  simp only [leibnizDir, e, collisionTerm]
  rw [deltaInt_congr (F := collisionKernel j (fun y => c * fderiv ℝ φ₁ y v) φ₂ φ₃ k)
      (G := fun ℓ x => c * collisionKernel j (fun y => fderiv ℝ φ₁ y v) φ₂ φ₃ k ℓ x)
      (fun ℓ x => by fin_cases j <;> simp only [collisionKernel] <;> ring),
    deltaInt_congr (F := collisionKernel j φ₁ (fun y => c * fderiv ℝ φ₂ y v) φ₃ k)
      (G := fun ℓ x => c * collisionKernel j φ₁ (fun y => fderiv ℝ φ₂ y v) φ₃ k ℓ x)
      (fun ℓ x => by fin_cases j <;> simp only [collisionKernel] <;> ring),
    deltaInt_congr (F := collisionKernel j φ₁ φ₂ (fun y => c * fderiv ℝ φ₃ y v) k)
      (G := fun ℓ x => c * collisionKernel j φ₁ φ₂ (fun y => fderiv ℝ φ₃ y v) k ℓ x)
      (fun ℓ x => by fin_cases j <;> simp only [collisionKernel] <;> ring),
    deltaInt_smul, deltaInt_smul, deltaInt_smul]
  ring

/-- **Leibniz rule** TARGET (schappend6) (L2506–L2508) for Schwartz inputs: `k ↦ 𝒦ⱼ(φ₁,φ₂,φ₃)(k)`
is Fréchet differentiable, with derivative in the direction `v` equal to
`𝒦ⱼ(∂ᵥφ₁,φ₂,φ₃) + 𝒦ⱼ(φ₁,∂ᵥφ₂,φ₃) + 𝒦ⱼ(φ₁,φ₂,∂ᵥφ₃)`. -/
theorem hasFDerivAt_collisionTerm (hd : 2 ≤ d) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) (j : Fin 4)
    (k : Mom d) :
    ∃ L : Mom d →L[ℝ] ℝ, HasFDerivAt (collisionTerm j φ₁ φ₂ φ₃) L k ∧
      ∀ v, L v = leibnizDir j φ₁ φ₂ φ₃ k v := by
  let Lin : Mom d →ₗ[ℝ] ℝ :=
    { toFun := leibnizDir j φ₁ φ₂ φ₃ k
      map_add' := leibnizDir_add hd j φ₁ φ₂ φ₃ k
      map_smul' := fun c v => leibnizDir_smul j φ₁ φ₂ φ₃ k c v }
  refine ⟨LinearMap.toContinuousLinearMap Lin, ?_, fun v => rfl⟩
  have hs : (0 : ℝ) ≤ 2 * d + 1 := by positivity
  obtain ⟨B₁, hB₁, T₁⟩ := schwartz_taylor φ₁ hs
  obtain ⟨B₂, hB₂, T₂⟩ := schwartz_taylor φ₂ hs
  obtain ⟨B₃, hB₃, T₃⟩ := schwartz_taylor φ₃ hs
  set B := B₁ + B₂ + B₃
  have hB : 0 ≤ B := by positivity
  have l₁ : B₁ ≤ B := by simp only [B]; linarith
  have l₂ : B₂ ≤ B := by simp only [B]; linarith
  have l₃ : B₃ ≤ B := by simp only [B]; linarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO ?_ (isLittleO_norm_pow_id (n := 2) one_lt_two)
  refine IsBigO.of_bound (6 * trilinA d * B ^ 3) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : Mom d) one_pos] with h hh
  have hh' : ‖h‖ ≤ 1 := by simpa using hh
  have hnh := norm_nonneg h
  obtain ⟨a₁, δ₁, r₁, D₁⟩ := T₁ h hh'
  obtain ⟨a₂, δ₂, r₂, D₂⟩ := T₂ h hh'
  obtain ⟨a₃, δ₃, r₃, D₃⟩ := T₃ h hh'
  have z₁ : DecayBound B₁ (2 * d + 1) φ₁ := by simpa using (T₁ 0 (by simp)).1
  have z₂ : DecayBound B₂ (2 * d + 1) φ₂ := by simpa using (T₂ 0 (by simp)).1
  have tr : ∀ φ : 𝓢(Mom d, ℝ), Continuous fun y => φ (y + h) :=
    fun φ => φ.continuous.comp (continuous_id.add continuous_const)
  have hmono : ∀ {Bi : ℝ} (c : ℝ), 0 ≤ c → Bi ≤ B → Bi * c ≤ B * c :=
    fun c hc hle => mul_le_mul_of_nonneg_right hle hc
  have key := abs_collisionTerm_remainder_le (j := j) (k := k) (t := ‖h‖) hd hB
    ⟨tr φ₁, _, a₁⟩ ⟨tr φ₂, _, a₂⟩ ⟨tr φ₃, _, a₃⟩
    (admissible_schwartz φ₁ _) (admissible_schwartz φ₂ _) (admissible_schwartz φ₃ _)
    (admissible_fderiv φ₁ _ h) (admissible_fderiv φ₂ _ h) (admissible_fderiv φ₃ _ h)
    (a₂.mono_C l₂) (a₃.mono_C l₃) (z₁.mono_C l₁) (z₂.mono_C l₂)
    (D₁.mono_C (hmono _ hnh l₁)) (D₂.mono_C (hmono _ hnh l₂))
    (δ₂.mono_C (hmono _ hnh l₂)) (δ₃.mono_C (hmono _ hnh l₃))
    (r₁.mono_C (hmono _ (by positivity) l₁)) (r₂.mono_C (hmono _ (by positivity) l₂))
    (r₃.mono_C (hmono _ (by positivity) l₃))
  rw [collisionTerm_translate, Real.norm_eq_abs, norm_pow, norm_norm]
  calc |_| = |collisionTerm j (fun y => φ₁ (y + h)) (fun y => φ₂ (y + h)) (fun y => φ₃ (y + h)) k
        - collisionTerm j φ₁ φ₂ φ₃ k - leibnizDir j φ₁ φ₂ φ₃ k h| := rfl
    _ ≤ 6 * trilinA d * B ^ 3 * ‖h‖ ^ 2 := key

end WaveTurbulence
