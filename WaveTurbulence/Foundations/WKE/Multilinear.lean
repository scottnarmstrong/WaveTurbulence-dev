/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Characterization
public import WaveTurbulence.Foundations.WKE.Trilinear

/-!
# Multilinearity, translation invariance and the weight identity

* `DeltaKernel.deltaInt_add`, `deltaInt_smul`: linearity of `deltaInt` on decaying kernels;
* `collisionTerm_sub_sub_sub`: the telescoping identity
  `𝒦ⱼ(a) - 𝒦ⱼ(b) = 𝒦ⱼ(a₁-b₁, a₂, a₃) + 𝒦ⱼ(b₁, a₂-b₂, a₃) + 𝒦ⱼ(b₁, b₂, a₃-b₃)`;
* `collisionTerm_translate`: `𝒦ⱼ(φ₁, φ₂, φ₃)(k + h) = 𝒦ⱼ(φ₁(· + h), φ₂(· + h), φ₃(· + h))(k)`;
* `weight_collisionTerm`: the weight identity TARGET (schappend7) (L2509–L2511):
  `λ(k) 𝒦₀(φ₁,φ₂,φ₃) = 𝒦₀(λφ₁,φ₂,φ₃) - 𝒦₀(φ₁,λφ₂,φ₃) + 𝒦₀(φ₁,φ₂,λφ₃)` for a linear functional
  `λ` (e.g. a coordinate `kⁱ`), and the one-term versions for `𝒦₁, 𝒦₂, 𝒦₃`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence.WKE

variable {d : ℕ}

/-! ### Linearity of `deltaInt` -/

/-- Both levels of `deltaInt F` are honest integrals: the hyperplane integrands are integrable
for `ℓ ≠ 0` and the outer integrand is integrable. -/
structure DeltaIntegrable (F : Mom d → Mom d → ℝ) : Prop where
  perp : ∀ ℓ : Mom d, ℓ ≠ 0 → Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => F ℓ w)
  outer : Integrable (fun ℓ : Mom d => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ w)

theorem _root_.WaveTurbulence.DeltaKernel.deltaIntegrable {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ}
    {b : Mom d → Mom d} {M : ℝ} (hF : DeltaKernel F A b M) (hd : 0 < d) :
    DeltaIntegrable F :=
  ⟨fun _ hℓ => hF.integrable_perp hℓ, hF.integrable_outer hd⟩

namespace DeltaIntegrable

variable {F G : Mom d → Mom d → ℝ}

theorem add (hF : DeltaIntegrable F) (hG : DeltaIntegrable G) (hd : 0 < d) :
    DeltaIntegrable (fun ℓ x => F ℓ x + G ℓ x) where
  perp ℓ hℓ := (hF.perp ℓ hℓ).add (hG.perp ℓ hℓ)
  outer := by
    refine (hF.outer.add hG.outer).congr ?_
    filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    rw [integral_add (hF.perp ℓ hℓ) (hG.perp ℓ hℓ), mul_add]
    rfl

theorem sub (hF : DeltaIntegrable F) (hG : DeltaIntegrable G) (hd : 0 < d) :
    DeltaIntegrable (fun ℓ x => F ℓ x - G ℓ x) where
  perp ℓ hℓ := (hF.perp ℓ hℓ).sub (hG.perp ℓ hℓ)
  outer := by
    refine (hF.outer.sub hG.outer).congr ?_
    filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    rw [integral_sub (hF.perp ℓ hℓ) (hG.perp ℓ hℓ), mul_sub]
    rfl

theorem deltaInt_add (hF : DeltaIntegrable F) (hG : DeltaIntegrable G) (hd : 0 < d) :
    deltaInt (fun ℓ x => F ℓ x + G ℓ x) = deltaInt F + deltaInt G := by
  simp only [deltaInt]
  rw [← integral_add hF.outer hG.outer]
  refine integral_congr_ae ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [integral_add (hF.perp ℓ hℓ) (hG.perp ℓ hℓ), mul_add]

theorem deltaInt_sub (hF : DeltaIntegrable F) (hG : DeltaIntegrable G) (hd : 0 < d) :
    deltaInt (fun ℓ x => F ℓ x - G ℓ x) = deltaInt F - deltaInt G := by
  simp only [deltaInt]
  rw [← integral_sub hF.outer hG.outer]
  refine integral_congr_ae ?_
  filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
  rw [integral_sub (hF.perp ℓ hℓ) (hG.perp ℓ hℓ), mul_sub]

end DeltaIntegrable

theorem deltaInt_smul (c : ℝ) (F : Mom d → Mom d → ℝ) :
    deltaInt (fun ℓ x => c * F ℓ x) = c * deltaInt F := by
  simp only [deltaInt]
  rw [← integral_const_mul]
  congr 1; funext ℓ
  rw [integral_const_mul]; ring

theorem deltaInt_congr {F G : Mom d → Mom d → ℝ} (h : ∀ ℓ x, F ℓ x = G ℓ x) :
    deltaInt F = deltaInt G := by
  have : F = G := funext fun ℓ => funext fun x => h ℓ x
  rw [this]

theorem _root_.WaveTurbulence.CollisionInputs.deltaIntegrable {φ₁ φ₂ φ₃ : Mom d → ℝ} {C N : ℝ}
    (h : CollisionInputs φ₁ φ₂ φ₃ C N) (hd : 2 ≤ d) (j : Fin 4) (k : Mom d) :
    DeltaIntegrable (collisionKernel j φ₁ φ₂ φ₃ k) :=
  (h.deltaKernel hd j k).deltaIntegrable (by omega)

/-! ### Telescoping -/

section Telescoping

variable {a₁ a₂ a₃ b₁ b₂ b₃ : Mom d → ℝ}

theorem collisionKernel_sub (j : Fin 4) (k ℓ x : Mom d) :
    collisionKernel j a₁ a₂ a₃ k ℓ x - collisionKernel j b₁ b₂ b₃ k ℓ x =
      collisionKernel j (fun y => a₁ y - b₁ y) a₂ a₃ k ℓ x
        + collisionKernel j b₁ (fun y => a₂ y - b₂ y) a₃ k ℓ x
        + collisionKernel j b₁ b₂ (fun y => a₃ y - b₃ y) k ℓ x := by
  fin_cases j <;> simp only [collisionKernel] <;> ring

end Telescoping

/-! ### Translation invariance -/

theorem collisionKernel_translate (j : Fin 4) (φ₁ φ₂ φ₃ : Mom d → ℝ) (k h ℓ x : Mom d) :
    collisionKernel j φ₁ φ₂ φ₃ (k + h) ℓ x =
      collisionKernel j (fun y => φ₁ (y + h)) (fun y => φ₂ (y + h)) (fun y => φ₃ (y + h))
        k ℓ x := by
  have e1 : k + h + ℓ = k + ℓ + h := by abel
  have e2 : k + ℓ + h + x = k + ℓ + x + h := by abel
  have e3 : k + h + x = k + x + h := by abel
  fin_cases j <;> simp only [collisionKernel, e1, e2, e3]

/-- **Translation invariance** `𝒦ⱼ(φ₁, φ₂, φ₃)(k + h) = 𝒦ⱼ(φ₁(·+h), φ₂(·+h), φ₃(·+h))(k)`. -/
theorem collisionTerm_translate (j : Fin 4) (φ₁ φ₂ φ₃ : Mom d → ℝ) (k h : Mom d) :
    collisionTerm j φ₁ φ₂ φ₃ (k + h) =
      collisionTerm j (fun y => φ₁ (y + h)) (fun y => φ₂ (y + h)) (fun y => φ₃ (y + h)) k :=
  deltaInt_congr fun ℓ x => collisionKernel_translate j φ₁ φ₂ φ₃ k h ℓ x

/-! ### The weight identity (schappend7) -/

section Weight

variable {φ₁ φ₂ φ₃ : Mom d → ℝ}

theorem collisionKernel_weight (lam : Mom d →L[ℝ] ℝ) (k ℓ x : Mom d) :
    lam k * collisionKernel 0 φ₁ φ₂ φ₃ k ℓ x =
      collisionKernel 0 (fun y => lam y * φ₁ y) φ₂ φ₃ k ℓ x
        - collisionKernel 0 φ₁ (fun y => lam y * φ₂ y) φ₃ k ℓ x
        + collisionKernel 0 φ₁ φ₂ (fun y => lam y * φ₃ y) k ℓ x := by
  simp only [collisionKernel, map_add]
  ring

theorem _root_.WaveTurbulence.DecayBound.anti {C N N' : ℝ} {φ : Mom d → ℝ} (h : DecayBound C N φ) (hN : N' ≤ N) :
    DecayBound C N' φ :=
  fun y => (h y).trans (mul_le_mul_of_nonneg_left (one_add_norm_rpow_neg_anti hN) h.C_nonneg)

theorem _root_.WaveTurbulence.DecayBound.clm_mul {C N : ℝ} {φ : Mom d → ℝ} (h : DecayBound C (N + 1) φ)
    (lam : Mom d →L[ℝ] ℝ) : DecayBound (‖lam‖ * C) N (fun y => lam y * φ y) := by
  intro y
  have hy : 0 < 1 + ‖y‖ := by positivity
  have e : (1 + ‖y‖) * (1 + ‖y‖) ^ (-(N + 1)) = (1 + ‖y‖) ^ (-N) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (1 + ‖y‖)]
    rw [← Real.rpow_add hy]; ring_nf
  have hC := h.C_nonneg
  rw [abs_mul]
  calc |lam y| * |φ y| ≤ (‖lam‖ * (1 + ‖y‖)) * (C * (1 + ‖y‖) ^ (-(N + 1))) := by
        refine mul_le_mul ?_ (h y) (abs_nonneg _) (by positivity)
        rw [← Real.norm_eq_abs]
        exact (lam.le_opNorm y).trans
          (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg y]) (norm_nonneg _))
    _ = ‖lam‖ * C * ((1 + ‖y‖) * (1 + ‖y‖) ^ (-(N + 1))) := by ring
    _ = _ := by rw [e]

theorem _root_.WaveTurbulence.CollisionInputs.of {f₁ f₂ f₃ : Mom d → ℝ} {C₁ C₂ C₃ N : ℝ} (c₁ : Continuous f₁)
    (c₂ : Continuous f₂) (c₃ : Continuous f₃) (h₁ : DecayBound C₁ N f₁)
    (h₂ : DecayBound C₂ N f₂) (h₃ : DecayBound C₃ N f₃) (hN : 2 * (d : ℝ) < N) :
    CollisionInputs f₁ f₂ f₃ (max C₁ (max C₂ C₃)) N :=
  ⟨c₁, c₂, c₃, h₁.mono_C (le_max_left _ _),
    h₂.mono_C ((le_max_left _ _).trans (le_max_right _ _)),
    h₃.mono_C ((le_max_right _ _).trans (le_max_right _ _)), hN⟩

/-- **Weight identity** TARGET (schappend7) (L2509–L2511) for the gain term `𝒦₀`, for any linear
functional `λ` (e.g. a coordinate `kⁱ`), on continuous inputs with `(1+|y|)^{-(N+1)}` decay,
`N > 2d`. -/
theorem weight_collisionTerm_zero (hd : 2 ≤ d) {C N : ℝ} (hN : 2 * (d : ℝ) < N)
    (c₁ : Continuous φ₁) (c₂ : Continuous φ₂) (c₃ : Continuous φ₃)
    (h₁ : DecayBound C (N + 1) φ₁) (h₂ : DecayBound C (N + 1) φ₂)
    (h₃ : DecayBound C (N + 1) φ₃) (lam : Mom d →L[ℝ] ℝ) (k : Mom d) :
    lam k * collisionTerm 0 φ₁ φ₂ φ₃ k =
      collisionTerm 0 (fun y => lam y * φ₁ y) φ₂ φ₃ k
        - collisionTerm 0 φ₁ (fun y => lam y * φ₂ y) φ₃ k
        + collisionTerm 0 φ₁ φ₂ (fun y => lam y * φ₃ y) k := by
  have hd0 : 0 < d := by omega
  have l₁ : Continuous fun y => lam y * φ₁ y := lam.continuous.mul c₁
  have l₂ : Continuous fun y => lam y * φ₂ y := lam.continuous.mul c₂
  have l₃ : Continuous fun y => lam y * φ₃ y := lam.continuous.mul c₃
  have i₁ := (CollisionInputs.of l₁ c₂ c₃ (h₁.clm_mul lam) (h₂.anti (by linarith))
    (h₃.anti (by linarith)) hN).deltaIntegrable hd 0 k
  have i₂ := (CollisionInputs.of c₁ l₂ c₃ (h₁.anti (by linarith)) (h₂.clm_mul lam)
    (h₃.anti (by linarith)) hN).deltaIntegrable hd 0 k
  have i₃ := (CollisionInputs.of c₁ c₂ l₃ (h₁.anti (by linarith))
    (h₂.anti (by linarith)) (h₃.clm_mul lam) hN).deltaIntegrable hd 0 k
  simp only [collisionTerm]
  rw [← deltaInt_smul, ← i₁.deltaInt_sub i₂ hd0, ← (i₁.sub i₂ hd0).deltaInt_add i₃ hd0]
  exact deltaInt_congr fun ℓ x => collisionKernel_weight lam k ℓ x

/-- Weight identity for the loss terms (one term each): `λ(k) 𝒦₁(φ₁,φ₂,φ₃) = 𝒦₁(λφ₁,φ₂,φ₃)`,
`λ(k) 𝒦₂ = 𝒦₂(φ₁,λφ₂,φ₃)`, `λ(k) 𝒦₃ = 𝒦₃(φ₁,φ₂,λφ₃)` (TARGET L2511). No hypotheses needed. -/
theorem weight_collisionTerm_one (lam : Mom d →L[ℝ] ℝ) (k : Mom d) :
    lam k * collisionTerm 1 φ₁ φ₂ φ₃ k = collisionTerm 1 (fun y => lam y * φ₁ y) φ₂ φ₃ k := by
  simp only [collisionTerm]
  rw [← deltaInt_smul]
  exact deltaInt_congr fun ℓ x => by simp only [collisionKernel]; ring

theorem weight_collisionTerm_two (lam : Mom d →L[ℝ] ℝ) (k : Mom d) :
    lam k * collisionTerm 2 φ₁ φ₂ φ₃ k = collisionTerm 2 φ₁ (fun y => lam y * φ₂ y) φ₃ k := by
  simp only [collisionTerm]
  rw [← deltaInt_smul]
  exact deltaInt_congr fun ℓ x => by simp only [collisionKernel]; ring

theorem weight_collisionTerm_three (lam : Mom d →L[ℝ] ℝ) (k : Mom d) :
    lam k * collisionTerm 3 φ₁ φ₂ φ₃ k = collisionTerm 3 φ₁ φ₂ (fun y => lam y * φ₃ y) k := by
  simp only [collisionTerm]
  rw [← deltaInt_smul]
  exact deltaInt_congr fun ℓ x => by simp only [collisionKernel]; ring

end Weight

end WaveTurbulence.WKE
