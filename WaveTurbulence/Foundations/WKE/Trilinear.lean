/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.CollisionOp

/-!
# Tame weighted-sup trilinear estimate for the collision operator

For `d ≥ 2`, `s₀ > 2d`, `s ≥ 0` and inputs with `|fᵢ(y)| ≤ Hᵢ (1 + |y|)^{-s}` and
`|fᵢ(y)| ≤ Lᵢ (1 + |y|)^{-s₀}` (no continuity needed: the bounds hold for every function),

`(1 + |k|)^s |𝒦ⱼ(f₁, f₂, f₃)(k)| ≤ tameConst d s₀ · 3^s · (H₁L₂L₃ + L₁H₂L₃ + L₁L₂H₃)`

(`abs_collisionTerm_le_tame`), and four times this for `𝒦 = collisionOp`
(`abs_collisionOp_le_tame`). With `s = s₀` this is the trilinear estimate
`‖𝒦ⱼ(f₁, f₂, f₃)‖_{L^∞_s} ≤ C(d, s) ∏ ‖fᵢ‖_{L^∞_s}` for `s > 2d`.

This is the weighted-`L^∞` substitute for the `Z_s = L²_s` estimate (schappend8) of TARGET
Appendix C (L2513–L2516), cited there from GIT20 Lemmas 4.1–4.3; GIT20 proves the `L²` estimate
only in `d = 3` (FINDINGS F18/F32). The tame form (the weight `s` lands on one input only) is
what the a priori estimate (schappend10) and the Taylor bound (taylorbound) need.

The proof: `k = k₁ - k₂ + k₃` on the support (in the variables (C.5): `k₁ = k + ℓ₁`,
`k₂ = k + ℓ₁ + ℓ₃`, `k₃ = k + ℓ₃`), hence `(1 + |k|)^s ≤ 3^s Σᵢ (1 + |kᵢ|)^s`; the two remaining
factors are integrated by the uniform hyperplane bound and `∫ |ℓ|⁻¹ (1 + |c + ℓ|)^{-s₀/2} dℓ ≤ C`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-! ### Abstract bounds for decaying kernels -/

/-- `∫_{|ℓ|<1} |ℓ|⁻¹ dℓ + ∫ (1 + |ℓ|)^{-M} dℓ`. -/
@[expose] noncomputable def invNormConst (d : ℕ) (M : ℝ) : ℝ :=
  (∫ x in Metric.ball (0 : Mom d) 1, ‖x‖⁻¹) + ∫ x : Mom d, (1 + ‖x‖) ^ (-M)

theorem integral_inv_norm_mul_one_add_norm_le (hd : 2 ≤ d) {M : ℝ} (hM : (d : ℝ) < M)
    (c : Mom d) : ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * (1 + ‖c + ℓ‖) ^ (-M) ≤ invNormConst d M := by
  have hfin : Module.finrank ℝ (Mom d) = d := finrank_euclideanSpace_fin
  have hfr : (Module.finrank ℝ (Mom d) : ℝ) < M := by rw [hfin]; exact hM
  have hdec := (integrable_one_add_norm (E := Mom d) (μ := volume) hfr).comp_add_left c
  have hind := (integrableOn_ball_inv_norm hd).integrable_indicator measurableSet_ball
  calc ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * (1 + ‖c + ℓ‖) ^ (-M)
      ≤ ∫ ℓ : Mom d, ((Metric.ball (0 : Mom d) 1).indicator (fun x => ‖x‖⁻¹) ℓ
          + (1 + ‖c + ℓ‖) ^ (-M)) :=
        integral_mono (integrable_inv_norm_mul_one_add_norm hd hM c) (hind.add hdec)
          (fun ℓ => inv_norm_mul_one_add_norm_le (le_trans (Nat.cast_nonneg d) hM.le) c ℓ)
    _ = invNormConst d M := by
        rw [integral_add hind hdec, integral_indicator measurableSet_ball]
        have h := integral_add_left_eq_self (μ := (volume : Measure (Mom d)))
          (fun x : Mom d => (1 + ‖x‖) ^ (-M)) c
        rw [h, invNormConst]

theorem integral_perp_one_add_norm_le {ℓ : Mom d} (hℓ : ℓ ≠ 0) {M : ℝ}
    (hM : (d : ℝ) - 1 < M) (hM0 : 0 ≤ M) (c : Mom d) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => (1 + ‖c + (w : Mom d)‖) ^ (-M)) ∧
      ∫ w : ↥(ℝ ∙ ℓ)ᗮ, (1 + ‖c + (w : Mom d)‖) ^ (-M) ≤ hypConst d M := by
  constructor
  · simpa using integrable_one_add_norm_slice hℓ hM hM0 c 0
  · simpa using integral_one_add_norm_slice_le hℓ hM hM0 c 0

/-- Hyperplane integral of a function dominated by a finite sum of decaying profiles. -/
theorem abs_integral_perp_le_sum {ℓ : Mom d} (hℓ : ℓ ≠ 0) {M : ℝ} (hM : (d : ℝ) - 1 < M)
    (hM0 : 0 ≤ M) {ι : Type*} (s : Finset ι) {A : ι → ℝ} (hA : ∀ i, 0 ≤ A i) {b : ι → Mom d}
    {G : ↥(ℝ ∙ ℓ)ᗮ → ℝ} (hG : ∀ w, |G w| ≤ ∑ i ∈ s, A i * (1 + ‖b i + (w : Mom d)‖) ^ (-M)) :
    |∫ w, G w| ≤ (∑ i ∈ s, A i) * hypConst d M := by
  have hint := fun i => ((integral_perp_one_add_norm_le hℓ hM hM0 (b i)).1).const_mul (A i)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_finsetSum s (fun i _ => hint i))
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hG w)).trans ?_
  rw [integral_finsetSum s (fun i _ => hint i), Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_perp_one_add_norm_le hℓ hM hM0 (b i)).2 (hA i)

/-- **Bound for `deltaInt`** of a kernel dominated by a finite sum of decaying profiles
(no measurability of `F` is needed). -/
theorem abs_deltaInt_le_sum (hd : 0 < d) {M : ℝ} (hM : (d : ℝ) - 1 < M) (hM0 : 0 ≤ M)
    {ι : Type*} (s : Finset ι) {A : ι → Mom d → ℝ} {b : ι → Mom d → Mom d}
    (hA : ∀ i ℓ, 0 ≤ A i ℓ) (hAi : ∀ i ∈ s, Integrable (fun ℓ : Mom d => ‖ℓ‖⁻¹ * A i ℓ))
    {F : Mom d → Mom d → ℝ}
    (hF : ∀ ℓ x, |F ℓ x| ≤ ∑ i ∈ s, A i ℓ * (1 + ‖b i ℓ + x‖) ^ (-M)) :
    |deltaInt F| ≤ hypConst d M / 2 * ∑ i ∈ s, ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * A i ℓ := by
  rw [deltaInt, ← Real.norm_eq_abs]
  have hg : Integrable (fun ℓ : Mom d => hypConst d M / 2 * ∑ i ∈ s, ‖ℓ‖⁻¹ * A i ℓ) :=
    (integrable_finsetSum s hAi).const_mul _
  refine (norm_integral_le_of_norm_le hg ?_).trans_eq ?_
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have h := abs_integral_perp_le_sum hℓ hM hM0 s (fun i => hA i ℓ) (b := fun i => b i ℓ)
      (G := fun w => F ℓ w) (fun w => hF ℓ w)
    calc (2 * ‖ℓ‖)⁻¹ * |∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ w|
        ≤ (2 * ‖ℓ‖)⁻¹ * ((∑ i ∈ s, A i ℓ) * hypConst d M) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = hypConst d M / 2 * ∑ i ∈ s, ‖ℓ‖⁻¹ * A i ℓ := by
          rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_inv]; ring
  · rw [integral_const_mul, integral_finsetSum s hAi]

/-! ### Weight splitting -/

theorem add_add_rpow_le {x y z s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hs : 0 ≤ s) :
    (x + y + z) ^ s ≤ 3 ^ s * (x ^ s + y ^ s + z ^ s) := by
  have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx s
  have hys : 0 ≤ y ^ s := Real.rpow_nonneg hy s
  have hzs : 0 ≤ z ^ s := Real.rpow_nonneg hz s
  have h3 : (0 : ℝ) ≤ 3 ^ s := by positivity
  have key : ∀ m, 0 ≤ m → x + y + z ≤ 3 * m → m ^ s ≤ x ^ s + y ^ s + z ^ s →
      (x + y + z) ^ s ≤ 3 ^ s * (x ^ s + y ^ s + z ^ s) := by
    intro m hm hle hms
    calc (x + y + z) ^ s ≤ (3 * m) ^ s :=
          Real.rpow_le_rpow (by positivity) hle hs
      _ = 3 ^ s * m ^ s := Real.mul_rpow (by norm_num) hm
      _ ≤ 3 ^ s * (x ^ s + y ^ s + z ^ s) := mul_le_mul_of_nonneg_left hms h3
  rcases le_total y x with hxy | hxy <;> rcases le_total z x with hxz | hxz <;>
    rcases le_total z y with hyz | hyz
  all_goals first
    | exact key x hx (by linarith) (by linarith)
    | exact key y hy (by linarith) (by linarith)
    | exact key z hz (by linarith) (by linarith)

/-- `(1 + |k₁ - k₂ + k₃|)^s ≤ 3^s Σᵢ (1 + |kᵢ|)^s`. -/
theorem one_add_norm_rpow_le_three (k₁ k₂ k₃ : Mom d) {s : ℝ} (hs : 0 ≤ s) :
    (1 + ‖k₁ - k₂ + k₃‖) ^ s ≤
      3 ^ s * ((1 + ‖k₁‖) ^ s + (1 + ‖k₂‖) ^ s + (1 + ‖k₃‖) ^ s) := by
  have h : 1 + ‖k₁ - k₂ + k₃‖ ≤ (1 + ‖k₁‖) + (1 + ‖k₂‖) + (1 + ‖k₃‖) := by
    have := norm_add_le (k₁ - k₂) k₃
    have := norm_sub_le k₁ k₂
    linarith
  exact (Real.rpow_le_rpow (by positivity) h hs).trans
    (add_add_rpow_le (by positivity) (by positivity) (by positivity) hs)

/-! ### The tame kernel bound -/

/-- The weight `(1 + |y|)^{-N}`. -/
@[expose] noncomputable def wt (N : ℝ) (y : Mom d) : ℝ := (1 + ‖y‖) ^ (-N)

theorem wt_nonneg (N : ℝ) (y : Mom d) : 0 ≤ wt N y := by unfold wt; positivity

theorem wt_mul_rpow (N : ℝ) (y : Mom d) : wt N y * (1 + ‖y‖) ^ N = 1 := by
  unfold wt; rw [← Real.rpow_add (by positivity)]; simp

theorem wt_anti {N N' : ℝ} (h : N' ≤ N) (y : Mom d) : wt N y ≤ wt N' y :=
  one_add_norm_rpow_neg_anti h

section Tame

variable {f₁ f₂ f₃ : Mom d → ℝ} {H₁ H₂ H₃ L₁ L₂ L₃ s s₀ : ℝ}

theorem DecayBound.rpow_mul_le {C N : ℝ} {φ : Mom d → ℝ} (h : DecayBound C N φ) (y : Mom d) :
    (1 + ‖y‖) ^ N * |φ y| ≤ C := by
  have hp : 0 < (1 + ‖y‖) ^ N := by positivity
  have h1 : |φ y| ≤ C * wt N y := h y
  calc (1 + ‖y‖) ^ N * |φ y| ≤ (1 + ‖y‖) ^ N * (C * wt N y) :=
        mul_le_mul_of_nonneg_left h1 hp.le
    _ = C * (wt N y * (1 + ‖y‖) ^ N) := by ring
    _ = C := by rw [wt_mul_rpow, mul_one]

theorem DecayBound.le_wt {C N : ℝ} {φ : Mom d → ℝ} (h : DecayBound C N φ) (y : Mom d) :
    |φ y| ≤ C * wt N y := h y

/-- The coefficients of the tame bound. -/
@[expose] noncomputable def tameA (k : Mom d) (s M H₁ H₂ H₃ L₁ L₂ L₃ : ℝ) (i : Fin 3)
    (ℓ : Mom d) : ℝ :=
  3 ^ s * wt s k *
    ![H₁ * L₂ * L₃ * wt M ℓ, L₁ * H₂ * L₃ * wt M (k + ℓ), L₁ * L₂ * H₃ * wt M (k + ℓ)] i

/-- The shifts of the tame bound. -/
@[expose] def tameB (k : Mom d) (i : Fin 3) (ℓ : Mom d) : Mom d := ![k, k, k + ℓ] i

/-- The pointwise tame bound, for each of the four kernels. -/
theorem abs_collisionKernel_le_tame (hs : 0 ≤ s) (hs₀ : 0 ≤ s₀)
    (hH₁ : DecayBound H₁ s f₁) (hH₂ : DecayBound H₂ s f₂) (hH₃ : DecayBound H₃ s f₃)
    (hL₁ : DecayBound L₁ s₀ f₁) (hL₂ : DecayBound L₂ s₀ f₂) (hL₃ : DecayBound L₃ s₀ f₃)
    (j : Fin 4) (k ℓ x : Mom d) :
    |collisionKernel j f₁ f₂ f₃ k ℓ x| ≤
      ∑ i : Fin 3, tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ *
        (1 + ‖tameB k i ℓ + x‖) ^ (-(s₀ / 2)) := by
  have hH₁0 := hH₁.C_nonneg; have hH₂0 := hH₂.C_nonneg; have hH₃0 := hH₃.C_nonneg
  have hL₁0 := hL₁.C_nonneg; have hL₂0 := hL₂.C_nonneg; have hL₃0 := hL₃.C_nonneg
  have hk : (k + ℓ) - (k + ℓ + x) + (k + x) = k := by abel
  have hP : wt s₀ (k + ℓ + x) * wt s₀ (k + x) ≤ wt (s₀ / 2) ℓ * wt (s₀ / 2) (k + x) := by
    have h := one_add_norm_rpow_neg_mul_le (k + x) ℓ hs₀
    have e : k + x + ℓ = k + ℓ + x := by abel
    rw [e] at h; exact h
  have hQ : wt s₀ (k + ℓ) * wt s₀ (k + x) ≤ wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + x) :=
    mul_le_mul (wt_anti (by linarith) _) (wt_anti (by linarith) _) (wt_nonneg _ _)
      (wt_nonneg _ _)
  have hR : wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x) ≤
      wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + ℓ + x) :=
    mul_le_mul (wt_anti (by linarith) _) (wt_anti (by linarith) _) (wt_nonneg _ _)
      (wt_nonneg _ _)
  have hRHS : ∑ i : Fin 3, tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ *
        (1 + ‖tameB k i ℓ + x‖) ^ (-(s₀ / 2)) =
      3 ^ s * wt s k * (H₁ * L₂ * L₃ * (wt (s₀ / 2) ℓ * wt (s₀ / 2) (k + x))
        + L₁ * H₂ * L₃ * (wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + x))
        + L₁ * L₂ * H₃ * (wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + ℓ + x))) := by
    simp only [Fin.sum_univ_three, tameA, tameB, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [wt]
    ring
  rw [hRHS]
  have h3 : (1 : ℝ) ≤ 3 ^ s := Real.one_le_rpow (by norm_num) hs
  have hWk := wt_nonneg s k
  have w1 := wt_nonneg (s₀ / 2) ℓ; have w2 := wt_nonneg (s₀ / 2) (k + ℓ)
  have w3 := wt_nonneg (s₀ / 2) (k + x); have w4 := wt_nonneg (s₀ / 2) (k + ℓ + x)
  have t1 : 0 ≤ H₁ * L₂ * L₃ * (wt (s₀ / 2) ℓ * wt (s₀ / 2) (k + x)) := by positivity
  have t2 : 0 ≤ L₁ * H₂ * L₃ * (wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + x)) := by positivity
  have t3 : 0 ≤ L₁ * L₂ * H₃ * (wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + ℓ + x)) := by
    positivity
  set T₁ := H₁ * L₂ * L₃ * (wt (s₀ / 2) ℓ * wt (s₀ / 2) (k + x))
  set T₂ := L₁ * H₂ * L₃ * (wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + x))
  set T₃ := L₁ * L₂ * H₃ * (wt (s₀ / 2) (k + ℓ) * wt (s₀ / 2) (k + ℓ + x))
  have v1 := wt_nonneg s₀ (k + ℓ); have v2 := wt_nonneg s₀ (k + ℓ + x)
  have v3 := wt_nonneg s₀ (k + x)
  fin_cases j
  · -- gain term: split the weight `(1 + |k|)^s` among the three inputs
    show |f₁ (k + ℓ) * f₂ (k + ℓ + x) * f₃ (k + x)| ≤ _
    have a₁ := hH₁.rpow_mul_le (k + ℓ)
    have a₂ := hH₂.rpow_mul_le (k + ℓ + x)
    have a₃ := hH₃.rpow_mul_le (k + x)
    have b₁ := hL₁.le_wt (k + ℓ); have b₂ := hL₂.le_wt (k + ℓ + x)
    have b₃ := hL₃.le_wt (k + x)
    have hsplit := one_add_norm_rpow_le_three (k + ℓ) (k + ℓ + x) (k + x) hs
    rw [hk] at hsplit
    rw [abs_mul, abs_mul]
    have hF₁ := abs_nonneg (f₁ (k + ℓ)); have hF₂ := abs_nonneg (f₂ (k + ℓ + x))
    have hF₃ := abs_nonneg (f₃ (k + x))
    have hA₁ : 0 ≤ (1 + ‖k + ℓ‖) ^ s := by positivity
    have hA₂ : 0 ≤ (1 + ‖k + ℓ + x‖) ^ s := by positivity
    have hA₃ : 0 ≤ (1 + ‖k + x‖) ^ s := by positivity
    have step1 : (1 + ‖k‖) ^ s * (|f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * |f₃ (k + x)|) ≤
        3 ^ s * (H₁ * L₂ * L₃ * (wt s₀ (k + ℓ + x) * wt s₀ (k + x))
          + L₁ * H₂ * L₃ * (wt s₀ (k + ℓ) * wt s₀ (k + x))
          + L₁ * L₂ * H₃ * (wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x))) := by
      calc (1 + ‖k‖) ^ s * (|f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * |f₃ (k + x)|)
          ≤ 3 ^ s * ((1 + ‖k + ℓ‖) ^ s + (1 + ‖k + ℓ + x‖) ^ s + (1 + ‖k + x‖) ^ s) *
              (|f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * |f₃ (k + x)|) :=
            mul_le_mul_of_nonneg_right hsplit (by positivity)
        _ = 3 ^ s * (((1 + ‖k + ℓ‖) ^ s * |f₁ (k + ℓ)|) * |f₂ (k + ℓ + x)| * |f₃ (k + x)|
              + |f₁ (k + ℓ)| * ((1 + ‖k + ℓ + x‖) ^ s * |f₂ (k + ℓ + x)|) * |f₃ (k + x)|
              + |f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * ((1 + ‖k + x‖) ^ s * |f₃ (k + x)|)) := by
            ring
        _ ≤ 3 ^ s * (H₁ * (L₂ * wt s₀ (k + ℓ + x)) * (L₃ * wt s₀ (k + x))
              + (L₁ * wt s₀ (k + ℓ)) * H₂ * (L₃ * wt s₀ (k + x))
              + (L₁ * wt s₀ (k + ℓ)) * (L₂ * wt s₀ (k + ℓ + x)) * H₃) := by
            gcongr
        _ = _ := by ring
    have step2 : 3 ^ s * (H₁ * L₂ * L₃ * (wt s₀ (k + ℓ + x) * wt s₀ (k + x))
          + L₁ * H₂ * L₃ * (wt s₀ (k + ℓ) * wt s₀ (k + x))
          + L₁ * L₂ * H₃ * (wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x))) ≤ 3 ^ s * (T₁ + T₂ + T₃) := by
      have h30 : (0 : ℝ) ≤ 3 ^ s := by positivity
      gcongr
      · exact mul_le_mul_of_nonneg_left hP (by positivity)
      · exact mul_le_mul_of_nonneg_left hQ (by positivity)
      · exact mul_le_mul_of_nonneg_left hR (by positivity)
    calc |f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * |f₃ (k + x)|
        = wt s k * ((1 + ‖k‖) ^ s * (|f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * |f₃ (k + x)|)) := by
          rw [← mul_assoc, wt_mul_rpow, one_mul]
      _ ≤ wt s k * (3 ^ s * (T₁ + T₂ + T₃)) :=
          mul_le_mul_of_nonneg_left (step1.trans step2) hWk
      _ = _ := by ring
  · -- `φ₁(k) φ₂(k+ℓ+x) φ₃(k+x)`
    show |f₁ k * f₂ (k + ℓ + x) * f₃ (k + x)| ≤ _
    rw [abs_mul, abs_mul]
    have a := hH₁.le_wt k
    have b₂ := hL₂.le_wt (k + ℓ + x); have b₃ := hL₃.le_wt (k + x)
    calc |f₁ k| * |f₂ (k + ℓ + x)| * |f₃ (k + x)|
        ≤ (H₁ * wt s k) * (L₂ * wt s₀ (k + ℓ + x)) * (L₃ * wt s₀ (k + x)) := by
          gcongr
      _ = wt s k * (H₁ * L₂ * L₃ * (wt s₀ (k + ℓ + x) * wt s₀ (k + x))) := by ring
      _ ≤ wt s k * T₁ :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (by positivity)) hWk
      _ ≤ wt s k * (T₁ + T₂ + T₃) := mul_le_mul_of_nonneg_left (by linarith) hWk
      _ ≤ 3 ^ s * wt s k * (T₁ + T₂ + T₃) := by
          rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) h3
  · -- `φ₁(k+ℓ) φ₂(k) φ₃(k+x)`
    show |f₁ (k + ℓ) * f₂ k * f₃ (k + x)| ≤ _
    rw [abs_mul, abs_mul]
    have a := hH₂.le_wt k
    have b₁ := hL₁.le_wt (k + ℓ); have b₃ := hL₃.le_wt (k + x)
    calc |f₁ (k + ℓ)| * |f₂ k| * |f₃ (k + x)|
        ≤ (L₁ * wt s₀ (k + ℓ)) * (H₂ * wt s k) * (L₃ * wt s₀ (k + x)) := by
          gcongr
      _ = wt s k * (L₁ * H₂ * L₃ * (wt s₀ (k + ℓ) * wt s₀ (k + x))) := by ring
      _ ≤ wt s k * T₂ :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (by positivity)) hWk
      _ ≤ wt s k * (T₁ + T₂ + T₃) := mul_le_mul_of_nonneg_left (by linarith) hWk
      _ ≤ 3 ^ s * wt s k * (T₁ + T₂ + T₃) := by
          rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) h3
  · -- `φ₁(k+ℓ) φ₂(k+ℓ+x) φ₃(k)`
    show |f₁ (k + ℓ) * f₂ (k + ℓ + x) * f₃ k| ≤ _
    rw [abs_mul, abs_mul]
    have a := hH₃.le_wt k
    have b₁ := hL₁.le_wt (k + ℓ); have b₂ := hL₂.le_wt (k + ℓ + x)
    calc |f₁ (k + ℓ)| * |f₂ (k + ℓ + x)| * |f₃ k|
        ≤ (L₁ * wt s₀ (k + ℓ)) * (L₂ * wt s₀ (k + ℓ + x)) * (H₃ * wt s k) := by
          gcongr
      _ = wt s k * (L₁ * L₂ * H₃ * (wt s₀ (k + ℓ) * wt s₀ (k + ℓ + x))) := by ring
      _ ≤ wt s k * T₃ :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (by positivity)) hWk
      _ ≤ wt s k * (T₁ + T₂ + T₃) := mul_le_mul_of_nonneg_left (by linarith) hWk
      _ ≤ 3 ^ s * wt s k * (T₁ + T₂ + T₃) := by
          rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) h3

theorem tameA_eq (k : Mom d) (s M H₁ H₂ H₃ L₁ L₂ L₃ : ℝ) (i : Fin 3) (ℓ : Mom d) :
    tameA k s M H₁ H₂ H₃ L₁ L₂ L₃ i ℓ =
      3 ^ s * wt s k * ![H₁ * L₂ * L₃, L₁ * H₂ * L₃, L₁ * L₂ * H₃] i *
        wt M (![0, k, k] i + ℓ) := by
  fin_cases i <;> simp [tameA] <;> ring

/-- The constant of the tame estimate. -/
@[expose] noncomputable def tameConst (d : ℕ) (s₀ : ℝ) : ℝ :=
  hypConst d (s₀ / 2) / 2 * invNormConst d (s₀ / 2)

theorem integrable_inv_norm_mul_wt (hd : 2 ≤ d) {M : ℝ} (hM : (d : ℝ) < M) (c : Mom d) :
    Integrable (fun ℓ : Mom d => ‖ℓ‖⁻¹ * wt M (c + ℓ)) :=
  integrable_inv_norm_mul_one_add_norm hd hM c

theorem integral_inv_norm_mul_wt_le (hd : 2 ≤ d) {M : ℝ} (hM : (d : ℝ) < M) (c : Mom d) :
    ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * wt M (c + ℓ) ≤ invNormConst d M :=
  integral_inv_norm_mul_one_add_norm_le hd hM c

/-- The kernel bound, integrated: the right-hand side of the tame estimate. -/
theorem abs_deltaInt_le_tame (hd : 2 ≤ d) (hs₀ : 2 * (d : ℝ) < s₀)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂) (hH₃ : 0 ≤ H₃) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃)
    (k : Mom d) {c : ℝ} (hc : 0 ≤ c) {F : Mom d → Mom d → ℝ}
    (hF : ∀ ℓ x, |F ℓ x| ≤ ∑ i : Fin 3, c * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ *
        (1 + ‖tameB k i ℓ + x‖) ^ (-(s₀ / 2))) :
    (1 + ‖k‖) ^ s * |deltaInt F| ≤
      c * (tameConst d s₀ * 3 ^ s * (H₁ * L₂ * L₃ + L₁ * H₂ * L₃ + L₁ * L₂ * H₃)) := by
  have hM : (d : ℝ) < s₀ / 2 := by linarith
  have hM1 : (d : ℝ) - 1 < s₀ / 2 := by linarith
  have hM0 : 0 ≤ s₀ / 2 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hcoef : ∀ i : Fin 3, 0 ≤ ![H₁ * L₂ * L₃, L₁ * H₂ * L₃, L₁ * L₂ * H₃] i := by
    intro i; fin_cases i <;> simp <;> positivity
  have hWk := wt_nonneg s k
  have hA : ∀ (i : Fin 3) ℓ, 0 ≤ c * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ := by
    intro i ℓ
    rw [tameA_eq]
    have := hcoef i; have := wt_nonneg (s₀ / 2) (![0, k, k] i + ℓ)
    positivity
  have hAeq : ∀ (i : Fin 3) (ℓ : Mom d), ‖ℓ‖⁻¹ * (c * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ) =
      (c * (3 ^ s * wt s k * ![H₁ * L₂ * L₃, L₁ * H₂ * L₃, L₁ * L₂ * H₃] i)) *
        (‖ℓ‖⁻¹ * wt (s₀ / 2) (![0, k, k] i + ℓ)) := by
    intro i ℓ; rw [tameA_eq]; ring
  have hAi : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun ℓ : Mom d =>
      ‖ℓ‖⁻¹ * (c * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ)) := by
    intro i _
    simp_rw [hAeq]
    exact (integrable_inv_norm_mul_wt hd hM _).const_mul _
  have hmain := abs_deltaInt_le_sum (by omega) hM1 hM0 Finset.univ hA hAi hF
  have hsum : ∑ i : Fin 3, ∫ ℓ : Mom d, ‖ℓ‖⁻¹ * (c * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ)
      ≤ c * (3 ^ s * wt s k * (H₁ * L₂ * L₃ + L₁ * H₂ * L₃ + L₁ * L₂ * H₃)) *
          invNormConst d (s₀ / 2) := by
    have hterm : ∀ i : Fin 3, ∫ ℓ : Mom d,
        ‖ℓ‖⁻¹ * (c * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ) ≤
        c * (3 ^ s * wt s k * ![H₁ * L₂ * L₃, L₁ * H₂ * L₃, L₁ * L₂ * H₃] i) *
          invNormConst d (s₀ / 2) := by
      intro i
      simp_rw [hAeq]
      rw [integral_const_mul]
      have := hcoef i
      exact mul_le_mul_of_nonneg_left (integral_inv_norm_mul_wt_le hd hM _) (by positivity)
    refine (Finset.sum_le_sum fun i _ => hterm i).trans_eq ?_
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hhyp := hypConst_nonneg d (s₀ / 2)
  calc (1 + ‖k‖) ^ s * |deltaInt F|
      ≤ (1 + ‖k‖) ^ s * (hypConst d (s₀ / 2) / 2 *
          (c * (3 ^ s * wt s k * (H₁ * L₂ * L₃ + L₁ * H₂ * L₃ + L₁ * L₂ * H₃)) *
            invNormConst d (s₀ / 2))) := by
        refine mul_le_mul_of_nonneg_left (hmain.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c * (tameConst d s₀ * 3 ^ s * (H₁ * L₂ * L₃ + L₁ * H₂ * L₃ + L₁ * L₂ * H₃)) *
          (wt s k * (1 + ‖k‖) ^ s) := by rw [tameConst]; ring
    _ = _ := by rw [wt_mul_rpow, mul_one]

/-- **Tame trilinear estimate for each term `𝒦ⱼ`** (weighted-`L^∞` form of TARGET (schappend8),
L2513–L2516; cf. the `L^∞_s` estimate of GIT20 Prop. `PropLinfty`, Kin8.tex L571–L577).
For `d ≥ 2`, `s₀ > 2d`, `s ≥ 0`,
`|fᵢ| ≤ Hᵢ (1+|y|)^{-s}` and `|fᵢ| ≤ Lᵢ (1+|y|)^{-s₀}`:
`(1+|k|)^s |𝒦ⱼ(f₁,f₂,f₃)(k)| ≤ tameConst d s₀ · 3^s · (H₁L₂L₃ + L₁H₂L₃ + L₁L₂H₃)`. -/
theorem abs_collisionTerm_le_tame (hd : 2 ≤ d) (hs₀ : 2 * (d : ℝ) < s₀) (hs : 0 ≤ s)
    (hH₁ : DecayBound H₁ s f₁) (hH₂ : DecayBound H₂ s f₂) (hH₃ : DecayBound H₃ s f₃)
    (hL₁ : DecayBound L₁ s₀ f₁) (hL₂ : DecayBound L₂ s₀ f₂) (hL₃ : DecayBound L₃ s₀ f₃)
    (j : Fin 4) (k : Mom d) :
    (1 + ‖k‖) ^ s * |collisionTerm j f₁ f₂ f₃ k| ≤
      tameConst d s₀ * 3 ^ s * (H₁ * L₂ * L₃ + L₁ * H₂ * L₃ + L₁ * L₂ * H₃) := by
  have hs₀' : 0 ≤ s₀ := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h := abs_deltaInt_le_tame (F := collisionKernel j f₁ f₂ f₃ k) hd hs₀ hH₁.C_nonneg
    hH₂.C_nonneg hH₃.C_nonneg hL₁.C_nonneg hL₂.C_nonneg hL₃.C_nonneg k zero_le_one
    (fun ℓ x => by
      simpa only [one_mul] using
        abs_collisionKernel_le_tame hs hs₀' hH₁ hH₂ hH₃ hL₁ hL₂ hL₃ j k ℓ x)
  simpa only [one_mul, collisionTerm] using h

theorem abs_sub_add_sub_le (a b c e : ℝ) : |a - b + c - e| ≤ |a| + |b| + |c| + |e| := by
  have h1 := abs_add_le (a - b + c) (-e)
  have h2 := abs_add_le (a - b) c
  have h3 := abs_add_le a (-b)
  simp only [abs_neg, ← sub_eq_add_neg] at h1 h3
  linarith

/-- **Tame trilinear estimate for `𝒦 = collisionOp`.** -/
theorem abs_collisionOp_le_tame (hd : 2 ≤ d) (hs₀ : 2 * (d : ℝ) < s₀) (hs : 0 ≤ s)
    (hH₁ : DecayBound H₁ s f₁) (hH₂ : DecayBound H₂ s f₂) (hH₃ : DecayBound H₃ s f₃)
    (hL₁ : DecayBound L₁ s₀ f₁) (hL₂ : DecayBound L₂ s₀ f₂) (hL₃ : DecayBound L₃ s₀ f₃)
    (k : Mom d) :
    (1 + ‖k‖) ^ s * |collisionOp f₁ f₂ f₃ k| ≤
      4 * (tameConst d s₀ * 3 ^ s * (H₁ * L₂ * L₃ + L₁ * H₂ * L₃ + L₁ * L₂ * H₃)) := by
  have hs₀' : 0 ≤ s₀ := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  rw [collisionOp_eq_deltaInt]
  refine abs_deltaInt_le_tame hd hs₀ hH₁.C_nonneg hH₂.C_nonneg hH₃.C_nonneg hL₁.C_nonneg
    hL₂.C_nonneg hL₃.C_nonneg k (by norm_num) (fun ℓ x => ?_)
  have b := fun j => abs_collisionKernel_le_tame hs hs₀' hH₁ hH₂ hH₃ hL₁ hL₂ hL₃ j k ℓ x
  rw [collisionIntegrand_eq]
  have e : ∑ i : Fin 3, 4 * tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ *
      (1 + ‖tameB k i ℓ + x‖) ^ (-(s₀ / 2)) = 4 * ∑ i : Fin 3,
        tameA k s (s₀ / 2) H₁ H₂ H₃ L₁ L₂ L₃ i ℓ * (1 + ‖tameB k i ℓ + x‖) ^ (-(s₀ / 2)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  have t := abs_sub_add_sub_le (collisionKernel 0 f₁ f₂ f₃ k ℓ x)
    (collisionKernel 1 f₁ f₂ f₃ k ℓ x) (collisionKernel 2 f₁ f₂ f₃ k ℓ x)
    (collisionKernel 3 f₁ f₂ f₃ k ℓ x)
  linarith [b 0, b 1, b 2, b 3]

/-- **Trilinear estimate in `L^∞_s`, `s > 2d`.** If `|fᵢ(y)| ≤ Cᵢ (1+|y|)^{-s}` then
`(1+|k|)^s |𝒦ⱼ(f₁,f₂,f₃)(k)| ≤ 3^{s+1} tameConst d s · C₁C₂C₃`. -/
theorem abs_collisionTerm_le (hd : 2 ≤ d) (hs : 2 * (d : ℝ) < s) {C₁ C₂ C₃ : ℝ}
    (h₁ : DecayBound C₁ s f₁) (h₂ : DecayBound C₂ s f₂) (h₃ : DecayBound C₃ s f₃)
    (j : Fin 4) (k : Mom d) :
    (1 + ‖k‖) ^ s * |collisionTerm j f₁ f₂ f₃ k| ≤ 3 * tameConst d s * 3 ^ s * (C₁ * C₂ * C₃) := by
  have hs0 : 0 ≤ s := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h := abs_collisionTerm_le_tame hd hs hs0 h₁ h₂ h₃ h₁ h₂ h₃ j k
  linarith

end Tame

end WaveTurbulence
