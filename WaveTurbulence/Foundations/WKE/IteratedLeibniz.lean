/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.SchwartzValued
public import WaveTurbulence.Foundations.WKE.MaxSplit

/-!
# The iterated Leibniz rule and multiplicative bounds

* `iteratedLineDerivOp_ktriple`: TARGET (schappend6) iterated (L2508, "can be iterated to get
  corresponding equalities for multi-indices"): for directions `m : Fin r → ℝ^d`,
  `∂^m 𝒦ⱼ(F₀,F₁,F₂) = Σ_{σ : Fin r → Fin 3} 𝒦ⱼ(distr m σ F)`, where `distr m σ F` applies the
  derivative `∂_{m t}` to the input `σ t`.
* `MultBound R W s₀ μ Y X f`: `(1 + |y|)^{w+s₀} ‖Dʳf(y)‖ ≤ (μY)^{r+w} X` for `r ≤ R`, `w ≤ W`.
* `multBound_ktriple`: if `Fᵢ` satisfies `MultBound … μᵢ Y Xᵢ` then `𝒦ⱼ(F)` satisfies
  `MultBound … (μ₁+μ₂+μ₃) Y (A X₁X₂X₃)` with `A = 9·3^{s₀}·tameConst d s₀`, **independent of
  `R, W`**. This is the inductive step of the Taylor bound (FINDINGS F10).
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace SchwartzMap LineDeriv Finset

namespace WaveTurbulence.WKE

variable {d : ℕ}

/-- `𝒦ⱼ(F₀, F₁, F₂)` for a triple of Schwartz functions. -/
@[expose] noncomputable def ktriple (hd : 2 ≤ d) (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)) :
    𝓢(Mom d, ℝ) :=
  collisionTermSchwartz hd j (F 0) (F 1) (F 2)

theorem coe_ktriple (hd : 2 ≤ d) (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)) :
    ⇑(ktriple hd j F) = collisionTerm j (F 0) (F 1) (F 2) := rfl

/-- Distribute the directional derivatives `∂_{m t}` to the inputs `σ t`. -/
@[expose] noncomputable def distr : {n : ℕ} → (Fin n → Mom d) → (Fin n → Fin 3) →
    (Fin 3 → 𝓢(Mom d, ℝ)) → Fin 3 → 𝓢(Mom d, ℝ)
  | 0, _, _, F => F
  | _ + 1, m, σ, F =>
    Function.update (distr (Fin.tail m) (Fin.tail σ) F) (σ 0)
      (∂_{m 0} (distr (Fin.tail m) (Fin.tail σ) F (σ 0)))

theorem lineDerivOp_ktriple (hd : 2 ≤ d) (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)) (v : Mom d) :
    ∂_{v} (ktriple hd j F) = ∑ i : Fin 3, ktriple hd j (Function.update F i (∂_{v} (F i))) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, coe_ktriple, fderiv_collisionTerm hd]
  simp only [Fin.sum_univ_three, add_apply, coe_ktriple]
  simp [Function.update, partialSchwartz]

theorem sum_fin_succ_fun {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin (n + 1) → Fin 3) → M) :
    ∑ σ : Fin (n + 1) → Fin 3, g σ = ∑ i : Fin 3, ∑ σ' : Fin n → Fin 3, g (Fin.cons i σ') := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **Iterated Leibniz rule** for `𝒦ⱼ` on Schwartz functions. -/
theorem iteratedLineDerivOp_ktriple (hd : 2 ≤ d) (j : Fin 4) (F : Fin 3 → 𝓢(Mom d, ℝ)) :
    ∀ {n : ℕ} (m : Fin n → Mom d),
      ∂^{m} (ktriple hd j F) = ∑ σ : Fin n → Fin 3, ktriple hd j (distr m σ F)
  | 0, m => by simp [distr]
  | n + 1, m => by
      rw [LineDeriv.iteratedLineDerivOp_succ_left, iteratedLineDerivOp_ktriple hd j F (Fin.tail m),
        LineDeriv.lineDerivOp_sum, sum_fin_succ_fun, Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ' _ => ?_
      rw [lineDerivOp_ktriple]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [distr, Fin.tail_cons, Fin.cons_zero]

/-! ### Each distributed input is an iterated derivative of the original one -/

theorem card_filter_fin_succ {n : ℕ} (σ : Fin (n + 1) → Fin 3) (i : Fin 3) :
    #{t | σ t = i} = (if σ 0 = i then 1 else 0) + #{t | Fin.tail σ t = i} := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  rfl

theorem prod_filter_fin_succ {n : ℕ} (σ : Fin (n + 1) → Fin 3) (i : Fin 3)
    (f : Fin (n + 1) → ℝ) :
    ∏ t ∈ Finset.univ.filter (fun t => σ t = i), f t =
      (if σ 0 = i then f 0 else 1) *
        ∏ t ∈ Finset.univ.filter (fun t => Fin.tail σ t = i), f (Fin.succ t) := by
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
  rfl

theorem distr_eq_iteratedLineDerivOp : ∀ {n : ℕ} (m : Fin n → Mom d) (σ : Fin n → Fin 3)
    (F : Fin 3 → 𝓢(Mom d, ℝ)) (i : Fin 3), ∃ (c : ℕ) (m' : Fin c → Mom d),
      c = #{t | σ t = i} ∧ distr m σ F i = ∂^{m'} (F i) ∧
        ∏ t, ‖m' t‖ = ∏ t ∈ Finset.univ.filter (fun t => σ t = i), ‖m t‖
  | 0, m, σ, F, i => ⟨0, Fin.elim0, by simp, rfl, by simp⟩
  | n + 1, m, σ, F, i => by
      obtain ⟨c, m', hc, h1, h2⟩ := distr_eq_iteratedLineDerivOp (Fin.tail m) (Fin.tail σ) F i
      by_cases hi : σ 0 = i
      · refine ⟨c + 1, Fin.cons (m 0) m', ?_, ?_, ?_⟩
        · rw [card_filter_fin_succ, ite_eq_left hi, hc]; ring
        · simp only [distr]
          rw [← hi, Function.update_self, hi, h1, LineDeriv.iteratedLineDerivOp_succ_left,
            Fin.cons_zero, Fin.tail_cons]
        · rw [Fin.prod_univ_succ, Fin.cons_zero, prod_filter_fin_succ, ite_eq_left hi]
          simp only [Fin.cons_succ]
          rw [h2]
          rfl
      · refine ⟨c, m', ?_, ?_, ?_⟩
        · rw [card_filter_fin_succ, ite_eq_right hi, hc, zero_add]
        · simp only [distr]
          rw [Function.update_of_ne (Ne.symm hi), h1]
        · rw [prod_filter_fin_succ, ite_eq_right hi, one_mul, h2]
          rfl

theorem abs_distr_le {n : ℕ} (m : Fin n → Mom d) (σ : Fin n → Fin 3) (F : Fin 3 → 𝓢(Mom d, ℝ))
    (i : Fin 3) (y : Mom d) :
    |distr m σ F i y| ≤ ‖iteratedFDeriv ℝ #{t | σ t = i} (F i) y‖ *
      ∏ t ∈ Finset.univ.filter (fun t => σ t = i), ‖m t‖ := by
  obtain ⟨c, m', hc, h1, h2⟩ := distr_eq_iteratedLineDerivOp m σ F i
  subst hc
  rw [h1, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, ← h2, ← Real.norm_eq_abs]
  exact ContinuousMultilinearMap.le_opNorm _ m'

/-! ### Multiplicative bounds -/

/-- `(1 + |y|)^{w+s₀} ‖Dʳ f(y)‖ ≤ (μ Y)^{r+w} X` for all `r ≤ R`, `w ≤ W`. -/
@[expose] def MultBound (R W : ℕ) (s₀ μ Y X : ℝ) (f : 𝓢(Mom d, ℝ)) : Prop :=
  ∀ r ≤ R, ∀ w ≤ W, ∀ y : Mom d,
    (1 + ‖y‖) ^ ((w : ℝ) + s₀) * ‖iteratedFDeriv ℝ r f y‖ ≤ (μ * Y) ^ (r + w) * X

/-- The constant of the multiplicative step. -/
@[expose] noncomputable def multConst (d : ℕ) (s₀ : ℝ) : ℝ := 9 * 3 ^ s₀ * tameConst d s₀

theorem multConst_nonneg (d : ℕ) (s₀ : ℝ) : 0 ≤ multConst d s₀ := by
  unfold multConst; have := tameConst_nonneg d s₀; positivity

theorem sum_card_filter_fin3 {n : ℕ} (σ : Fin n → Fin 3) :
    #{t | σ t = 0} + #{t | σ t = 1} + #{t | σ t = 2} = n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := σ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three] at h
  simpa using h.symm

theorem prod_fin3_fiberwise {n : ℕ} (σ : Fin n → Fin 3) (f : Fin n → ℝ) :
    (∏ t ∈ Finset.univ.filter (fun t => σ t = 0), f t) *
      (∏ t ∈ Finset.univ.filter (fun t => σ t = 1), f t) *
        (∏ t ∈ Finset.univ.filter (fun t => σ t = 2), f t) = ∏ t, f t := by
  have h := Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := σ)
    (fun _ _ => Finset.mem_univ _) f
  rw [Fin.prod_univ_three] at h
  simpa using h

theorem prod_pow_card_fin3 {n : ℕ} (σ : Fin n → Fin 3) (μ : Fin 3 → ℝ) :
    μ 0 ^ #{t | σ t = 0} * μ 1 ^ #{t | σ t = 1} * μ 2 ^ #{t | σ t = 2} = ∏ t, μ (σ t) := by
  have h := Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.univ) (g := σ)
    (fun _ _ => Finset.mem_univ _) μ
  rw [Fin.prod_univ_three] at h
  simp only [Finset.prod_const] at h
  simpa using h

theorem sum_prod_fin3 (n : ℕ) (μ : Fin 3 → ℝ) :
    ∑ σ : Fin n → Fin 3, ∏ t, μ (σ t) = (μ 0 + μ 1 + μ 2) ^ n := by
  rw [← Fin.sum_univ_three, Finset.sum_pow']
  simp

theorem MultBound.nonneg {R W : ℕ} {s₀ μ Y X : ℝ} {f : 𝓢(Mom d, ℝ)}
    (h : MultBound R W s₀ μ Y X f) : 0 ≤ X := by
  have := h 0 (Nat.zero_le _) 0 (Nat.zero_le _) 0
  have e : (μ * Y) ^ (0 + 0) * X = X := by simp
  rw [e] at this
  exact (mul_nonneg (by positivity) (norm_nonneg _)).trans this

theorem MultBound.le_wt {R W : ℕ} {s₀ μ Y X : ℝ} {f : 𝓢(Mom d, ℝ)}
    (h : MultBound R W s₀ μ Y X f) {r w : ℕ} (hr : r ≤ R) (hw : w ≤ W) (y : Mom d) :
    ‖iteratedFDeriv ℝ r f y‖ ≤ (μ * Y) ^ (r + w) * X * wt ((w : ℝ) + s₀) y :=
  le_of_weighted y (h r hr w hw y)

/-- **The multiplicative step.** If each input satisfies `MultBound R W s₀ μᵢ Y Xᵢ`, then
`𝒦ⱼ(F)` satisfies `MultBound R W s₀ (μ₀+μ₁+μ₂) Y (multConst d s₀ · X₀X₁X₂)`; the constant does not
depend on `R` or `W`. -/
theorem multBound_ktriple (hd : 2 ≤ d) {R W : ℕ} {s₀ Y : ℝ} (hs₀ : 2 * (d : ℝ) < s₀)
    (hY : 0 ≤ Y) {μ X : Fin 3 → ℝ} (hμ : ∀ i, 0 < μ i) {F : Fin 3 → 𝓢(Mom d, ℝ)}
    (hF : ∀ i, MultBound R W s₀ (μ i) Y (X i) (F i)) (j : Fin 4) :
    MultBound R W s₀ (μ 0 + μ 1 + μ 2) Y (multConst d s₀ * (X 0 * X 1 * X 2))
      (ktriple hd j F) := by
  intro r hr w hw y
  have hs₀' : 0 ≤ s₀ := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hX : ∀ i, 0 ≤ X i := fun i => (hF i).nonneg
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => (hμ i).le
  set μs := μ 0 + μ 1 + μ 2
  have hμs : 0 < μs := by have := hμ 0; have := hμ 1; have := hμ 2; positivity
  set B := (μs * Y) ^ (r + w) * (multConst d s₀ * (X 0 * X 1 * X 2))
  have hB : 0 ≤ B := by
    have := multConst_nonneg d s₀; have := hX 0; have := hX 1; have := hX 2; positivity
  suffices hop : ‖iteratedFDeriv ℝ r (ktriple hd j F) y‖ ≤ B * wt ((w : ℝ) + s₀) y by
    calc (1 + ‖y‖) ^ ((w : ℝ) + s₀) * ‖iteratedFDeriv ℝ r (ktriple hd j F) y‖
        ≤ (1 + ‖y‖) ^ ((w : ℝ) + s₀) * (B * wt ((w : ℝ) + s₀) y) :=
          mul_le_mul_of_nonneg_left hop (by positivity)
      _ = B * (wt ((w : ℝ) + s₀) y * (1 + ‖y‖) ^ ((w : ℝ) + s₀)) := by ring
      _ = B := by rw [wt_mul_rpow, mul_one]
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg hB (wt_nonneg _ _)) fun m => ?_
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_ktriple hd j F m,
    sum_apply]
  refine (norm_sum_le _ _).trans ?_
  -- the bound for each distribution `σ`
  have hterm : ∀ σ : Fin r → Fin 3, ‖ktriple hd j (distr m σ F) y‖ ≤
      multConst d s₀ * μs ^ w * Y ^ (r + w) * (X 0 * X 1 * X 2) * (∏ t, ‖m t‖) *
        (∏ t, μ (σ t)) * wt ((w : ℝ) + s₀) y := by
    intro σ
    set c := fun i => #{t | σ t = i}
    set P := fun i => ∏ t ∈ Finset.univ.filter (fun t => σ t = i), ‖m t‖
    have hP : ∀ i, 0 ≤ P i := fun i => Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hc : ∀ i, c i ≤ r := fun i => by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin r)) (fun t => σ t = i)
    have hHigh : ∀ i, HighBound (w : ℝ) s₀ (μ i)
        (μ i ^ c i * Y ^ (c i + w) * X i * P i) (distr m σ F i) := by
      intro i z
      have h1 := abs_distr_le m σ F i z
      have h2 := hF i (c i) ((hc i).trans hr) w hw z
      have hz : 0 ≤ (1 + ‖z‖) ^ ((w : ℝ) + s₀) := by positivity
      calc (1 + ‖z‖) ^ ((w : ℝ) + s₀) * |distr m σ F i z|
          ≤ (1 + ‖z‖) ^ ((w : ℝ) + s₀) * (‖iteratedFDeriv ℝ (c i) (F i) z‖ * P i) :=
            mul_le_mul_of_nonneg_left h1 hz
        _ = ((1 + ‖z‖) ^ ((w : ℝ) + s₀) * ‖iteratedFDeriv ℝ (c i) (F i) z‖) * P i := by ring
        _ ≤ ((μ i * Y) ^ (c i + w) * X i) * P i := mul_le_mul_of_nonneg_right h2 (hP i)
        _ = μ i ^ ((w : ℕ) : ℝ) * (μ i ^ c i * Y ^ (c i + w) * X i * P i) := by
            rw [Real.rpow_natCast, mul_pow, pow_add]; ring
    have hLow : ∀ i, DecayBound ((μ i * Y) ^ c i * X i * P i) s₀ (distr m σ F i) := by
      intro i z
      have h1 := abs_distr_le m σ F i z
      have h2 := (hF i).le_wt ((hc i).trans hr) (Nat.zero_le W) z
      simp only [Nat.cast_zero, zero_add, add_zero] at h2
      calc |distr m σ F i z| ≤ ‖iteratedFDeriv ℝ (c i) (F i) z‖ * P i := h1
        _ ≤ ((μ i * Y) ^ (c i) * X i * wt s₀ z) * P i := mul_le_mul_of_nonneg_right h2 (hP i)
        _ = (μ i * Y) ^ c i * X i * P i * (1 + ‖z‖) ^ (-s₀) := by simp only [wt]; ring
    have hw' : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
    have key := abs_collisionTerm_le_weighted hd hs₀ hw' (hμ 0) (hμ 1) (hμ 2) (hHigh 0)
      (hHigh 1) (hHigh 2) (hLow 0) (hLow 1) (hLow 2) j y
    have key' := le_of_weighted y key
    rw [Real.norm_eq_abs, coe_ktriple]
    refine key'.trans (le_of_eq ?_)
    have hsum : c 0 + c 1 + c 2 = r := sum_card_filter_fin3 σ
    have hprodP : P 0 * P 1 * P 2 = ∏ t, ‖m t‖ := prod_fin3_fiberwise σ _
    have hprodμ : μ 0 ^ c 0 * μ 1 ^ c 1 * μ 2 ^ c 2 = ∏ t, μ (σ t) := prod_pow_card_fin3 σ μ
    rw [← hprodP, ← hprodμ, Real.rpow_natCast, ← hsum]
    simp only [multConst, mul_pow, pow_add]
    ring
  calc ∑ σ : Fin r → Fin 3, ‖ktriple hd j (distr m σ F) y‖
      ≤ ∑ σ : Fin r → Fin 3, multConst d s₀ * μs ^ w * Y ^ (r + w) * (X 0 * X 1 * X 2) *
          (∏ t, ‖m t‖) * (∏ t, μ (σ t)) * wt ((w : ℝ) + s₀) y := Finset.sum_le_sum fun σ _ => hterm σ
    _ = multConst d s₀ * μs ^ w * Y ^ (r + w) * (X 0 * X 1 * X 2) * (∏ t, ‖m t‖) *
          (∑ σ : Fin r → Fin 3, ∏ t, μ (σ t)) * wt ((w : ℝ) + s₀) y := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = B * wt ((w : ℝ) + s₀) y * ∏ t, ‖m t‖ := by
        rw [sum_prod_fin3]
        simp only [B, μs, mul_pow, pow_add]
        ring

end WaveTurbulence.WKE
