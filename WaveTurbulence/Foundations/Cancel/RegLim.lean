/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.ApproxId
public import WaveTurbulence.Foundations.ClassJR.MCChainF

/-!
# Regularized limits of time coefficients, and the type 1 step (DH21 (recurtype1))

The Gaussian-regularized integrals `R_θ(t, s)` of a time coefficient over its variables are compared
with their limits `J(t, s)` through the invariant `RegLim2 R J`. On the square `[0,1]²` it requires,
eventually in `θ → 0+`:
* a uniform bound;
* a uniform joint Lipschitz bound;
* pointwise convergence `R_θ → J`.

The type 1 step of DH21 (newexp1)/(recurtype1) (`regLim2_type1`): if `H` has the invariant, so does
`∫_0^t∫_0^s kk b θ (t₁ - s₁) H_θ(t₁, s₁) ds₁ dt₁`. Its limit is `2∫_0^{min(t,s)} H(τ, τ) dτ` for
`b = false` (the root variable is not in `Z`; the two-sided mass of `gk` is `2`) and `0` for
`b = true` (`hk` is odd).
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-- **The regularized-limit invariant** on the square `[0,1]²`. -/
structure RegLim2 (R : ℝ → ℝ → ℝ → ℂ) (J : ℝ → ℝ → ℂ) : Prop where
  bound : ∃ M, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖R θ t s‖ ≤ M
  lip : ∃ L, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t' ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, ‖R θ t s - R θ t' s'‖ ≤ L * (|t - t'| + |s - s'|)
  lim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, Tendsto (fun θ => R θ t s) (𝓝[>] 0) (𝓝 (J t s))

theorem RegLim2.congr {R R' : ℝ → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ} (h : RegLim2 R J)
    (he : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, R' θ t s = R θ t s) :
    RegLim2 R' J := by
  obtain ⟨M, hM⟩ := h.bound
  obtain ⟨L, hL⟩ := h.lip
  refine ⟨⟨M, ?_⟩, ⟨L, ?_⟩, fun t ht s hs => (h.lim t ht s hs).congr' ?_⟩
  · filter_upwards [hM, he] with θ h1 h2 t ht s hs
    rw [h2 t ht s hs]; exact h1 t ht s hs
  · filter_upwards [hL, he] with θ h1 h2 t ht s hs t' ht' s' hs'
    rw [h2 t ht s hs, h2 t' ht' s' hs']; exact h1 t ht s hs t' ht' s' hs'
  · filter_upwards [he] with θ h2
    exact (h2 t ht s hs).symm

theorem RegLim2.limit_lip {R : ℝ → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ} (h : RegLim2 R J) :
    ∃ L, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      ‖J t s - J t' s'‖ ≤ L * (|t - t'| + |s - s'|) := by
  obtain ⟨L, hL⟩ := h.lip
  refine ⟨L, fun t ht s hs t' ht' s' hs' => ?_⟩
  have h1 := ((h.lim t ht s hs).sub (h.lim t' ht' s' hs')).norm
  exact le_of_tendsto h1 (hL.mono fun θ hθ => hθ t ht s hs t' ht' s' hs')

theorem RegLim2.limit_bound {R : ℝ → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ} (h : RegLim2 R J) :
    ∃ M, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖J t s‖ ≤ M := by
  obtain ⟨M, hM⟩ := h.bound
  exact ⟨M, fun t ht s hs => le_of_tendsto (h.lim t ht s hs).norm (hM.mono fun θ hθ => hθ t ht s hs)⟩

/-! ### Clamping onto the square -/

theorem abs_clamp01_sub_le (x y : ℝ) : |clamp01 x - clamp01 y| ≤ |x - y| := by
  unfold clamp01
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le (abs_nonneg _) ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  simp

/-- A function on the square, `L`-Lipschitz there, is globally Lipschitz after clamping. -/
theorem lip_clamp {f : ℝ → ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      ‖f t s - f t' s'‖ ≤ L * (|t - t'| + |s - s'|)) (t s t' s' : ℝ) :
    ‖f (clamp01 t) (clamp01 s) - f (clamp01 t') (clamp01 s')‖ ≤ L * (|t - t'| + |s - s'|) :=
  (hf _ (clamp01_mem t) _ (clamp01_mem s) _ (clamp01_mem t') _ (clamp01_mem s')).trans
    (mul_le_mul_of_nonneg_left (add_le_add (abs_clamp01_sub_le t t') (abs_clamp01_sub_le s s')) hL)

theorem continuous_of_lip2 {f : ℝ → ℝ → ℂ} {L : ℝ}
    (hf : ∀ t s t' s', ‖f t s - f t' s'‖ ≤ L * (|t - t'| + |s - s'|)) :
    Continuous (Function.uncurry f) := by
  have hL : 0 ≤ L := by
    have := hf 1 0 0 0
    norm_num at this
    exact (norm_nonneg _).trans this
  refine (LipschitzWith.of_dist_le_mul (K := ⟨2 * L, by positivity⟩) fun p q => ?_).continuous
  rw [dist_eq_norm]
  refine (hf p.1 p.2 q.1 q.2).trans ?_
  change L * (|p.1 - q.1| + |p.2 - q.2|) ≤ (2 * L) * dist p q
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have h1 := le_max_left |p.1 - q.1| |p.2 - q.2|
  have h2 := le_max_right |p.1 - q.1| |p.2 - q.2|
  nlinarith

theorem continuous_of_lip1 {f : ℝ → ℂ} {L : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ L * |x - y|) :
    Continuous f := by
  have hL : 0 ≤ L := by
    have := hf 1 0
    norm_num at this
    exact (norm_nonneg _).trans this
  refine (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun x y => ?_).continuous
  rw [dist_eq_norm, Real.dist_eq]; exact hf x y

/-! ### The inner integral of the type 1 step -/

/-- `∫_a^c |kk b θ (τ - x)| dx ≤ 2`. -/
theorem integral_abs_kk_shift_le {b : Bool} {θ : ℝ} (hθ : 0 < θ) (τ : ℝ) {a c : ℝ} (hac : a ≤ c) :
    ∫ x in a..c, |kk b θ (τ - x)| ≤ 2 := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => |kk b θ u|)]
  exact integral_abs_kk_le hθ (by linarith)

theorem norm_integral_kk_shift_le {b : Bool} {θ : ℝ} (hθ : 0 < θ) (τ : ℝ) {a c : ℝ} (hac : a ≤ c)
    {f : ℝ → ℂ} {B : ℝ} (hB : ∀ x ∈ Icc a c, ‖f x‖ ≤ B) :
    ‖∫ x in a..c, (kk b θ (τ - x) : ℂ) * f x‖ ≤ 2 * max B 0 := by
  refine (intervalIntegral.norm_integral_le_of_norm_le hac (g := fun x => max B 0 * |kk b θ (τ - x)|)
    (Eventually.of_forall fun x hx => ?_) ?_).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hB x ⟨hx.1.le, hx.2⟩).trans (le_max_left _ _)) (abs_nonneg _)
  · exact (((continuous_kk b θ).comp (continuous_const.sub continuous_id)).abs.const_mul _).intervalIntegrable _ _
  · rw [intervalIntegral.integral_const_mul]
    nlinarith [integral_abs_kk_shift_le (b := b) hθ τ hac, le_max_right B 0]

theorem integral_abs_kk_shift_le' {b : Bool} {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {a c : ℝ} (hac : a ≤ c) :
    ∫ x in a..c, |kk b θ (x - σ)| ≤ 2 := by
  rw [intervalIntegral.integral_comp_sub_right (fun u => |kk b θ u|)]
  exact integral_abs_kk_le hθ (by linarith)

theorem norm_integral_kk_shift_le' {b : Bool} {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {a c : ℝ} (hac : a ≤ c)
    {f : ℝ → ℂ} {B : ℝ} (hB : ∀ x ∈ Icc a c, ‖f x‖ ≤ B) :
    ‖∫ x in a..c, (kk b θ (x - σ) : ℂ) * f x‖ ≤ 2 * max B 0 := by
  refine (intervalIntegral.norm_integral_le_of_norm_le hac (g := fun x => max B 0 * |kk b θ (x - σ)|)
    (Eventually.of_forall fun x hx => ?_) ?_).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hB x ⟨hx.1.le, hx.2⟩).trans (le_max_left _ _)) (abs_nonneg _)
  · exact (((continuous_kk b θ).comp (continuous_id.sub continuous_const)).abs.const_mul _).intervalIntegrable _ _
  · rw [intervalIntegral.integral_const_mul]
    nlinarith [integral_abs_kk_shift_le' (b := b) hθ σ hac, le_max_right B 0]

/-- **The inner limit**: `∫_0^s kk b θ (τ - x) h_θ(x) dx → 2a` (`gk`) or `0` (`hk`) for `0 < τ < s`, and
`→ 0` for `τ > s`, if `h_θ` is uniformly bounded and Lipschitz with `h_θ(τ) → a`. -/
theorem tendsto_inner_type1 (b : Bool) {h : ℝ → ℝ → ℂ} {M L : ℝ}
    (hc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (h θ))
    (hM : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ x, ‖h θ x‖ ≤ M)
    (hL : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ x y, ‖h θ x - h θ y‖ ≤ L * |x - y|)
    {τ : ℝ} (hτ : 0 < τ) {a : ℂ} (ha : Tendsto (fun θ => h θ τ) (𝓝[>] 0) (𝓝 a))
    {s : ℝ} (hs : 0 ≤ s) (hτs : τ ≠ s) :
    Tendsto (fun θ => ∫ x in (0 : ℝ)..s, (kk b θ (τ - x) : ℂ) * h θ x) (𝓝[>] 0)
      (𝓝 (if τ < s then (if b then 0 else 2 * a) else 0)) := by
  -- the left half `[0, τ]`, after `u = τ - x`
  have hleft : ∀ c, 0 < c → c ≤ τ → Tendsto (fun θ => ∫ u in (0 : ℝ)..c, (kk b θ u : ℂ) * h θ (τ - u))
      (𝓝[>] 0) (𝓝 (sg b * a)) := by
    intro c hc0 _
    refine tendsto_integral_kk_mul_of_lip hc0 (hc.mono fun θ hθ =>
      (hθ.comp (continuous_const.sub continuous_id)).continuousOn) (L := L) ?_ (by simpa using ha)
    filter_upwards [hL] with θ hθ u hu
    have := hθ (τ - u) τ
    simp only [sub_sub_cancel_left, abs_neg] at this
    simpa [abs_of_nonneg hu.1] using this
  by_cases hlt : τ < s
  · simp only [hlt, ↓reduceIte]
    have hint : ∀ θ, Continuous (h θ) → ∀ x y : ℝ,
        IntervalIntegrable (fun x => (kk b θ (τ - x) : ℂ) * h θ x) volume x y := fun θ hθ x y =>
      ((continuous_ofReal.comp ((continuous_kk b θ).comp (continuous_const.sub continuous_id))).mul
        hθ).intervalIntegrable _ _
    -- split at `τ`
    have hsplit : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∫ x in (0 : ℝ)..s, (kk b θ (τ - x) : ℂ) * h θ x =
        (∫ u in (0 : ℝ)..τ, (kk b θ u : ℂ) * h θ (τ - u)) +
          (if b then -1 else 1) * ∫ u in (0 : ℝ)..(s - τ), (kk b θ u : ℂ) * h θ (τ + u) := by
      filter_upwards [hc] with θ hθ
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := τ) (hint θ hθ 0 τ)
        (hint θ hθ τ s)]
      congr 1
      · have e := intervalIntegral.integral_comp_sub_left
          (fun u => (kk b θ u : ℂ) * h θ (τ - u)) (a := 0) (b := τ) τ
        simp only [sub_sub_cancel, sub_self, sub_zero] at e
        exact e
      · have e := intervalIntegral.integral_comp_sub_right
          (fun u => (kk b θ (-u) : ℂ) * h θ (τ + u)) (a := τ) (b := s) τ
        simp only [sub_self, neg_sub, add_sub_cancel] at e
        rw [e, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun u _ => ?_
        rw [kk_neg]; cases b <;> simp
    refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
    have h1 := hleft τ hτ le_rfl
    have h2 := (tendsto_integral_kk_mul_of_lip (b := b) (sub_pos.2 hlt)
      (f := fun θ u => h θ (τ + u)) (hc.mono fun θ hθ =>
        (hθ.comp (continuous_const.add continuous_id)).continuousOn) (L := L)
      (by
        filter_upwards [hL] with θ hθ u hu
        have := hθ (τ + u) τ
        simp only [add_sub_cancel_left] at this
        simpa [abs_of_nonneg hu.1] using this)
      (by simpa using ha)).const_mul (if b then -1 else 1)
    have := h1.add h2
    convert this using 2
    cases b
    · simp only [sg, Bool.false_eq_true, ite_false]; ring
    · simp [sg]
  · have hgt : s < τ := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hτs)
    simp only [hlt, ↓reduceIte]
    have e : ∀ θ, ∫ x in (0 : ℝ)..s, (kk b θ (τ - x) : ℂ) * h θ x =
        ∫ u in (τ - s)..τ, (kk b θ u : ℂ) * h θ (τ - u) := by
      intro θ
      have e := intervalIntegral.integral_comp_sub_left
        (fun u => (kk b θ u : ℂ) * h θ (τ - u)) (a := 0) (b := s) τ
      simp only [sub_sub_cancel, sub_zero] at e
      exact e
    simp_rw [e]
    exact tendsto_integral_kk_tail (sub_pos.2 hgt) (by linarith) (M := M)
      (hM.mono fun θ hθ u _ => hθ _)

/-- `∫_0^t 1_{x<s} c(x) dx = ∫_0^{min(t,s)} c(x) dx`. -/
theorem integral_ite_lt {c : ℝ → ℂ} {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hc : ∀ x y, IntervalIntegrable c volume x y) :
    ∫ x in (0 : ℝ)..t, (if x < s then c x else 0) = ∫ x in (0 : ℝ)..min t s, c x := by
  rcases le_total t s with hts | hst
  · rw [min_eq_left hts]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume t] with x hxt hx
    rw [uIoc_of_le ht] at hx
    simp only [lt_of_lt_of_le (lt_of_le_of_ne hx.2 hxt) hts, ↓reduceIte]
  · rw [min_eq_right hst]
    have hi : ∀ x y, IntervalIntegrable (fun x => if x < s then c x else 0) volume x y := by
      intro x y
      have : (fun x => if x < s then c x else 0) = (Iio s).indicator c := by
        funext x; simp [Set.indicator, Set.mem_Iio]
      rw [this]
      exact ⟨(hc x y).1.indicator measurableSet_Iio, (hc x y).2.indicator measurableSet_Iio⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hi 0 s) (hi s t)]
    have h1 : ∫ x in (0 : ℝ)..s, (if x < s then c x else 0) = ∫ x in (0 : ℝ)..s, c x := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume s] with x hxs hx
      rw [uIoc_of_le hs] at hx
      simp only [lt_of_le_of_ne hx.2 hxs, ↓reduceIte]
    have h2 : ∫ x in s..t, (if x < s then c x else 0) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun x hx => ?_]
      · simp
      · rw [uIcc_of_le hst] at hx
        simp [not_lt.2 hx.1]
    rw [h1, h2, add_zero]

/-! ### The type 1 step -/

/-- **The type 1 step** (DH21 (newexp1), (integralK), (recurtype1)). -/
theorem regLim2_type1 {H : ℝ → ℝ → ℝ → ℂ} {H₀ : ℝ → ℝ → ℂ} (hH : RegLim2 H H₀) (b : Bool) :
    RegLim2 (fun θ t s => ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, (kk b θ (t₁ - s₁) : ℂ) * H θ t₁ s₁)
      (fun t s => if b then 0 else 2 * ∫ τ in (0 : ℝ)..min t s, H₀ τ τ) := by
  obtain ⟨M, hM⟩ := hH.bound
  obtain ⟨L, hL⟩ := hH.lip
  set Hc : ℝ → ℝ → ℝ → ℂ := fun θ t s => H θ (clamp01 t) (clamp01 s) with hHc
  have hHcM : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t s, ‖Hc θ t s‖ ≤ M :=
    hM.mono fun θ hθ t s => hθ _ (clamp01_mem t) _ (clamp01_mem s)
  have hHcL : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t s t' s',
      ‖Hc θ t s - Hc θ t' s'‖ ≤ max L 0 * (|t - t'| + |s - s'|) :=
    hL.mono fun θ hθ t s t' s' => lip_clamp (le_max_right _ _) (fun t ht s hs t' ht' s' hs' =>
      (hθ t ht s hs t' ht' s' hs').trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by positivity))) t s t' s'
  have hHcC : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (Function.uncurry (Hc θ)) :=
    hHcL.mono fun θ hθ => continuous_of_lip2 hθ
  set R : ℝ → ℝ → ℝ → ℂ := fun θ t s =>
    ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁ with hR
  -- the clamped version agrees on the square
  have heq : ∀ θ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, (kk b θ (t₁ - s₁) : ℂ) * H θ t₁ s₁) = R θ t s := by
    intro θ t ht s hs
    refine intervalIntegral.integral_congr fun t₁ ht₁ => intervalIntegral.integral_congr fun s₁ hs₁ => ?_
    rw [uIcc_of_le ht.1] at ht₁; rw [uIcc_of_le hs.1] at hs₁
    simp only [hHc, clamp01_eq ⟨ht₁.1, ht₁.2.trans ht.2⟩, clamp01_eq ⟨hs₁.1, hs₁.2.trans hs.2⟩]
  refine RegLim2.congr ?_ (Eventually.of_forall fun θ t ht s hs => heq θ t ht s hs)
  -- the inner integral
  set I : ℝ → ℝ → ℝ → ℂ := fun θ t₁ s => ∫ s₁ in (0 : ℝ)..s, (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁
    with hI
  have hIb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t₁, ∀ s ∈ Icc (0 : ℝ) 1, ‖I θ t₁ s‖ ≤ 2 * max M 0 := by
    filter_upwards [hHcM, hHcC, eventually_pos_nhdsGT] with θ hθM hθC hθ t₁ s hs
    exact norm_integral_kk_shift_le hθ t₁ hs.1 (fun x _ => hθM t₁ x)
  have hIc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ s, Continuous fun t₁ => I θ t₁ s := by
    filter_upwards [hHcC] with θ hθC s
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t₁ s₁ => (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁)
      ((continuous_ofReal.comp ((continuous_kk b θ).comp (continuous_fst.sub continuous_snd))).mul
        hθC) 0 s
  -- Fubini on the rectangle
  have hswap : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t s, R θ t s =
      ∫ s₁ in (0 : ℝ)..s, ∫ t₁ in (0 : ℝ)..t, (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁ := by
    filter_upwards [hHcC] with θ hθC t s
    refine intervalIntegral_intervalIntegral_swap ?_
    have hcont : Continuous (Function.uncurry fun t₁ s₁ => (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁) :=
      (continuous_ofReal.comp ((continuous_kk b θ).comp (continuous_fst.sub continuous_snd))).mul hθC
    exact (hcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hJb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ s₁, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖∫ t₁ in (0 : ℝ)..t, (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁‖ ≤ 2 * max M 0 := by
    filter_upwards [hHcM, hHcC, eventually_pos_nhdsGT] with θ hθM hθC hθ s₁ t ht
    exact norm_integral_kk_shift_le' hθ s₁ ht.1 (fun x _ => hθM x s₁)
  have hJc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t, Continuous fun s₁ =>
      ∫ t₁ in (0 : ℝ)..t, (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁ := by
    filter_upwards [hHcC] with θ hθC t
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s₁ t₁ => (kk b θ (t₁ - s₁) : ℂ) * Hc θ t₁ s₁)
      ((continuous_ofReal.comp ((continuous_kk b θ).comp (continuous_snd.sub continuous_fst))).mul
        (hθC.comp (continuous_snd.prodMk continuous_fst))) 0 t
  have hM2 : 0 ≤ 2 * max M 0 := by positivity
  refine ⟨⟨2 * max M 0, ?_⟩, ⟨2 * max M 0, ?_⟩, ?_⟩
  · -- the bound
    filter_upwards [hIb] with θ hθ t ht s hs
    show ‖∫ t₁ in (0 : ℝ)..t, I θ t₁ s‖ ≤ _
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => hθ x s hs).trans ?_
    rw [sub_zero, abs_of_nonneg ht.1]
    nlinarith [ht.2]
  · -- the Lipschitz bound
    filter_upwards [hIb, hIc, hJb, hJc, hswap] with θ hIb' hIc' hJb' hJc' hsw t ht s hs t' ht' s' hs'
    have h1 : ‖R θ t s - R θ t' s‖ ≤ 2 * max M 0 * |t - t'| := by
      show ‖(∫ t₁ in (0 : ℝ)..t, I θ t₁ s) - ∫ t₁ in (0 : ℝ)..t', I θ t₁ s‖ ≤ _
      rw [intervalIntegral.integral_interval_sub_left ((hIc' s).intervalIntegrable _ _)
        ((hIc' s).intervalIntegrable _ _)]
      exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => hIb' x s hs
    have h2 : ‖R θ t' s - R θ t' s'‖ ≤ 2 * max M 0 * |s - s'| := by
      rw [hsw t' s, hsw t' s', intervalIntegral.integral_interval_sub_left
        ((hJc' t').intervalIntegrable _ _) ((hJc' t').intervalIntegrable _ _)]
      exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => hJb' x t' ht'
    calc ‖R θ t s - R θ t' s'‖ ≤ ‖R θ t s - R θ t' s‖ + ‖R θ t' s - R θ t' s'‖ := by
          rw [← sub_add_sub_cancel (R θ t s) (R θ t' s) (R θ t' s')]; exact norm_add_le _ _
      _ ≤ 2 * max M 0 * |t - t'| + 2 * max M 0 * |s - s'| := add_le_add h1 h2
      _ = 2 * max M 0 * (|t - t'| + |s - s'|) := by ring
  · -- the limit
    intro t ht s hs
    obtain ⟨L₀, hL₀⟩ := hH.limit_lip
    set H₀c : ℝ → ℂ := fun τ => H₀ (clamp01 τ) (clamp01 τ) with hH₀c
    have hH₀cc : Continuous H₀c := by
      have h := continuous_of_lip2 (f := fun t s => H₀ (clamp01 t) (clamp01 s))
        (lip_clamp (le_max_right L₀ 0) fun t ht s hs t' ht' s' hs' => (hL₀ t ht s hs t' ht' s' hs').trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      exact h.comp (continuous_id.prodMk continuous_id)
    have hlim : Tendsto (fun θ => R θ t s) (𝓝[>] 0)
        (𝓝 (∫ t₁ in (0 : ℝ)..t, if t₁ < s then (if b then 0 else 2 * H₀c t₁) else 0)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => 2 * max M 0) ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [hIc] with θ hθ
        exact (hθ s).aestronglyMeasurable
      · filter_upwards [hIb] with θ hθ
        exact Eventually.of_forall fun x _ => hθ x s hs
      · filter_upwards [Measure.ae_ne volume s] with t₁ hne ht₁
        rw [uIoc_of_le ht.1] at ht₁
        have ht₁' : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1.le, ht₁.2.trans ht.2⟩
        have ha : Tendsto (fun θ => Hc θ t₁ t₁) (𝓝[>] 0) (𝓝 (H₀c t₁)) := by
          simp only [hHc, hH₀c, clamp01_eq ht₁']
          exact hH.lim t₁ ht₁' t₁ ht₁'
        exact tendsto_inner_type1 b (h := fun θ => Hc θ t₁) (M := M) (L := max L 0)
          (hHcC.mono fun θ hθ => hθ.comp (continuous_const.prodMk continuous_id))
          (hHcM.mono fun θ hθ x => hθ t₁ x)
          (hHcL.mono fun θ hθ x y => by simpa using hθ t₁ x t₁ y) ht₁.1 ha hs.1 hne
    have hval : (∫ t₁ in (0 : ℝ)..t, if t₁ < s then (if b then 0 else 2 * H₀c t₁) else 0) =
        if b then 0 else 2 * ∫ τ in (0 : ℝ)..min t s, H₀ τ τ := by
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        rw [integral_ite_lt (c := fun x => 2 * H₀c x) ht.1 hs.1
          fun x y => ((continuous_const.mul hH₀cc).intervalIntegrable x y),
          intervalIntegral.integral_const_mul]
        congr 1
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le (le_min ht.1 hs.1)] at hτ
        have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ((min_le_left _ _).trans ht.2)⟩
        simp only [hH₀c, clamp01_eq hτ']
      · simp
    rw [← hval]
    exact hlim

end WaveTurbulence.Cancel
