/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.GlueCore
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TraceBox

/-! # W2-KIND2 Lemma A (7): the `𝔛^θ` norm of the kink kernels `κ(t) e^{2πi(ξ₀ φ(t₀) + ξ₁ t₁)}`

`cut0`: smooth, `= 1` on `[0, 2]`; `cut1 = chiUnit`: smooth, `= 1` on `[0, 1]`.  For `φ(t) = c₀ + sa·min(t - (w+1), 0) + sb·max(t - (w+1), 0)` (`sa = 0 ∨ sb = 0`, `|sa|,|sb| ≤ 1`):
`‖κ₀(t₀ - w) κ₁(t₁ - b) e^{2πi(ξ₀ φ(t₀) + ξ₁ t₁)}‖_{𝔛^θ} ≤ Ck · ⟨ξ⟩^{θ+δ}` with `Ck` independent of `w, b, c₀, sa, sb, ξ` (`kernel_norm`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology WaveTurbulence.Fourier
open scoped ENNReal

/-- The fixed cutoff in the `t₀` direction: `1` on `[0, 2]`, supported in `(-1, 3)`. -/
noncomputable def bump0 : ContDiffBump (1 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def cut0 (x : ℝ) : ℂ := ((bump0 x : ℝ) : ℂ)

/-- The fixed cutoff in the `t₁` direction: `1` on `[0, 1]`. -/
noncomputable def cut1 (x : ℝ) : ℂ := ((VineEstS3.chiUnit x : ℝ) : ℂ)

theorem cut0_contDiff : ContDiff ℝ (⊤ : ℕ∞) cut0 := Complex.ofRealCLM.contDiff.comp bump0.contDiff

theorem cut0_compact : HasCompactSupport cut0 := bump0.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

theorem cut0_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) : cut0 x = 1 := by
  unfold cut0
  have : x ∈ Metric.closedBall (1 : ℝ) bump0.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |x - 1| ≤ 1
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  simp [bump0.one_of_mem_closedBall this]

theorem cut1_contDiff : ContDiff ℝ (⊤ : ℕ∞) cut1 := Complex.ofRealCLM.contDiff.comp VineEstS3.chiUnit_contDiff

theorem cut1_compact : HasCompactSupport cut1 :=
  VineEstS3.chiUnit_hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

theorem cut1_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : cut1 x = 1 := by
  unfold cut1; simp [VineEstS3.chiUnit_eq_one hx]

theorem ex_neg_eq_eE (p x : ℝ) : ex (-p) x = eE (p * x) := by
  unfold ex eE
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem ex_add_arg (μ x y : ℝ) : ex μ (x + y) = ex μ x * ex μ y := by
  unfold ex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eE_add (a b : ℝ) : eE (a + b) = eE a * eE b := by
  unfold eE
  rw [AddChar.map_add_eq_mul]
  simp

/-- Shift and phase do not change the transform's modulus. -/
theorem norm_fT_shift {F : ℝ → ℂ} (c : ℝ) {ph : ℂ} (hph : ‖ph‖ = 1) (l : ℝ) :
    ‖fT (fun t => ph * F (t - c)) l‖ = ‖fT F l‖ := by
  have h : fT (fun t => ph * F (t - c)) l = ph * ex l c * fT F l := by
    unfold fT
    have e : ∀ t : ℝ, ph * F (t - c) * ex l t = (ph * ex l c) * (F (t - c) * ex l (t - c)) := fun t => by
      have : ex l t = ex l (t - c) * ex l c := by rw [← ex_add_arg]; congr 1; ring
      rw [this]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => F x * ex l x) c]
  rw [h, norm_mul, norm_mul, hph, norm_ex]; simp

theorem NN_shift {F : ℝ → ℂ} (α c : ℝ) {ph : ℂ} (hph : ‖ph‖ = 1) :
    NN α (fun t => ph * F (t - c)) = NN α F := by
  unfold NN
  refine lintegral_congr fun l => ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_fT_shift c hph]

theorem fT_modulate (κ : ℝ → ℂ) (ξ l : ℝ) : fT (kinkFn κ ξ ξ) l = fT (kinkFn κ 0 0) (l - ξ) := by
  unfold fT
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have h1 : kinkFn κ ξ ξ x = κ x * ex (-ξ) x := by unfold kinkFn; split_ifs <;> rfl
  have h2 : kinkFn κ 0 0 x = κ x := by unfold kinkFn; split_ifs <;> simp [ex]
  rw [h1, h2, mul_assoc, ex_add, show -ξ + l = l - ξ by ring]


theorem NN_modulated_le {κ : ℝ → ℂ} {α : ℝ} (hα : 0 ≤ α) (ξ : ℝ) :
    NN α (kinkFn κ ξ ξ) ≤ ENNReal.ofReal ((1 + |ξ|) ^ α) * NN α (kinkFn κ 0 0) := by
  unfold NN
  have e1 : ∫⁻ l, ENNReal.ofReal ((1 + |l|) ^ α) * ‖fT (kinkFn κ ξ ξ) l‖ₑ =
      ∫⁻ l, (fun x : ℝ => ENNReal.ofReal ((1 + |x + ξ|) ^ α) * ‖fT (kinkFn κ 0 0) x‖ₑ) (l - ξ) := by
    refine lintegral_congr fun l => ?_
    simp only [sub_add_cancel]
    rw [fT_modulate]
  rw [e1, lintegral_sub_right_eq_self (fun x : ℝ => ENNReal.ofReal ((1 + |x + ξ|) ^ α) * ‖fT (kinkFn κ 0 0) x‖ₑ) ξ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h := one_add_abs_le_mul (x + ξ) ξ
  rw [add_sub_cancel_right] at h
  calc (1 + |x + ξ|) ^ α ≤ ((1 + |ξ|) * (1 + |x|)) ^ α := Real.rpow_le_rpow (by positivity) h hα
    _ = _ := Real.mul_rpow (by positivity) (by positivity)

theorem one_add_abs_le_tb (ξ : Fin 2 → ℝ) (j : Fin 2) : 1 + |ξ j| ≤ Real.sqrt 2 * timeBracket ξ := by
  have h1 : Real.sqrt (1 + ξ j ^ 2) ≤ timeBracket ξ := by
    unfold timeBracket
    exact Finset.le_sup' (fun i : Option (Fin 2) => match i with | none => (1 : ℝ) | some j => Real.sqrt (1 + ξ j ^ 2))
      (Finset.mem_univ (some j))
  have h2 : 1 + |ξ j| ≤ Real.sqrt 2 * Real.sqrt (1 + ξ j ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [sq_abs (ξ j), abs_nonneg (ξ j), sq_nonneg (|ξ j| - 1)]
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _))


theorem two_le_top' : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  simpa using h

theorem cut0_shift_contDiff : ContDiff ℝ 2 (fun x : ℝ => cut0 (x + 1)) :=
  (cut0_contDiff.of_le two_le_top').comp (contDiff_id.add contDiff_const)

theorem cut0_shift_compact : HasCompactSupport (fun x : ℝ => cut0 (x + 1)) :=
  cut0_compact.comp_homeomorph (Homeomorph.addRight (1 : ℝ))

theorem kernel_norm {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (hθδ : θ + δ ≤ 1) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ (w b c0 sa sb : ℝ) (ξ : Fin 2 → ℝ), (sa = 0 ∨ sb = 0) → |sa| ≤ 1 → |sb| ≤ 1 →
      timeFourierNorm θ (fun t : Fin 2 → ℝ => (cut0 (t 0 - w) * cut1 (t 1 - b)) *
        eE (ξ 0 * (c0 + sa * min (t 0 - (w + 1)) 0 + sb * max (t 0 - (w + 1)) 0) + ξ 1 * t 1)) ≤
        ENNReal.ofReal (Ck * timeBracket ξ ^ (θ + δ)) := by
  have hc1 : ContDiff ℝ 2 cut1 := cut1_contDiff.of_le two_le_top'
  obtain ⟨Ka, hKa, hA⟩ := kink_weighted cut0_shift_contDiff cut0_shift_compact (α := θ) (δ := δ) hθ hδ hθδ
  obtain ⟨Kb, hKb, hB⟩ := kink_weighted cut0_shift_contDiff cut0_shift_compact (α := 0) (δ := δ) le_rfl hδ (by linarith)
  obtain ⟨Kc, hKc, hC⟩ := kink_weighted hc1 cut1_compact (α := θ) (δ := δ) hθ hδ hθδ
  obtain ⟨Kd, hKd, hD⟩ := kink_weighted hc1 cut1_compact (α := 0) (δ := δ) le_rfl hδ (by linarith)
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  refine ⟨Ka * Kd * Real.sqrt 2 + Kb * Kc * Real.sqrt 2 + 1, by positivity, fun w b c0 sa sb ξ hs hsa hsb => ?_⟩
  set p : ℝ := ξ 0 * sa with hp
  set q : ℝ := ξ 0 * sb with hq
  set d : ℝ := p + q with hd
  have hpq : (p = 0 ∧ q = d) ∨ (p = d ∧ q = 0) := by
    rcases hs with h | h
    · left; subst h; simp [hp, hd]
    · right; subst h; simp [hq, hd]
  have hdle : |d| ≤ |ξ 0| := by
    rcases hs with h | h
    · subst h; simp only [hd, hp, hq, mul_zero, zero_add, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hsb
    · subst h; simp only [hd, hp, hq, mul_zero, add_zero, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hsa
  let κ0 : ℝ → ℂ := fun x => cut0 (x + 1)
  let F0 : ℝ → ℂ := fun t => eE (ξ 0 * c0) * kinkFn κ0 p q (t - (w + 1))
  let F1 : ℝ → ℂ := fun t => eE (ξ 1 * b) * kinkFn cut1 (ξ 1) (ξ 1) (t - b)
  have hfun : (fun t : Fin 2 → ℝ => (cut0 (t 0 - w) * cut1 (t 1 - b)) *
        eE (ξ 0 * (c0 + sa * min (t 0 - (w + 1)) 0 + sb * max (t 0 - (w + 1)) 0) + ξ 1 * t 1)) =
      fun t => F0 (t 0) * F1 (t 1) := by
    funext t
    simp only [F0, F1]
    set x : ℝ := t 0 - (w + 1) with hx
    have hk0 : κ0 x = cut0 (t 0 - w) := by simp only [κ0, hx]; congr 1; ring
    have hk1 : kinkFn cut1 (ξ 1) (ξ 1) (t 1 - b) = cut1 (t 1 - b) * eE (ξ 1 * (t 1 - b)) := by
      unfold kinkFn; split_ifs <;> simp [ex_neg_eq_eE]
    have he1 : eE (ξ 1 * t 1) = eE (ξ 1 * b) * eE (ξ 1 * (t 1 - b)) := by
      rw [← eE_add]; congr 1; ring
    rcases le_or_gt x 0 with hx0 | hx0
    · have hmin : min x 0 = x := min_eq_left hx0
      have hmax : max x 0 = 0 := max_eq_right hx0
      have hk : kinkFn κ0 p q x = κ0 x * eE (p * x) := by
        rw [kinkFn_of_nonpos hx0, ex_neg_eq_eE]
      rw [hk, hk1, hmin, hmax, hk0]
      have : ξ 0 * (c0 + sa * x + sb * 0) + ξ 1 * t 1 = ξ 0 * c0 + p * x + ξ 1 * t 1 := by simp only [hp]; ring
      rw [this, eE_add, eE_add, he1]
      ring
    · have hmin : min x 0 = 0 := min_eq_right hx0.le
      have hmax : max x 0 = x := max_eq_left hx0.le
      have hk : kinkFn κ0 p q x = κ0 x * eE (q * x) := by
        rw [kinkFn_of_pos hx0, ex_neg_eq_eE]
      rw [hk, hk1, hmin, hmax, hk0]
      have : ξ 0 * (c0 + sa * 0 + sb * x) + ξ 1 * t 1 = ξ 0 * c0 + q * x + ξ 1 * t 1 := by simp only [hq]; ring
      rw [this, eE_add, eE_add, he1]
      ring
  rw [hfun]
  have hI0 : Integrable F0 := by
    have := (integrable_kinkFn (κ := κ0) cut0_shift_contDiff.continuous cut0_shift_compact p q).comp_sub_right (w + 1)
    exact this.const_mul _
  have hI1 : Integrable F1 := by
    have := (integrable_kinkFn (κ := cut1) hc1.continuous cut1_compact (ξ 1) (ξ 1)).comp_sub_right b
    exact this.const_mul _
  refine (prod_norm_le hI0 hI1 hθ).trans ?_
  have hn0 : ‖eE (ξ 0 * c0)‖ = 1 := norm_eE _
  have hn1 : ‖eE (ξ 1 * b)‖ = 1 := norm_eE _
  have N0 : ∀ α, NN α F0 = NN α (kinkFn κ0 p q) := fun α => NN_shift α (w + 1) hn0
  have N1 : ∀ α, NN α F1 = NN α (kinkFn cut1 (ξ 1) (ξ 1)) := fun α => NN_shift α b hn1
  have a1 : NN θ F0 ≤ ENNReal.ofReal (Ka * (1 + |ξ 0|) ^ (θ + δ)) := by
    rw [N0]
    refine (hA p q d hpq).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)) hKa
  have a2 : NN 0 F0 ≤ ENNReal.ofReal (Kb * (1 + |ξ 0|) ^ (0 + δ)) := by
    rw [N0]
    refine (hB p q d hpq).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)) hKb
  have a3 : NN θ F1 ≤ ENNReal.ofReal (Kc * (1 + |ξ 1|) ^ θ) := by
    rw [N1]
    refine (NN_modulated_le hθ (ξ 1)).trans ?_
    have := hC 0 0 0 (Or.inl ⟨rfl, rfl⟩)
    have h2 : NN θ (kinkFn cut1 0 0) ≤ ENNReal.ofReal Kc := by
      refine this.trans (le_of_eq ?_); simp
    calc ENNReal.ofReal ((1 + |ξ 1|) ^ θ) * NN θ (kinkFn cut1 0 0) ≤ ENNReal.ofReal ((1 + |ξ 1|) ^ θ) * ENNReal.ofReal Kc :=
          mul_le_mul' le_rfl h2
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  have a4 : NN 0 F1 ≤ ENNReal.ofReal Kd := by
    rw [N1]
    refine (NN_modulated_le le_rfl (ξ 1)).trans ?_
    have := hD 0 0 0 (Or.inl ⟨rfl, rfl⟩)
    have h2 : NN 0 (kinkFn cut1 0 0) ≤ ENNReal.ofReal Kd := by
      refine this.trans (le_of_eq ?_); simp
    simpa using h2
  set T := timeBracket ξ with hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (by
    rw [hT]; unfold timeBracket
    exact Finset.le_sup' (fun i : Option (Fin 2) => match i with | none => (1 : ℝ) | some j => Real.sqrt (1 + ξ j ^ 2)) (Finset.mem_univ none))
  have hS0 := one_add_abs_le_tb ξ 0
  have hS1 := one_add_abs_le_tb ξ 1
  have hr : ∀ (a e : ℝ), 0 ≤ a → 0 ≤ e → e ≤ 1 → (Real.sqrt 2 * T) ^ e ≤ Real.sqrt 2 * T ^ e := by
    intro a e _ he0 he1
    rw [Real.mul_rpow (Real.sqrt_nonneg _) hT0.le]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc Real.sqrt 2 ^ e ≤ Real.sqrt 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs2 he1
      _ = _ := Real.rpow_one _
  have b1 : (1 + |ξ 0|) ^ (θ + δ) ≤ Real.sqrt 2 * T ^ (θ + δ) :=
    (Real.rpow_le_rpow (by positivity) hS0 (by linarith)).trans (hr 0 _ le_rfl (by linarith) hθδ)
  have b2 : (1 + |ξ 0|) ^ (0 + δ) * (1 + |ξ 1|) ^ θ ≤ Real.sqrt 2 * T ^ (θ + δ) := by
    have h1 := Real.rpow_le_rpow (by positivity) hS0 (by linarith : 0 ≤ 0 + δ)
    have h2 := Real.rpow_le_rpow (by positivity) hS1 hθ
    calc (1 + |ξ 0|) ^ (0 + δ) * (1 + |ξ 1|) ^ θ ≤ (Real.sqrt 2 * T) ^ (0 + δ) * (Real.sqrt 2 * T) ^ θ :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (Real.sqrt 2 * T) ^ (θ + δ) := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
      _ ≤ _ := hr 0 _ le_rfl (by linarith) hθδ
  have hKaKd : 0 ≤ Ka * Kd := mul_nonneg hKa hKd
  have hKbKc : 0 ≤ Kb * Kc := mul_nonneg hKb hKc
  calc NN θ F0 * NN 0 F1 + NN 0 F0 * NN θ F1
      ≤ ENNReal.ofReal (Ka * (1 + |ξ 0|) ^ (θ + δ)) * ENNReal.ofReal Kd +
        ENNReal.ofReal (Kb * (1 + |ξ 0|) ^ (0 + δ)) * ENNReal.ofReal (Kc * (1 + |ξ 1|) ^ θ) :=
        add_le_add (mul_le_mul' a1 a4) (mul_le_mul' a2 a3)
    _ = ENNReal.ofReal (Ka * Kd * (1 + |ξ 0|) ^ (θ + δ) + Kb * Kc * ((1 + |ξ 0|) ^ (0 + δ) * (1 + |ξ 1|) ^ θ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hTp : 0 ≤ T ^ (θ + δ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left b1 hKaKd, mul_le_mul_of_nonneg_left b2 hKbKc, mul_nonneg hKaKd (Real.sqrt_nonneg 2),
          mul_nonneg hKbKc (Real.sqrt_nonneg 2), mul_nonneg (Real.sqrt_nonneg 2) hTp]

end WaveTurbulence.VineEstS5C.P4.W2.K2
