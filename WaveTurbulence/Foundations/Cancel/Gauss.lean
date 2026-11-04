/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian regularization of the phases `e^{πiαu}` (DH21 §7.1)

DH21 (gausspv) (L1713) defines the Gaussian principal value `[G]∫ F = lim_{θ→0} ∫ F(α) e^{-πθ²α²} dα`. In
the proofs of DH21 Lemmas 7.1, 7.3 and Prop 7.5 the variable `α` enters through a phase `e^{πiαu}`, and

* `∫ e^{πiux} e^{-πθ²x²} dx = θ⁻¹ e^{-πu²/(4θ²)} =: gk θ u` (`ft_gw`), an approximate identity whose mass
  on each half-line is `1` (DH21 (approxid), L1745);
* `∫ (θπix) e^{πiux} e^{-πθ²x²} dx = -(πu/(2θ²)) e^{-πu²/(4θ²)} =: hk θ u` (`ft_xgw`). On `u > 0` this is
  minus an approximate identity of mass `1` (`integral_neg_hk`). This kernel extracts the coefficient of
  `χ_∞(α)/(πiα)`. Its sign is the sign of FINDINGS F61 (DH21 Lemma 7.3 needs `−I_μ`).

Main results: the two Fourier identities, the masses (`integral_gk_le_one`, `tendsto_integral_gk`,
`integral_neg_hk`), and the one-sided approximate identities (`tendsto_integral_gk_mul`,
`tendsto_integral_neg_hk_mul`) for continuous functions on `[0, c]`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology

namespace WaveTurbulence.Cancel

/-- The Gaussian weight `e^{-πθ²x²}`. -/
@[expose] noncomputable def gw (θ x : ℝ) : ℝ := Real.exp (-π * θ ^ 2 * x ^ 2)

/-- The kernel `gk θ u = θ⁻¹ e^{-πu²/(4θ²)}`. -/
@[expose] noncomputable def gk (θ u : ℝ) : ℝ := θ⁻¹ * Real.exp (-π * u ^ 2 / (4 * θ ^ 2))

/-- The kernel `hk θ u = -(πu/(2θ²)) e^{-πu²/(4θ²)}`. -/
@[expose] noncomputable def hk (θ u : ℝ) : ℝ := -(π * u / (2 * θ ^ 2)) * Real.exp (-π * u ^ 2 / (4 * θ ^ 2))

theorem gw_pos (θ x : ℝ) : 0 < gw θ x := Real.exp_pos _

theorem gw_le_one (θ x : ℝ) : gw θ x ≤ 1 := by
  unfold gw
  rw [Real.exp_le_one_iff]
  have := Real.pi_pos
  have : 0 ≤ θ ^ 2 * x ^ 2 := by positivity
  nlinarith

@[fun_prop] theorem continuous_gw (θ : ℝ) : Continuous (gw θ) := by
  unfold gw; fun_prop

theorem gk_nonneg {θ : ℝ} (hθ : 0 < θ) (u : ℝ) : 0 ≤ gk θ u :=
  mul_nonneg (inv_nonneg.2 hθ.le) (Real.exp_pos _).le

theorem integrable_gw {θ : ℝ} (hθ : 0 < θ) : Integrable (gw θ) := by
  have h := integrable_exp_neg_mul_sq (b := π * θ ^ 2) (by positivity)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [gw]; ring_nf

/-- **`∫ e^{πiux} e^{-πθ²x²} dx = θ⁻¹ e^{-πu²/(4θ²)}`.** -/
theorem ft_gw {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    ∫ x : ℝ, cexp (π * I * (u * x)) * (gw θ x : ℂ) = (gk θ u : ℂ) := by
  have hb : 0 < ((π * θ ^ 2 : ℝ) : ℂ).re := by simp only [ofReal_re]; positivity
  have h := fourierIntegral_gaussian hb ((π * u : ℝ) : ℂ)
  have e1 : (fun x : ℝ => cexp (π * I * (u * x)) * (gw θ x : ℂ)) =
      fun x : ℝ => cexp (I * ((π * u : ℝ) : ℂ) * x) * cexp (-((π * θ ^ 2 : ℝ) : ℂ) * x ^ 2) := by
    funext x
    simp only [gw, ofReal_exp]
    congr 1
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [e1, h]
  have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have e2 : ((π : ℂ) / ((π * θ ^ 2 : ℝ) : ℂ)) = (((θ⁻¹) ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  have e3 : ((((θ⁻¹) ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((θ⁻¹ : ℝ) : ℂ) := by
    have h0 : (0 : ℝ) ≤ (θ⁻¹) ^ 2 := by positivity
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow h0,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (inv_nonneg.2 hθ.le)]
  rw [e2, e3, gk]
  push_cast
  congr 1
  congr 1
  field_simp

theorem integrable_mul_gw {θ : ℝ} (hθ : 0 < θ) : Integrable fun x => x * gw θ x := by
  have h := integrable_mul_exp_neg_mul_sq (b := π * θ ^ 2) (by positivity)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [gw]; ring_nf

/-- The phase times the weight, `e^{πiux} e^{-πθ²x²}`. -/
theorem integrable_phase_gw {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    Integrable fun x : ℝ => cexp (π * I * (u * x)) * (gw θ x : ℂ) := by
  refine ((integrable_gw hθ).ofReal (𝕜 := ℂ)).bdd_mul (c := 1) ?_ ?_
  · exact (Continuous.cexp (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_exp]
    simp

theorem integrable_x_phase_gw {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    Integrable fun x : ℝ => (x : ℂ) * (cexp (π * I * (u * x)) * (gw θ x : ℂ)) := by
  refine Integrable.mono' (integrable_mul_gw hθ).norm ?_ (Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) * (cexp (π * I * (u * x)) * (gw θ x : ℂ))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_exp, norm_mul, Complex.norm_real, Complex.norm_real]
    simp

theorem integral_x_phase_gw {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    ∫ x : ℝ, (x : ℂ) * (cexp (π * I * (u * x)) * (gw θ x : ℂ)) =
      (I * u / (2 * θ ^ 2)) * (gk θ u : ℂ) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (π * I * (u * x)) * (gw θ x : ℂ))
      ((π * I * u) * (cexp (π * I * (u * x)) * (gw θ x : ℂ)) -
        (2 * π * θ ^ 2 : ℂ) * ((x : ℂ) * (cexp (π * I * (u * x)) * (gw θ x : ℂ)))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => cexp (π * I * (u * x)))
        (cexp (π * I * (u * x)) * (π * I * u)) x := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (π * I * u)).cexp
      have h2 := this.comp_ofReal (z := x)
      simpa [mul_assoc, mul_comm, mul_left_comm] using h2
    have h3 : HasDerivAt (fun x : ℝ => gw θ x) (gw θ x * (-π * θ ^ 2 * (2 * x))) x := by
      have := ((hasDerivAt_pow 2 x).const_mul (-π * θ ^ 2)).exp
      simpa [gw, mul_comm, mul_assoc] using this
    have h4 := h1.mul h3.ofReal_comp
    convert h4 using 1
    push_cast
    ring
  have hint := ((integrable_phase_gw hθ u).const_mul (π * I * u)).sub
    ((integrable_x_phase_gw hθ u).const_mul (2 * π * θ ^ 2 : ℂ))
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hint (integrable_phase_gw hθ u)
  rw [integral_sub ((integrable_phase_gw hθ u).const_mul _)
    ((integrable_x_phase_gw hθ u).const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, ft_gw hθ u] at h0
  have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  generalize (∫ a : ℝ, (a : ℂ) * (cexp (π * I * (u * a)) * (gw θ a : ℂ))) = J at h0 ⊢
  have h1 : (π : ℂ) * (2 * θ ^ 2 * J - I * u * gk θ u) = 0 := by linear_combination -h0
  have h2 := (mul_eq_zero.1 h1).resolve_left hπ
  field_simp
  linear_combination h2

/-- **`∫ (θπix) e^{πiux} e^{-πθ²x²} dx = -(πu/(2θ²)) e^{-πu²/(4θ²)}`.** -/
theorem ft_xgw {θ : ℝ} (hθ : 0 < θ) (u : ℝ) :
    ∫ x : ℝ, (θ * π * I * x) * (cexp (π * I * (u * x)) * (gw θ x : ℂ)) = (hk θ u : ℂ) := by
  have e : (fun x : ℝ => (θ * π * I * x) * (cexp (π * I * (u * x)) * (gw θ x : ℂ))) =
      fun x : ℝ => (θ * π * I : ℂ) * ((x : ℂ) * (cexp (π * I * (u * x)) * (gw θ x : ℂ))) := by
    funext x; ring
  have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ.ne'
  rw [e, MeasureTheory.integral_const_mul, integral_x_phase_gw hθ u, gk, hk]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-! ### Approximate identities -/

/-- **A one-sided approximate identity.** Continuous kernels `k θ ≥ 0` on `[0, c]` whose mass tends to `1`
and whose mass on `[δ, c]` tends to `0` for every `δ > 0` satisfy `∫_0^c k θ f → f(0)` for continuous `f`. -/
theorem tendsto_integral_mul_of_approxId {k : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hkc : ∀ θ, 0 < θ → Continuous (k θ)) (hk0 : ∀ θ, 0 < θ → ∀ u ∈ Icc 0 c, 0 ≤ k θ u)
    (hmass : Tendsto (fun θ => ∫ u in (0 : ℝ)..c, k θ u) (𝓝[>] 0) (𝓝 1))
    (htail : ∀ δ ∈ Ioo 0 c, Tendsto (fun θ => ∫ u in δ..c, k θ u) (𝓝[>] 0) (𝓝 0))
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 c)) :
    Tendsto (fun θ => ∫ u in (0 : ℝ)..c, (k θ u : ℂ) * f u) (𝓝[>] 0) (𝓝 (f 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hc.le⟩)
  have h0c : (0 : ℝ) ∈ Icc 0 c := ⟨le_rfl, hc.le⟩
  obtain ⟨δ0, hδ0, hδ⟩ := Metric.continuousWithinAt_iff.1 (hf 0 h0c) (ε / 8) (by positivity)
  set δ := min (δ0 / 2) (c / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδc : δ < c := (min_le_right _ _).trans_lt (by linarith)
  have hδ' : ∀ u ∈ Icc 0 δ, ‖f u - f 0‖ ≤ ε / 8 := by
    intro u hu
    have hu' : u ∈ Icc 0 c := ⟨hu.1, hu.2.trans hδc.le⟩
    have : dist u 0 < δ0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
      exact lt_of_le_of_lt hu.2 ((min_le_left _ _).trans_lt (by linarith))
    have := (hδ hu' this).le
    rwa [dist_eq_norm] at this
  have hmass' := (Metric.tendsto_nhds.1 hmass) (min 1 (ε / (4 * (‖f 0‖ + 1)))) (by positivity)
  have htail' := (Metric.tendsto_nhds.1 (htail δ ⟨hδpos, hδc⟩)) (ε / (8 * (2 * M + 1)))
    (by positivity)
  filter_upwards [hmass', htail', self_mem_nhdsWithin] with θ h1 h2 hθ
  have hθ : 0 < θ := hθ
  rw [Real.dist_eq, sub_zero] at h2
  rw [Real.dist_eq] at h1
  have hk := hkc θ hθ
  have hk0θ := hk0 θ hθ
  set m := ∫ u in (0 : ℝ)..c, k θ u with hm
  have hm2 : m ≤ 2 := by
    have := (abs_lt.1 h1).2; have : min 1 (ε / (4 * (‖f 0‖ + 1))) ≤ 1 := min_le_left _ _; linarith
  have hd : |m - 1| < ε / (4 * (‖f 0‖ + 1)) := h1.trans_le (min_le_right _ _)
  -- continuity of the integrands
  have hgc : ContinuousOn (fun u => k θ u * ‖f u - f 0‖) (Icc 0 c) :=
    hk.continuousOn.mul ((hf.sub continuousOn_const).norm)
  have hFc : ContinuousOn (fun u => (k θ u : ℂ) * (f u - f 0)) (Icc 0 c) :=
    (continuous_ofReal.comp hk).continuousOn.mul (hf.sub continuousOn_const)
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ c → Icc a b ⊆ Icc 0 c := fun a b ha hab hb u hu =>
    ⟨ha.trans hu.1, hu.2.trans hb⟩
  have igc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ c →
      IntervalIntegrable (fun u => k θ u * ‖f u - f 0‖) volume a b := fun a b ha hab hb =>
    (hgc.mono (hsub a b ha hab hb)).intervalIntegrable_of_Icc hab
  have ikc : ∀ a b, IntervalIntegrable (k θ) volume a b := fun a b => hk.intervalIntegrable a b
  -- the decomposition `∫ k f - f 0 = ∫ k (f - f 0) + f 0 (m - 1)`
  have hdec : (∫ u in (0 : ℝ)..c, (k θ u : ℂ) * f u) - f 0 =
      (∫ u in (0 : ℝ)..c, (k θ u : ℂ) * (f u - f 0)) + f 0 * ((m : ℂ) - 1) := by
    have e1 : (∫ u in (0 : ℝ)..c, (k θ u : ℂ) * (f u - f 0)) =
        (∫ u in (0 : ℝ)..c, (k θ u : ℂ) * f u) - (m : ℂ) * f 0 := by
      have i1 : IntervalIntegrable (fun u => (k θ u : ℂ) * f u) volume 0 c :=
        ((continuous_ofReal.comp hk).continuousOn.mul hf).intervalIntegrable_of_Icc hc.le
      have i2 : IntervalIntegrable (fun u => (k θ u : ℂ) * f 0) volume 0 c :=
        (continuous_ofReal.comp hk |>.mul continuous_const).intervalIntegrable 0 c
      rw [show (fun u => (k θ u : ℂ) * (f u - f 0)) = fun u => (k θ u : ℂ) * f u - (k θ u : ℂ) * f 0
        by funext u; ring, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_ofReal]
    rw [e1]; ring
  -- the bound on `∫ k (f - f 0)`
  have hmain : ‖∫ u in (0 : ℝ)..c, (k θ u : ℂ) * (f u - f 0)‖ ≤ ε / 8 * m + 2 * M * (∫ u in δ..c, k θ u) := by
    have n1 : ‖∫ u in (0 : ℝ)..c, (k θ u : ℂ) * (f u - f 0)‖ ≤
        ∫ u in (0 : ℝ)..c, k θ u * ‖f u - f 0‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm hc.le).trans_eq ?_
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hc.le] at hu
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk0θ u hu)]
    have s1 : ∫ u in (0 : ℝ)..c, k θ u * ‖f u - f 0‖ =
        (∫ u in (0 : ℝ)..δ, k θ u * ‖f u - f 0‖) + ∫ u in δ..c, k θ u * ‖f u - f 0‖ :=
      (intervalIntegral.integral_add_adjacent_intervals (igc 0 δ le_rfl hδpos.le hδc.le)
        (igc δ c hδpos.le hδc.le le_rfl)).symm
    have b1 : ∫ u in (0 : ℝ)..δ, k θ u * ‖f u - f 0‖ ≤ ∫ u in (0 : ℝ)..δ, k θ u * (ε / 8) := by
      refine intervalIntegral.integral_mono_on hδpos.le (igc 0 δ le_rfl hδpos.le hδc.le)
        ((ikc 0 δ).mul_const _) fun u hu => ?_
      exact mul_le_mul_of_nonneg_left (hδ' u hu) (hk0θ u ⟨hu.1, hu.2.trans hδc.le⟩)
    have b2 : ∫ u in δ..c, k θ u * ‖f u - f 0‖ ≤ ∫ u in δ..c, k θ u * (2 * M) := by
      refine intervalIntegral.integral_mono_on hδc.le (igc δ c hδpos.le hδc.le le_rfl)
        ((ikc δ c).mul_const _) fun u hu => ?_
      have hu' : u ∈ Icc 0 c := ⟨hδpos.le.trans hu.1, hu.2⟩
      refine mul_le_mul_of_nonneg_left ?_ (hk0θ u hu')
      calc ‖f u - f 0‖ ≤ ‖f u‖ + ‖f 0‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM u hu') (hM 0 h0c)
        _ = 2 * M := by ring
    have hsplitm : m = (∫ u in (0 : ℝ)..δ, k θ u) + ∫ u in δ..c, k θ u :=
      (intervalIntegral.integral_add_adjacent_intervals (ikc 0 δ) (ikc δ c)).symm
    have htn : 0 ≤ ∫ u in δ..c, k θ u :=
      intervalIntegral.integral_nonneg hδc.le fun u hu => hk0θ u ⟨hδpos.le.trans hu.1, hu.2⟩
    rw [intervalIntegral.integral_mul_const] at b1 b2
    have : (∫ u in (0 : ℝ)..δ, k θ u) * (ε / 8) ≤ ε / 8 * m := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  rw [dist_eq_norm, hdec]
  calc ‖(∫ u in (0 : ℝ)..c, (k θ u : ℂ) * (f u - f 0)) + f 0 * ((m : ℂ) - 1)‖
      ≤ ‖∫ u in (0 : ℝ)..c, (k θ u : ℂ) * (f u - f 0)‖ + ‖f 0‖ * |m - 1| := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_mul, show ((m : ℂ) - 1) = ((m - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
    _ < ε := by
        have h3 : ‖f 0‖ * |m - 1| ≤ ε / 4 := by
          have hp : 0 < ‖f 0‖ + 1 := by positivity
          calc ‖f 0‖ * |m - 1| ≤ (‖f 0‖ + 1) * (ε / (4 * (‖f 0‖ + 1))) :=
                mul_le_mul (by linarith) hd.le (abs_nonneg _) hp.le
            _ = ε / 4 := by field_simp
        have h4 : 2 * M * (∫ u in δ..c, k θ u) ≤ ε / 8 := by
          have hp : 0 < 2 * M + 1 := by positivity
          have := h2
          rw [abs_lt] at this
          calc 2 * M * (∫ u in δ..c, k θ u) ≤ (2 * M + 1) * (ε / (8 * (2 * M + 1))) := by
                refine mul_le_mul (by linarith) this.2.le ?_ hp.le
                exact intervalIntegral.integral_nonneg hδc.le fun u hu =>
                  hk0θ u ⟨hδpos.le.trans hu.1, hu.2⟩
            _ = ε / 8 := by field_simp
        nlinarith [hmain]
/-! ### Masses -/

@[fun_prop] theorem continuous_gk (θ : ℝ) : Continuous (gk θ) := by unfold gk; fun_prop

@[fun_prop] theorem continuous_hk (θ : ℝ) : Continuous (hk θ) := by unfold hk; fun_prop

/-- `∫_0^c gk θ = 2 ∫_0^{c/(2θ)} e^{-πv²} dv`. -/
theorem integral_gk_eq {θ : ℝ} (hθ : 0 < θ) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, gk θ u = 2 * ∫ v in (0 : ℝ)..(c / (2 * θ)), Real.exp (-π * v ^ 2) := by
  have h2 : (2 * θ)⁻¹ ≠ 0 := by positivity
  have e : (fun u => gk θ u) = fun u => θ⁻¹ * Real.exp (-π * ((2 * θ)⁻¹ * u) ^ 2) := by
    funext u; unfold gk; congr 2; field_simp; ring
  rw [e, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun v => Real.exp (-π * v ^ 2)) h2]
  simp only [mul_zero, smul_eq_mul, inv_inv]
  rw [show (2 * θ)⁻¹ * c = c / (2 * θ) by ring]
  field_simp

theorem integral_gauss_Ioi_half : ∫ v in Ioi (0 : ℝ), Real.exp (-π * v ^ 2) = 1 / 2 := by
  rw [integral_gaussian_Ioi, div_self Real.pi_ne_zero, Real.sqrt_one]

theorem integrableOn_gauss_Ioi : IntegrableOn (fun v : ℝ => Real.exp (-π * v ^ 2)) (Ioi 0) :=
  (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn

theorem integral_gauss_le_half {y : ℝ} (hy : 0 ≤ y) :
    ∫ v in (0 : ℝ)..y, Real.exp (-π * v ^ 2) ≤ 1 / 2 := by
  rw [intervalIntegral.integral_of_le hy, ← integral_gauss_Ioi_half]
  refine setIntegral_mono_set integrableOn_gauss_Ioi
    (Eventually.of_forall fun v => (Real.exp_pos _).le) (Eventually.of_forall ?_)
  intro v hv
  exact hv.1

theorem tendsto_div_two_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun θ : ℝ => c / (2 * θ)) (𝓝[>] 0) atTop := by
  have : Tendsto (fun θ : ℝ => (2 * θ)⁻¹) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        exact mul_pos two_pos hθ
    exact (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h1
  refine (this.const_mul_atTop hc).congr fun θ => ?_
  ring

/-- **The mass of `gk θ` on `[0, c]` tends to `1`** (DH21 (approxid)). -/
theorem tendsto_integral_gk {c : ℝ} (hc : 0 < c) :
    Tendsto (fun θ => ∫ u in (0 : ℝ)..c, gk θ u) (𝓝[>] 0) (𝓝 1) := by
  have h := (intervalIntegral_tendsto_integral_Ioi 0 integrableOn_gauss_Ioi
    (tendsto_div_two_mul hc)).const_mul 2
  rw [integral_gauss_Ioi_half, show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact (integral_gk_eq hθ c).symm

theorem integral_gk_le_one {θ : ℝ} (hθ : 0 < θ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ u in (0 : ℝ)..c, gk θ u ≤ 1 := by
  rw [integral_gk_eq hθ]
  have := integral_gauss_le_half (y := c / (2 * θ)) (by positivity)
  linarith

theorem tendsto_integral_gk_tail {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun θ => ∫ u in δ..c, gk θ u) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_integral_gk hc).sub (tendsto_integral_gk hδ)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact intervalIntegral.integral_interval_sub_left ((continuous_gk θ).intervalIntegrable _ _)
    ((continuous_gk θ).intervalIntegrable _ _)

/-- `hk θ` is the derivative of `e^{-πu²/(4θ²)}`. -/
theorem hasDerivAt_hk (θ u : ℝ) :
    HasDerivAt (fun u => Real.exp (-π * u ^ 2 / (4 * θ ^ 2))) (hk θ u) u := by
  have := (((hasDerivAt_pow 2 u).const_mul (-π)).div_const (4 * θ ^ 2)).exp
  convert this using 1
  unfold hk
  by_cases hθ : θ = 0
  · subst hθ; simp
  field_simp
  ring

/-- **`∫_0^c (-hk θ) = 1 - e^{-πc²/(4θ²)}`**: `-hk θ` is an approximate identity of mass `→ 1`. -/
theorem integral_neg_hk (θ c : ℝ) :
    ∫ u in (0 : ℝ)..c, -hk θ u = 1 - Real.exp (-π * c ^ 2 / (4 * θ ^ 2)) := by
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_hk θ u) ((continuous_hk θ).intervalIntegrable _ _)]
  simp

theorem tendsto_exp_neg_div_sq {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun θ : ℝ => Real.exp (-π * c ^ 2 / (4 * θ ^ 2))) (𝓝[>] 0) (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun θ : ℝ => θ ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact pow_pos hθ 2
  have h2 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h1
  have hc2 : 0 < c ^ 2 := by positivity
  have hneg : -π * c ^ 2 / 4 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith [mul_pos Real.pi_pos hc2]) (by norm_num)
  refine (h2.const_mul_atTop_of_neg hneg).congr fun θ => ?_
  simp only [Function.comp]
  field_simp

theorem tendsto_integral_neg_hk {c : ℝ} (hc : 0 < c) :
    Tendsto (fun θ => ∫ u in (0 : ℝ)..c, -hk θ u) (𝓝[>] 0) (𝓝 1) := by
  have h := (tendsto_exp_neg_div_sq hc.ne').const_sub 1
  rw [sub_zero] at h
  exact h.congr fun θ => (integral_neg_hk θ c).symm

theorem tendsto_integral_neg_hk_tail {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun θ => ∫ u in δ..c, -hk θ u) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_integral_neg_hk hc).sub (tendsto_integral_neg_hk hδ)
  rw [sub_self] at h
  refine h.congr' (Eventually.of_forall fun θ => ?_)
  exact intervalIntegral.integral_interval_sub_left ((continuous_hk θ).neg.intervalIntegrable _ _)
    ((continuous_hk θ).neg.intervalIntegrable _ _)

theorem neg_hk_nonneg {θ u : ℝ} (hu : 0 ≤ u) : 0 ≤ -hk θ u := by
  unfold hk
  rw [neg_mul, neg_neg]
  exact mul_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le hu) (by positivity)) (Real.exp_pos _).le

/-- **One-sided approximate identity for `gk`** (DH21 (approxid)). -/
theorem tendsto_integral_gk_mul {c : ℝ} (hc : 0 < c) {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 c)) :
    Tendsto (fun θ => ∫ u in (0 : ℝ)..c, (gk θ u : ℂ) * f u) (𝓝[>] 0) (𝓝 (f 0)) :=
  tendsto_integral_mul_of_approxId hc (fun θ _ => continuous_gk θ)
    (fun _ hθ u _ => gk_nonneg hθ u) (tendsto_integral_gk hc)
    (fun _ hδ => tendsto_integral_gk_tail hδ.1 hc) hf

/-- **One-sided approximate identity for `hk`**: `∫_0^c hk θ f → -f(0)` (the F61 sign). -/
theorem tendsto_integral_hk_mul {c : ℝ} (hc : 0 < c) {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 c)) :
    Tendsto (fun θ => ∫ u in (0 : ℝ)..c, (hk θ u : ℂ) * f u) (𝓝[>] 0) (𝓝 (-f 0)) := by
  have h := (tendsto_integral_mul_of_approxId (k := fun θ u => -hk θ u) hc
    (fun θ _ => (continuous_hk θ).neg) (fun θ _ u hu => neg_hk_nonneg hu.1)
    (tendsto_integral_neg_hk hc) (fun δ hδ => tendsto_integral_neg_hk_tail hδ.1 hc) hf).neg
  refine h.congr fun θ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun u _ => ?_
  push_cast; ring

end WaveTurbulence.Cancel
