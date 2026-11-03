/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.CellOps
public import WaveTurbulence.Foundations.ApproxNT.CellBounds

/-!
# `δ(⟨x,y⟩)` on one cell equals `∫_ℝ cellInt(s) ds` (packet NT6)

For the cell amplitude `P = θ(x-p)θ(y-q)e(ξ·x+η·y)`,
`NTSP.deltaInner P = ∫_ℝ ∫∫ P(x,y) e(s⟨x,y⟩) dx dy ds` ("the Fourier transform of `δ` is `1`").
Proof: with the fixed bump `ψ = χ₀`, `μ ∫∫ ψ(μ⟨x,y⟩) P → (∫ψ) deltaInner P` by DH23 Lemma 6.7(2)
(`NTSP.ntintlem_two`), while Fourier inversion for `ψ` gives
`μ ∫∫ ψ(μ⟨x,y⟩) P = ∫ ψ̂(s/μ) cellInt(s) ds → ψ̂(0) ∫ cellInt`.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp Filter Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-- Fourier inversion for a one-dimensional Schwartz function. -/
theorem schwartz_eq_integral (f : 𝓢(ℝ, ℂ)) (v : ℝ) :
    f v = ∫ τ, 𝓕 (f : ℝ → ℂ) τ * (𝐞 (τ * v) : ℂ) := by
  have h := Continuous.fourierInv_fourier_eq f.continuous f.integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).integrable)
  have h2 := congrFun h v
  rw [Real.fourierInv_eq] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only []
  rw [Circle.smul_def, smul_eq_mul, mul_comm]
  simp [mul_comm]

/-- The bump `χ₀` as a complex Schwartz function. -/
@[expose] def chi0S : 𝓢(ℝ, ℂ) :=
  (Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp Fourier.chi0_contDiff)

theorem chi0S_apply (u : ℝ) : chi0S u = (Fourier.chi0 u : ℂ) := rfl

theorem integral_chi0S_ne_zero : ∫ u, chi0S u ≠ 0 := by
  have hint : Integrable Fourier.chi0 := Fourier.chi0_integrable
  have h1 : ∫ u, chi0S u = ((∫ u, Fourier.chi0 u : ℝ) : ℂ) := by
    simp only [chi0S_apply]; exact integral_complex_ofReal
  rw [h1, Complex.ofReal_ne_zero]
  refine ne_of_gt ?_
  have hpos : 0 < ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Fourier.chi0 u := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => Fourier.chi0_eq_one (abs_le.2 hu))]
    simp
  refine lt_of_lt_of_le hpos (setIntegral_le_integral hint (Filter.Eventually.of_forall
    fun u => Fourier.chi0_nonneg u))

theorem integral_cellFn_prod (p q ξ η : Mom d) {G : Mom d → Mom d → ℂ}
    (hG : Continuous (Function.uncurry G)) :
    ∫ x, ∫ y, G x y * cellFn p q ξ η x y =
      ∫ z : Mom d × Mom d, G z.1 z.2 * cellFn p q ξ η z.1 z.2 := by
  have hc : Continuous (fun z : Mom d × Mom d => G z.1 z.2 * cellFn p q ξ η z.1 z.2) :=
    hG.mul ((contDiff_cellIntegrand p q ξ η 0).continuous.congr (fun z => by
      simp [cellFn, pairAmp]))
  have hs : HasCompactSupport (fun z : Mom d × Mom d => G z.1 z.2 * cellFn p q ξ η z.1 z.2) := by
    refine HasCompactSupport.mul_left ?_
    refine (hasCompactSupport_cellIntegrand p q ξ η 0).mono' ?_
    intro z hz
    refine subset_tsupport _ ?_
    rw [Function.mem_support] at hz ⊢
    simpa [cellFn, pairAmp] using hz
  exact (integral_prod _ (hc.integrable_of_hasCompactSupport hs)).symm

/-- The Fourier side of `μ ∫∫ ψ(μ⟨x,y⟩) P`. -/
theorem mu_integral_cellFn (f : 𝓢(ℝ, ℂ)) {μ : ℝ} (hμ : 0 < μ) (p q ξ η : Mom d) :
    (μ : ℂ) * ∫ x, ∫ y, f (μ * inner ℝ x y) * cellFn p q ξ η x y =
      ∫ s, 𝓕 (f : ℝ → ℂ) (s / μ) * cellInt p q ξ η s := by
  have hGc : Continuous (Function.uncurry fun x y : Mom d => f (μ * inner ℝ x y)) :=
    f.continuous.comp (continuous_const.mul (continuous_fst.inner continuous_snd))
  rw [integral_cellFn_prod p q ξ η hGc]
  have hjoint : Integrable (Function.uncurry fun (z : Mom d × Mom d) (τ : ℝ) =>
      𝓕 (f : ℝ → ℂ) τ * ((𝐞 (τ * (μ * inner ℝ z.1 z.2)) : ℂ) * cellFn p q ξ η z.1 z.2))
      ((volume : Measure (Mom d × Mom d)).prod volume) := by
    have hp := (integrable_cellAmp p q).mul_prod ((𝓕 f).integrable (μ := volume))
    refine hp.norm.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine ((𝓕 f).continuous.comp continuous_snd).mul (Continuous.mul ?_ ?_)
      · exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
          (continuous_snd.mul (continuous_const.mul
            ((continuous_fst.comp continuous_fst).inner (continuous_snd.comp continuous_fst))))
      · exact ((contDiff_cellIntegrand p q ξ η 0).continuous.congr (fun z => by
          simp [pairAmp])).comp continuous_fst
    · obtain ⟨z, τ⟩ := w
      simp only [Function.uncurry_apply_pair, norm_mul, cellFn, pairAmp, Circle.norm_smul,
        Circle.norm_coe, one_mul, SchwartzMap.fourier_coe]
      rw [mul_comm]
  calc (μ : ℂ) * ∫ z : Mom d × Mom d, f (μ * inner ℝ z.1 z.2) * cellFn p q ξ η z.1 z.2
      = (μ : ℂ) * ∫ z : Mom d × Mom d, ∫ τ, 𝓕 (f : ℝ → ℂ) τ *
          ((𝐞 (τ * (μ * inner ℝ z.1 z.2)) : ℂ) * cellFn p q ξ η z.1 z.2) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [schwartz_eq_integral f, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only; ring
    _ = (μ : ℂ) * ∫ τ, ∫ z : Mom d × Mom d, 𝓕 (f : ℝ → ℂ) τ *
          ((𝐞 (τ * (μ * inner ℝ z.1 z.2)) : ℂ) * cellFn p q ξ η z.1 z.2) := by
        rw [integral_integral_swap hjoint]
    _ = (μ : ℂ) * ∫ τ, 𝓕 (f : ℝ → ℂ) τ * cellInt p q ξ η (μ * τ) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only
        rw [integral_const_mul, cellInt_eq_prod]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [cellFn, pairAmp, Circle.smul_def, smul_eq_mul]
        rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
        congr 3
        ring
    _ = ∫ s, 𝓕 (f : ℝ → ℂ) (s / μ) * cellInt p q ξ η s := by
        have h := Measure.integral_comp_mul_left
          (fun s : ℝ => 𝓕 (f : ℝ → ℂ) (s / μ) * cellInt p q ξ η s) μ
        simp only [mul_div_cancel_left₀ _ hμ.ne'] at h
        rw [h, abs_of_pos (inv_pos.2 hμ), Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
          mul_inv_cancel₀ (by exact_mod_cast hμ.ne'), one_mul]

theorem tendsto_fourier_side (hd : 2 ≤ d) (f : 𝓢(ℝ, ℂ)) (p q ξ η : Mom d) :
    Tendsto (fun μ : ℝ => ∫ s, 𝓕 (f : ℝ → ℂ) (s / μ) * cellInt p q ξ η s) atTop
      (𝓝 (𝓕 (f : ℝ → ℂ) 0 * ∫ s, cellInt p q ξ η s)) := by
  rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => (∫ u, ‖f u‖) * ‖cellInt p q ξ η s‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun μ => ((𝓕 f).continuous.comp (continuous_id.div_const μ)
      |>.congr (fun s => by simp [SchwartzMap.fourier_coe])).mul
        (continuous_cellInt p q ξ η) |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun μ => Filter.Eventually.of_forall fun s => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (Real.norm_fourier_le_integral_norm _ _) (norm_nonneg _)
  · exact ((integrable_cellInt hd p q ξ η).norm.const_mul _)
  · refine Filter.Eventually.of_forall fun s => ?_
    refine Tendsto.mul_const _ ?_
    have hc : Continuous (𝓕 (f : ℝ → ℂ)) := by rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
    have h0 : Tendsto (fun μ : ℝ => s / μ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    exact (hc.tendsto 0).comp h0

theorem amp_cellAmp_eq (p q ξ η : Mom d) :
    NTSP.amp 2 (fun x y => 1 * cellAmp p q x y) p q ξ η = cellFn p q ξ η := by
  funext x y
  rw [NTSP.amp, chiScaled_mul_cellAmp, cellFn, pairAmp, Circle.smul_def, smul_eq_mul, mul_comm,
    one_mul]

/-- `δ(⟨x,y⟩)` on one cell is the integral of the cell's oscillatory integral. -/
theorem deltaInner_cellFn (hd : 3 ≤ d) (p q ξ η : Mom d) :
    NTSP.deltaInner (cellFn p q ξ η) = ∫ s, cellInt p q ξ η s := by
  have hd2 : 2 ≤ d := by omega
  set ψ : ℝ → ℂ := ⇑chi0S
  have hψm : Measurable ψ := chi0S.continuous.measurable
  have hW : Integrable (fun u => ‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - (1 / 4 : ℝ))) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.mul_right ?_
    exact (Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero).norm
  have hB := ntBounds_cellAmp (d := d) 1 (c := 1) (by simp) p q
  have hlim1 : Tendsto (fun μ : ℝ => (μ : ℂ) * ∫ x, ∫ y, ψ (μ * inner ℝ x y) *
      cellFn p q ξ η x y) atTop (𝓝 ((∫ u, ψ u) * NTSP.deltaInner (cellFn p q ξ η))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set K := 2 * NTSP.ntConst d (1 / 4) * cellConst d 1 * 2 ^ (2 * d) * (1 + ‖ξ‖ + ‖η‖) *
      ∫ u, ‖ψ u‖ * Real.sqrt (1 + u ^ 2) ^ (1 - (1 / 4 : ℝ))
    have hbound : ∀ᶠ μ : ℝ in atTop, ‖(μ : ℂ) * (∫ x, ∫ y, ψ (μ * inner ℝ x y) *
        cellFn p q ξ η x y) - (∫ u, ψ u) * NTSP.deltaInner (cellFn p q ξ η)‖ ≤
        K * μ ^ (-(1 - 2 * (1 / 4 : ℝ))) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with μ hμ
      have h := NTSP.ntintlem_two hd2 (η := 1 / 4) (by norm_num) (by norm_num) le_rfl hB
        (by norm_num : (1 : ℝ) ≤ 2) hμ hψm hW p q ξ η
      rw [amp_cellAmp_eq] at h
      refine h.trans (le_of_eq ?_)
      simp only [K]; ring
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
    have h0 : Tendsto (fun μ : ℝ => μ ^ (-(1 - 2 * (1 / 4 : ℝ)))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    simpa using h0.const_mul K
  have hlim2 : Tendsto (fun μ : ℝ => (μ : ℂ) * ∫ x, ∫ y, ψ (μ * inner ℝ x y) *
      cellFn p q ξ η x y) atTop (𝓝 (𝓕 (chi0S : ℝ → ℂ) 0 * ∫ s, cellInt p q ξ η s)) := by
    refine (tendsto_fourier_side hd2 chi0S p q ξ η).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
    exact (mu_integral_cellFn chi0S hμ p q ξ η).symm
  have hF0 : 𝓕 (chi0S : ℝ → ℂ) 0 = ∫ u, ψ u := by
    rw [Real.fourier_real_eq]; simp [ψ]
  have heq := tendsto_nhds_unique hlim1 hlim2
  rw [hF0] at heq
  exact mul_left_cancel₀ integral_chi0S_ne_zero heq

end WaveTurbulence.ApproxNT
