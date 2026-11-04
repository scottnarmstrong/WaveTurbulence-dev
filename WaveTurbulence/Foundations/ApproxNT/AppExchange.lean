/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.AppCellBound
public import WaveTurbulence.Foundations.ApproxNT.AppTools

/-!
# Exchanging `p.v.` and `δ` with superpositions of cells (packet NT6)

For `F(x,y) = ∑_a ∫ h_a(τ) P_a(τ; x, y) dν(τ)`, a finite sum of superpositions of cell functions
`P_a(τ) = cellFn p_a q_a (ξ_a τ) (η_a τ)` with integrable weights `h_a`:

* `pvOp F = ∑_a ∫ h_a(τ) pvOp(P_a(τ)) dν` (Fubini at each truncation `s`, the kernel being bounded
  by `2s`; then dominated convergence with the uniform bound of DH21 Lemma 6.3);
* `deltaInner F = ∑_a ∫ h_a(τ) deltaInner(P_a(τ)) dν` (Fubini on each hyperplane `x^⊥`, then on
  `(x, τ)`; the joint measurability of `(x, τ) ↦ |x|⁻¹ ∫_{x^⊥} P_a(τ; x, w) dw` comes from its
  representation as a pointwise limit of `μ ∫ ψ₀(μ⟨x,y⟩) P_a(τ; x, y) dy`, DH23 Lemma 6.7's slice
  analysis `NTSP.norm_psi_amp_sub_le`).

Also the measurability of `cellOp` in the frequencies.
-/

public section

noncomputable section

open MeasureTheory Finset Filter Topology Set
open scoped ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-! ### Cell functions -/

theorem continuous_cellFn_all (p q : Mom d) :
    Continuous (fun v : (Mom d × Mom d) × (Mom d × Mom d) =>
      cellFn p q v.1.1 v.1.2 v.2.1 v.2.2) := by
  simp only [cellFn, pairAmp, cellAmp, Circle.smul_def, smul_eq_mul]
  refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp ?_)).mul ?_
  · exact ((continuous_fst.comp continuous_snd).inner (continuous_fst.comp continuous_fst)).add
      ((continuous_snd.comp continuous_snd).inner (continuous_snd.comp continuous_fst))
  · exact (continuous_thetaC.comp ((continuous_fst.comp continuous_snd).sub continuous_const)).mul
      (continuous_thetaC.comp ((continuous_snd.comp continuous_snd).sub continuous_const))

theorem norm_cellFn (p q ξ η x y : Mom d) : ‖cellFn p q ξ η x y‖ = ‖cellAmp p q x y‖ := by
  rw [cellFn, pairAmp, Circle.norm_smul]

/-! ### The principal value -/

/-- The kernel `χ_∞(s⟨x,y⟩)/⟨x,y⟩` of the `s`-truncated principal value. -/
@[expose] def pvKer (s : ℝ) (x y : Mom d) : ℂ :=
  (((1 - Fourier.chi0 (s * inner ℝ x y)) / inner ℝ x y : ℝ) : ℂ)

theorem measurable_pvKer (s : ℝ) : Measurable (fun z : Mom d × Mom d => pvKer s z.1 z.2) := by
  have hc : Continuous fun z : Mom d × Mom d => inner ℝ z.1 z.2 :=
    continuous_fst.inner continuous_snd
  exact Complex.measurable_ofReal.comp ((measurable_const.sub
    ((Fourier.chi0_contDiff (n := 0)).continuous.measurable.comp
      (measurable_const.mul hc.measurable))).div hc.measurable)

theorem norm_pvKer_le {s : ℝ} (hs : 0 < s) (x y : Mom d) : ‖pvKer s x y‖ ≤ 2 * s := by
  rw [pvKer, Complex.norm_real, Real.norm_eq_abs]
  set u := inner ℝ x y
  by_cases hu : |s * u| ≤ 1 / 2
  · rw [Fourier.chi0_eq_one hu]; simp only [sub_self, zero_div, abs_zero]; positivity
  · push Not at hu
    rw [abs_mul, abs_of_pos hs] at hu
    have hu0 : 0 < |u| := by
      rcases eq_or_ne u 0 with h | h
      · rw [h, abs_zero, mul_zero] at hu; linarith
      · exact abs_pos.2 h
    have h1 : |1 - Fourier.chi0 (s * u)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [Fourier.chi0_nonneg (s * u), Fourier.chi0_le_one (s * u)]
    rw [abs_div, div_le_iff₀ hu0]
    nlinarith

theorem pvTrunc_eq_integral_prod {s : ℝ} {F : Mom d → Mom d → ℂ}
    (hF : Integrable (fun z : Mom d × Mom d => pvKer s z.1 z.2 * F z.1 z.2)) :
    pvTrunc s F = ∫ z : Mom d × Mom d, pvKer s z.1 z.2 * F z.1 z.2 := by
  rw [pvTrunc_eq_integral]
  exact (integral_prod _ hF).symm

variable {T : Type*} [MeasurableSpace T] {ν : Measure T} [SFinite ν]

theorem measurable_cellFn_param (p q : Mom d) {ξ η : T → Mom d} (hξ : Measurable ξ)
    (hη : Measurable η) :
    Measurable (fun z : (Mom d × Mom d) × T => cellFn p q (ξ z.2) (η z.2) z.1.1 z.1.2) := by
  have h1 : Measurable (fun z : (Mom d × Mom d) × T => ((ξ z.2, η z.2), z.1)) :=
    ((hξ.comp measurable_snd).prodMk (hη.comp measurable_snd)).prodMk measurable_fst
  have h2 := (continuous_cellFn_all p q).measurable.comp h1
  exact h2

/-- One superposition, at a fixed truncation `s > 0`: Fubini. -/
theorem pv_term (p q : Mom d) {ξ η : T → Mom d} (hξ : Measurable ξ) (hη : Measurable η)
    {h : T → ℂ} (hh : Integrable h ν) {s : ℝ} (hs : 0 < s) :
    Integrable (fun z : Mom d × Mom d =>
      pvKer s z.1 z.2 * ∫ τ, h τ * cellFn p q (ξ τ) (η τ) z.1 z.2 ∂ν) ∧
    Integrable (fun τ => h τ * pvTrunc s (cellFn p q (ξ τ) (η τ))) ν ∧
    pvTrunc s (fun x y => ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x y ∂ν) =
      ∫ τ, h τ * pvTrunc s (cellFn p q (ξ τ) (η τ)) ∂ν := by
  set G : (Mom d × Mom d) × T → ℂ := fun z =>
    pvKer s z.1.1 z.1.2 * (h z.2 * cellFn p q (ξ z.2) (η z.2) z.1.1 z.1.2) with hG_def
  have hG : Integrable G ((volume : Measure (Mom d × Mom d)).prod ν) := by
    refine Integrable.mono' (((integrable_cellAmp p q).norm.const_mul (2 * s)).mul_prod hh.norm)
      ?_ (Eventually.of_forall fun z => ?_)
    · have hK1 := (measurable_pvKer (d := d) s).comp
        (measurable_fst : Measurable (Prod.fst : (Mom d × Mom d) × T → Mom d × Mom d))
      have hc := measurable_cellFn_param p q hξ hη
      have h2 := (hK1.aestronglyMeasurable (μ := (volume : Measure (Mom d × Mom d)).prod ν)).mul
        ((hh.1.comp_snd (μ := (volume : Measure (Mom d × Mom d)))).mul hc.aestronglyMeasurable)
      exact h2
    · simp only [G, norm_mul, norm_cellFn]
      have := norm_pvKer_le hs z.1.1 z.1.2
      calc ‖pvKer s z.1.1 z.1.2‖ * (‖h z.2‖ * ‖cellAmp p q z.1.1 z.1.2‖)
          ≤ 2 * s * (‖h z.2‖ * ‖cellAmp p q z.1.1 z.1.2‖) := by gcongr
        _ = _ := by ring
  have hsl : ∀ τ, Integrable (fun z : Mom d × Mom d =>
      pvKer s z.1 z.2 * cellFn p q (ξ τ) (η τ) z.1 z.2) := fun τ => by
    refine Integrable.mono' ((integrable_cellAmp p q).norm.const_mul (2 * s)) ?_
      (Eventually.of_forall fun z => ?_)
    · have h1 : Continuous (fun z : Mom d × Mom d => ((ξ τ, η τ), z)) :=
        continuous_const.prodMk continuous_id
      have h2 := (continuous_cellFn_all p q).comp h1
      have h3 := ((measurable_pvKer s).mul h2.measurable).aestronglyMeasurable
        (μ := (volume : Measure (Mom d × Mom d)))
      exact h3
    · rw [norm_mul, norm_cellFn]
      exact mul_le_mul_of_nonneg_right (norm_pvKer_le hs _ _) (norm_nonneg _)
  have hKF : ∀ z : Mom d × Mom d, pvKer s z.1 z.2 * ∫ τ, h τ * cellFn p q (ξ τ) (η τ) z.1 z.2 ∂ν =
      ∫ τ, G (z, τ) ∂ν := fun z => by
    rw [← integral_const_mul]
  have hτ : ∀ τ, ∫ z : Mom d × Mom d, G (z, τ) = h τ * pvTrunc s (cellFn p q (ξ τ) (η τ)) :=
    fun τ => by
      rw [pvTrunc_eq_integral_prod (hsl τ), ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [G]; ring
  have h1 : Integrable (fun z : Mom d × Mom d =>
      pvKer s z.1 z.2 * ∫ τ, h τ * cellFn p q (ξ τ) (η τ) z.1 z.2 ∂ν) :=
    hG.integral_prod_left.congr (Eventually.of_forall fun z => (hKF z).symm)
  refine ⟨h1, hG.integral_prod_right.congr (Eventually.of_forall fun τ => hτ τ), ?_⟩
  rw [pvTrunc_eq_integral_prod h1]
  calc ∫ z : Mom d × Mom d, pvKer s z.1 z.2 * ∫ τ, h τ * cellFn p q (ξ τ) (η τ) z.1 z.2 ∂ν
      = ∫ z : Mom d × Mom d, ∫ τ, G (z, τ) ∂ν :=
        integral_congr_ae (Eventually.of_forall hKF)
    _ = ∫ τ, (∫ z : Mom d × Mom d, G (z, τ)) ∂ν :=
        integral_integral_swap (f := fun z τ => G (z, τ)) hG
    _ = _ := integral_congr_ae (Eventually.of_forall hτ)

/-- One superposition: the truncations converge to `∫ h p.v.(P(τ))`. -/
theorem tendsto_pv_term (hd : 3 ≤ d) (p q : Mom d) {ξ η : T → Mom d} (hξ : Measurable ξ)
    (hη : Measurable η) {h : T → ℂ} (hh : Integrable h ν) :
    Tendsto (fun s : ℝ => pvTrunc s (fun x y => ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x y ∂ν)) atTop
      (𝓝 (∫ τ, h τ * pvOp (cellFn p q (ξ τ) (η τ)) ∂ν)) := by
  obtain ⟨M, -, hM⟩ := exists_pvCell hd
  have hlim : Tendsto (fun s : ℝ => ∫ τ, h τ * pvTrunc s (cellFn p q (ξ τ) (η τ)) ∂ν) atTop
      (𝓝 (∫ τ, h τ * pvOp (cellFn p q (ξ τ) (η τ)) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun τ => M * ‖h τ‖) ?_ ?_
      (hh.norm.const_mul M) ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      exact (pv_term p q hξ hη hh hs).2.1.aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
      refine Eventually.of_forall fun τ => ?_
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hM _ _ _ _).1 s hs) (norm_nonneg _)
    · exact Eventually.of_forall fun τ => ((hM _ _ _ _).2.1).const_mul (h τ)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (pv_term p q hξ hη hh hs).2.2.symm

/-- **The principal value of a finite sum of superpositions of cells.** -/
theorem pvOp_sum_integral (hd : 3 ≤ d) {α : Type*} (Q : Finset α) (p q : α → Mom d)
    {ξ η : α → T → Mom d} (hξ : ∀ a, Measurable (ξ a)) (hη : ∀ a, Measurable (η a))
    {h : α → T → ℂ} (hh : ∀ a, Integrable (h a) ν) :
    pvOp (fun x y => ∑ a ∈ Q, ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν) =
      ∑ a ∈ Q, ∫ τ, h a τ * pvOp (cellFn (p a) (q a) (ξ a τ) (η a τ)) ∂ν := by
  have hsum : ∀ s : ℝ, 0 < s →
      pvTrunc s (fun x y => ∑ a ∈ Q, ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν) =
        ∑ a ∈ Q, pvTrunc s (fun x y => ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν) := by
    intro s hs
    have hi := fun a => (pv_term (p a) (q a) (hξ a) (hη a) (hh a) hs).1
    have hI : Integrable (fun z : Mom d × Mom d => pvKer s z.1 z.2 *
        ∑ a ∈ Q, ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) z.1 z.2 ∂ν) :=
      (integrable_finsetSum Q fun a _ => hi a).congr (Eventually.of_forall fun z => by
        simp only [mul_sum])
    rw [pvTrunc_eq_integral_prod hI]
    simp only [mul_sum]
    rw [integral_finsetSum _ fun a _ => hi a]
    exact sum_congr rfl fun a _ => (pvTrunc_eq_integral_prod
      (F := fun x y => ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν) (hi a)).symm
  have ht : Tendsto (fun s : ℝ => pvTrunc s
      (fun x y => ∑ a ∈ Q, ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν)) atTop
      (𝓝 (∑ a ∈ Q, ∫ τ, h a τ * pvOp (cellFn (p a) (q a) (ξ a τ) (η a τ)) ∂ν)) := by
    refine (tendsto_finsetSum Q fun a _ => tendsto_pv_term hd (p a) (q a) (hξ a) (hη a)
      (hh a)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (hsum s hs).symm
  exact ht.limUnder_eq

/-! ### The delta functional -/

/-- One superposition on one hyperplane: Fubini. -/
theorem delta_slice (p q : Mom d) {ξ η : T → Mom d} (hξ : Measurable ξ) (hη : Measurable η)
    {h : T → ℂ} (hh : Integrable h ν) {x : Mom d} (hx : x ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ x)ᗮ => ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν) ∧
    ∫ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν =
      ∫ τ, h τ * (∫ w : ↥(ℝ ∙ x)ᗮ, cellFn p q (ξ τ) (η τ) x w) ∂ν := by
  have hB := ntBounds_cellAmp (d := d) 1 (c := 1) (by simp) p q
  have hsl : Integrable (fun w : ↥(ℝ ∙ x)ᗮ => cellFn p q 0 0 x w) := by
    have h0 := NTSP.integrable_slice_amp le_rfl hB two_pos p q 0 0 hx 0
    rw [amp_cellAmp_eq] at h0
    simpa using h0
  set G : ↥(ℝ ∙ x)ᗮ × T → ℂ := fun z => h z.2 * cellFn p q (ξ z.2) (η z.2) x z.1 with hG_def
  have hG : Integrable G ((volume : Measure ↥(ℝ ∙ x)ᗮ).prod ν) := by
    refine Integrable.mono' (hsl.norm.mul_prod hh.norm) ?_ (Eventually.of_forall fun z => ?_)
    · have h1 : Measurable (fun z : ↥(ℝ ∙ x)ᗮ × T => ((ξ z.2, η z.2), (x, (z.1 : Mom d)))) :=
        ((hξ.comp measurable_snd).prodMk (hη.comp measurable_snd)).prodMk
          (measurable_const.prodMk (measurable_subtype_coe.comp measurable_fst))
      have h2 := (continuous_cellFn_all p q).measurable.comp h1
      have h3 := (hh.1.comp_snd (μ := (volume : Measure ↥(ℝ ∙ x)ᗮ))).mul h2.aestronglyMeasurable
      exact h3
    · simp only [G, norm_mul, norm_cellFn]
      rw [mul_comm]
  have h1 : ∀ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν = ∫ τ, G (w, τ) ∂ν :=
    fun w => rfl
  refine ⟨hG.integral_prod_left.congr (Eventually.of_forall fun w => (h1 w).symm), ?_⟩
  calc ∫ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν
      = ∫ τ, (∫ w : ↥(ℝ ∙ x)ᗮ, G (w, τ)) ∂ν := integral_integral_swap (f := fun w τ => G (w, τ)) hG
    _ = _ := integral_congr_ae (Eventually.of_forall fun τ => by
        simp only [G]; rw [integral_const_mul])

/-- The slice limit (DH23 Lemma 6.7's slice analysis, as in `NTSP.aestronglyMeasurable_delta`):
`(m+1) ∫ 1_{[0,1]}((m+1)⟨x,y⟩) P(x,y) dy → |x|⁻¹ ∫_{x^⊥} P(x,w) dw` for `x ≠ 0`. -/
theorem tendsto_slice (p q ξ η : Mom d) {x : Mom d} (hx : x ≠ 0) :
    Tendsto (fun m : ℕ => ((m + 1 : ℝ) : ℂ) *
      ∫ y, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) ((m + 1 : ℝ) * inner ℝ x y) *
        cellFn p q ξ η x y) atTop
      (𝓝 (((‖x‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ x)ᗮ, cellFn p q ξ η x w)) := by
  have hB := ntBounds_cellAmp (d := d) 1 (c := 1) (by simp) p q
  rw [← amp_cellAmp_eq p q ξ η]
  set D := cellConst d 1
  have hD := hB.nonneg
  set lam : ℝ := 2
  have hlam : (1 : ℝ) ≤ lam := by norm_num
  have h0 : (0 : ℝ) < lam := by norm_num
  set ψ₀ : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hψ₀m : Measurable ψ₀ := measurable_const.indicator measurableSet_Icc
  have hψ₀ : Integrable ψ₀ := (integrableOn_const (C := (1 : ℂ)) (by simp)).integrable_indicator
    measurableSet_Icc
  have hint0 : ∫ u, ψ₀ u = 1 := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc]
    simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set Lb := 2 * ‖NTSP.chiScaled lam (x - p)‖ * NTSP.ampLip d D η * NTSP.sliceConst d lam
  have hLb : 0 ≤ Lb := by
    have := NTSP.ampLip_nonneg d hD η; have := NTSP.sliceConst_nonneg d h0.le
    simp only [Lb]; positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (g := fun n : ℕ => ‖x‖⁻¹ * (Lb / (((n : ℝ) + 1) * ‖x‖))) ?_
  · have hμ : (0 : ℝ) < n + 1 := by positivity
    have h := NTSP.norm_psi_amp_sub_le le_rfl hB hlam hμ hψ₀m hψ₀ p q ξ η hx
    rw [hint0, one_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hb : ∀ u, ‖ψ₀ u‖ * min (2 * (D * ‖NTSP.chiScaled lam (x - p)‖ * NTSP.sliceConst d lam))
        (Lb * (|u| / (((n : ℝ) + 1) * ‖x‖))) ≤
        (Icc (0 : ℝ) 1).indicator (fun _ => Lb / (((n : ℝ) + 1) * ‖x‖)) u := fun u => by
      by_cases hu : u ∈ Icc (0 : ℝ) 1
      · simp only [ψ₀, Set.indicator_of_mem hu, norm_one, one_mul]
        refine (min_le_right _ _).trans ?_
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
        have : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
        nlinarith
      · simp only [ψ₀, Set.indicator_of_notMem hu, norm_zero, zero_mul, le_refl]
    calc ∫ u, ‖ψ₀ u‖ * min (2 * (D * ‖NTSP.chiScaled lam (x - p)‖ * NTSP.sliceConst d lam))
          (Lb * (|u| / (((n : ℝ) + 1) * ‖x‖)))
        ≤ ∫ u, (Icc (0 : ℝ) 1).indicator (fun _ => Lb / (((n : ℝ) + 1) * ‖x‖)) u :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => by
            have : 0 ≤ min (2 * (D * ‖NTSP.chiScaled lam (x - p)‖ * NTSP.sliceConst d lam))
                (Lb * (|u| / (((n : ℝ) + 1) * ‖x‖))) := le_min (by
                  have := NTSP.sliceConst_nonneg d h0.le; positivity) (by positivity)
            positivity)
            ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
            (Eventually.of_forall hb)
      _ = Lb / (((n : ℝ) + 1) * ‖x‖) := by
          rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc]
          simp
  · have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 := (h1.const_mul (‖x‖⁻¹ * (Lb / ‖x‖)))
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    field_simp

omit [SFinite ν] in
/-- Joint measurability of the sliced cell function in `(x, τ)`. -/
theorem aestronglyMeasurable_slice_param (hd : 1 ≤ d) (p q : Mom d) {ξ η : T → Mom d}
    (hξ : Measurable ξ) (hη : Measurable η) :
    AEStronglyMeasurable (fun z : Mom d × T =>
      ((‖z.1‖⁻¹ : ℝ) : ℂ) * ∫ w : ↥(ℝ ∙ z.1)ᗮ, cellFn p q (ξ z.2) (η z.2) z.1 w)
      ((volume : Measure (Mom d)).prod ν) := by
  set ψ₀ : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hψ₀m : Measurable ψ₀ := measurable_const.indicator measurableSet_Icc
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun m : ℕ => fun z : Mom d × T => ((m + 1 : ℝ) : ℂ) *
      ∫ y, ψ₀ ((m + 1 : ℝ) * inner ℝ z.1 y) * cellFn p q (ξ z.2) (η z.2) z.1 y)
    (fun m => ?_) ?_
  · refine (stronglyMeasurable_const.mul ?_).aestronglyMeasurable
    refine StronglyMeasurable.integral_prod_right' (f := fun w : (Mom d × T) × Mom d =>
      ψ₀ ((m + 1 : ℝ) * inner ℝ w.1.1 w.2) * cellFn p q (ξ w.1.2) (η w.1.2) w.1.1 w.2) ?_
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable (fun w : (Mom d × T) × Mom d =>
        ((ξ w.1.2, η w.1.2), (w.1.1, w.2))) :=
      ((hξ.comp (measurable_snd.comp measurable_fst)).prodMk
        (hη.comp (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 := (continuous_cellFn_all p q).measurable.comp h1
    have h3 : Measurable (fun w : (Mom d × T) × Mom d => ψ₀ ((m + 1 : ℝ) * inner ℝ w.1.1 w.2)) :=
      hψ₀m.comp (measurable_const.mul ((measurable_fst.comp measurable_fst).inner measurable_snd))
    have h4 := h3.mul h2
    exact h4
  · have hae : ∀ᵐ z ∂((volume : Measure (Mom d)).prod ν), z.1 ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae (NTSP.ae_ne_zero_mom (by omega))
    filter_upwards [hae] with z hz
    exact tendsto_slice p q (ξ z.2) (η z.2) hz

/-- One superposition: the delta functional, with the integrability needed for sums. -/
theorem delta_term (hd : 3 ≤ d) (p q : Mom d) {ξ η : T → Mom d} (hξ : Measurable ξ)
    (hη : Measurable η) {h : T → ℂ} (hh : Integrable h ν) :
    (∀ x : Mom d, x ≠ 0 → Integrable (fun w : ↥(ℝ ∙ x)ᗮ =>
      ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν)) ∧
    Integrable (fun x : Mom d => ((‖x‖⁻¹ : ℝ) : ℂ) *
      ∫ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν) ∧
    NTSP.deltaInner (fun x y => ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x y ∂ν) =
      ∫ τ, h τ * NTSP.deltaInner (cellFn p q (ξ τ) (η τ)) ∂ν := by
  have hd0 : 0 < d := by omega
  have hB := ntBounds_cellAmp (d := d) 1 (c := 1) (by simp) p q
  set Cs := cellConst d 1 * NTSP.sliceConst d 2
  have hCs : 0 ≤ Cs := mul_nonneg hB.nonneg (NTSP.sliceConst_nonneg d (by norm_num))
  set r := 2 * Real.sqrt d
  have hr : 0 < r := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd0)
    positivity
  set S : Mom d × T → ℂ := fun z => ∫ w : ↥(ℝ ∙ z.1)ᗮ, cellFn p q (ξ z.2) (η z.2) z.1 w
  set Φ : Mom d × T → ℂ := fun z => ((‖z.1‖⁻¹ : ℝ) : ℂ) * (h z.2 * S z) with hΦ_def
  have hS : ∀ z : Mom d × T, z.1 ≠ 0 →
      ‖S z‖ ≤ Cs * (Metric.closedBall p r).indicator (fun _ => (1 : ℝ)) z.1 := fun z hz => by
    have h1 := NTSP.norm_sliceAmp_le hB two_pos p q (ξ z.2) (η z.2) hz 0
    rw [NTSP.sliceAmp] at h1
    simp only [zero_smul, zero_add] at h1
    rw [amp_cellAmp_eq] at h1
    refine h1.trans ?_
    have h2 := NTSP.norm_chiScaled_le_indicator (lam := 2) two_pos p z.1
    calc cellConst d 1 * ‖NTSP.chiScaled 2 (z.1 - p)‖ * NTSP.sliceConst d 2
        ≤ cellConst d 1 * (Metric.closedBall p (2 * Real.sqrt d)).indicator (fun _ => (1 : ℝ)) z.1 *
            NTSP.sliceConst d 2 := by
          have := NTSP.sliceConst_nonneg d (lam := 2) (by norm_num)
          have := hB.nonneg
          gcongr
      _ = _ := by simp only [Cs, r]; ring
  have hΦ : Integrable Φ ((volume : Measure (Mom d)).prod ν) := by
    have hsing := (NTSP.integrable_indicator_norm_rpow (d := d) (p := 1) zero_le_one
      (by have : (3 : ℝ) ≤ d := by exact_mod_cast hd
          linarith) hr p).const_mul Cs
    refine Integrable.mono' (hsing.mul_prod hh.norm) ?_ (Eventually.of_forall fun z => ?_)
    · have h1 := aestronglyMeasurable_slice_param (ν := ν) (by omega) p q hξ hη
      exact (hh.1.comp_snd.mul h1).congr (Eventually.of_forall fun z => by
        simp only [Φ, S, Pi.mul_apply]; ring)
    · simp only [Φ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hz : z.1 = 0
      · rw [hz, norm_zero, inv_zero, abs_zero, zero_mul]
        have : 0 ≤ (Metric.closedBall p r).indicator (fun x : Mom d => ‖x‖ ^ (-(1 : ℝ))) 0 :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        positivity
      · have hxn : 0 < ‖z.1‖ := norm_pos_iff.2 hz
        rw [abs_of_pos (inv_pos.2 hxn)]
        have hSz := hS z hz
        by_cases hzb : z.1 ∈ Metric.closedBall p r
        · rw [Set.indicator_of_mem hzb] at hSz ⊢
          rw [Real.rpow_neg_one]
          calc ‖z.1‖⁻¹ * (‖h z.2‖ * ‖S z‖) ≤ ‖z.1‖⁻¹ * (‖h z.2‖ * (Cs * 1)) := by gcongr
            _ = _ := by ring
        · rw [Set.indicator_of_notMem hzb] at hSz ⊢
          have : ‖S z‖ = 0 := le_antisymm (by simpa using hSz) (norm_nonneg _)
          rw [this]; simp
  -- the slices
  have hslice : ∀ x : Mom d, x ≠ 0 → ∫ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν =
      ∫ τ, h τ * S (x, τ) ∂ν := fun x hx => (delta_slice p q hξ hη hh hx).2
  have hae : ∀ᵐ x : Mom d, ((‖x‖⁻¹ : ℝ) : ℂ) *
      ∫ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν = ∫ τ, Φ (x, τ) ∂ν := by
    filter_upwards [NTSP.ae_ne_zero_mom hd0] with x hx
    rw [hslice x hx, ← integral_const_mul]
  refine ⟨fun x hx => (delta_slice p q hξ hη hh hx).1,
    hΦ.integral_prod_left.congr (hae.mono fun x hx => hx.symm), ?_⟩
  rw [NTSP.deltaInner]
  calc ∫ x : Mom d, ((‖x‖⁻¹ : ℝ) : ℂ) *
        ∫ w : ↥(ℝ ∙ x)ᗮ, ∫ τ, h τ * cellFn p q (ξ τ) (η τ) x w ∂ν
      = ∫ x : Mom d, ∫ τ, Φ (x, τ) ∂ν := integral_congr_ae hae
    _ = ∫ τ, (∫ x : Mom d, Φ (x, τ)) ∂ν := integral_integral_swap (f := fun x τ => Φ (x, τ)) hΦ
    _ = _ := integral_congr_ae (Eventually.of_forall fun τ => by
        simp only [Φ, S, NTSP.deltaInner]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        ring)

theorem deltaInner_finset_sum (hd0 : 0 < d) {α : Type*} (Q : Finset α)
    (F : α → Mom d → Mom d → ℂ)
    (h1 : ∀ a ∈ Q, ∀ x : Mom d, x ≠ 0 → Integrable (fun w : ↥(ℝ ∙ x)ᗮ => F a x w))
    (h3 : ∀ a ∈ Q, Integrable (fun x : Mom d => ((‖x‖⁻¹ : ℝ) : ℂ) *
      ∫ w : ↥(ℝ ∙ x)ᗮ, F a x w)) :
    NTSP.deltaInner (fun x y => ∑ a ∈ Q, F a x y) = ∑ a ∈ Q, NTSP.deltaInner (F a) := by
  simp only [NTSP.deltaInner]
  rw [← integral_finsetSum _ h3]
  refine integral_congr_ae ?_
  filter_upwards [NTSP.ae_ne_zero_mom hd0] with x hx
  rw [integral_finsetSum _ fun a ha => h1 a ha x hx, mul_sum]

/-- **The delta functional of a finite sum of superpositions of cells.** -/
theorem deltaInner_sum_integral (hd : 3 ≤ d) {α : Type*} (Q : Finset α) (p q : α → Mom d)
    {ξ η : α → T → Mom d} (hξ : ∀ a, Measurable (ξ a)) (hη : ∀ a, Measurable (η a))
    {h : α → T → ℂ} (hh : ∀ a, Integrable (h a) ν) :
    NTSP.deltaInner (fun x y => ∑ a ∈ Q, ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν) =
      ∑ a ∈ Q, ∫ τ, h a τ * NTSP.deltaInner (cellFn (p a) (q a) (ξ a τ) (η a τ)) ∂ν := by
  rw [deltaInner_finset_sum (by omega) Q
    (fun a x y => ∫ τ, h a τ * cellFn (p a) (q a) (ξ a τ) (η a τ) x y ∂ν)
    (fun a _ => (delta_term hd (p a) (q a) (hξ a) (hη a) (hh a)).1)
    (fun a _ => (delta_term hd (p a) (q a) (hξ a) (hη a) (hh a)).2.1)]
  exact sum_congr rfl fun a _ => (delta_term hd (p a) (q a) (hξ a) (hη a) (hh a)).2.2

end WaveTurbulence.ApproxNT
