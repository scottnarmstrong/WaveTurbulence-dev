/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppExchange
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Group.Integral

/-! # Countable absolutely summable Fourier-cell mixtures for principal values -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Filter Topology

variable {d : ℕ} {U : Type*} [MeasurableSpace U] (ν : Measure U)

/-- An actual source cell with an arbitrary integrable spectral weight. -/
def cellMixture (p q : Mom d) (ξ η : U → Mom d) (h : U → ℂ) (x y : Mom d) : ℂ :=
  ∫ u, h u*cellFn p q (ξ u) (η u) x y ∂ν

/-- The pointwise scalar estimate retains the fixed cell amplitude. -/
theorem norm_cellMixture_le (p q : Mom d) (ξ η : U → Mom d) (h : U → ℂ) (x y : Mom d) :
    ‖cellMixture ν p q ξ η h x y‖ ≤ ‖cellAmp p q x y‖*(∫ u, ‖h u‖ ∂ν) := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [norm_mul,norm_cellFn]
  rw [integral_mul_const]
  ring

/-- Every translated cell has exactly the same physical L1 mass. -/
theorem integral_norm_cellAmp_eq (p q : Mom d) :
    (∫ z : Mom d × Mom d, ‖cellAmp p q z.1 z.2‖) =
      ∫ z : Mom d × Mom d, ‖cellAmp 0 0 z.1 z.2‖ := by
  let : (volume : Measure (Mom d × Mom d)).IsAddRightInvariant := by
    change (volume.prod volume : Measure (Mom d × Mom d)).IsAddRightInvariant
    infer_instance
  simpa [cellAmp] using integral_sub_right_eq_self
    (fun z : Mom d × Mom d => ‖cellAmp 0 0 z.1 z.2‖) (p,q)

variable [SFinite ν]

/-- Joint physical measurability of the original cell superposition. -/
theorem stronglyMeasurable_cellMixture (p q : Mom d) {ξ η : U → Mom d}
    (hξ : Measurable ξ) (hη : Measurable η) {h : U → ℂ} (hh : StronglyMeasurable h) :
    StronglyMeasurable (fun z : Mom d × Mom d => cellMixture ν p q ξ η h z.1 z.2) := by
  have hG : StronglyMeasurable (fun z : (Mom d × Mom d) × U =>
      h z.2*cellFn p q (ξ z.2) (η z.2) z.1.1 z.1.2) :=
    (hh.comp_measurable measurable_snd).mul (measurable_cellFn_param p q hξ hη).stronglyMeasurable
  exact hG.integral_prod_right'

/-- Fixed-truncation physical L1 cost, uniformly in both cell centers. -/
theorem integral_norm_pv_cellMixture_le (p q : Mom d) {ξ η : U → Mom d}
    (hξ : Measurable ξ) (hη : Measurable η) {h : U → ℂ} (hh : Integrable h ν)
    {s : ℝ} (hs : 0 < s) :
    (∫ z : Mom d × Mom d, ‖pvKer s z.1 z.2*cellMixture ν p q ξ η h z.1 z.2‖) ≤
      (2*s)*(∫ z : Mom d × Mom d, ‖cellAmp 0 0 z.1 z.2‖)*(∫ u, ‖h u‖ ∂ν) := by
  have hi := (pv_term p q hξ hη hh hs).1.norm
  have hbound := ((integrable_cellAmp p q).norm.const_mul (2*s)).mul_const (∫ u, ‖h u‖ ∂ν)
  calc
    _ ≤ ∫ z : Mom d × Mom d, (2*s)*‖cellAmp p q z.1 z.2‖*(∫ u, ‖h u‖ ∂ν) := by
      apply integral_mono hi hbound
      intro z
      change ‖pvKer s z.1 z.2*cellMixture ν p q ξ η h z.1 z.2‖ ≤
        (2*s)*‖cellAmp p q z.1 z.2‖*(∫ u, ‖h u‖ ∂ν)
      rw [norm_mul]
      calc
        _ ≤ (2*s)*(‖cellAmp p q z.1 z.2‖*(∫ u, ‖h u‖ ∂ν)) :=
          mul_le_mul (norm_pvKer_le hs _ _) (norm_cellMixture_le ν p q ξ η h _ _)
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (2*s)*(∫ z : Mom d × Mom d, ‖cellAmp p q z.1 z.2‖)*(∫ u, ‖h u‖ ∂ν) := by
      rw [integral_mul_const,integral_const_mul]
    _ = _ := by rw [integral_norm_cellAmp_eq]

/-- A countable family with summable physical L1 norms has an integrable
actual complex sum. This is used for the unbounded union of source cells. -/
theorem integrable_countable_cell_sum {I X : Type*} [Countable I] [MeasurableSpace X]
    (μ : Measure X) (f : I → X → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hi : ∀ i, Integrable (f i) μ) (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨(AEMeasurable.tsum (fun i => (hm i).aemeasurable)).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    _ ≤ ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ := lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ := lintegral_tsum (fun i => (hm i).enorm)
    _ < ⊤ := by
      simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
      exact hs.tsum_ofReal_lt_top

/-- Countable source cells commute with every fixed positive PV
truncation. The only global premise is summable absolute coefficient mass. -/
theorem pvTrunc_tsum_cellMixture {I : Type*} [Countable I]
    (p q : I → Mom d) (ξ η : I → U → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν))
    {s : ℝ} (hs : 0 < s) :
    pvTrunc s (fun x y => ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y) =
      ∑' i, ∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν := by
  let F := fun (i : I) (z : Mom d × Mom d) =>
    pvKer s z.1 z.2*cellMixture ν (p i) (q i) (ξ i) (η i) (h i) z.1 z.2
  have hfm (i : I) : StronglyMeasurable (F i) :=
    (measurable_pvKer s).stronglyMeasurable.mul
      (stronglyMeasurable_cellMixture ν (p i) (q i) (hξ i) (hη i) (hsm i))
  have hfi (i : I) : Integrable (F i) := (pv_term (p i) (q i) (hξ i) (hη i) (hi i) hs).1
  have hfs : Summable (fun i => ∫ z : Mom d × Mom d, ‖F i z‖) := by
    apply (hsum.mul_left ((2*s)*(∫ z : Mom d × Mom d, ‖cellAmp 0 0 z.1 z.2‖))).of_norm_bounded
    intro i
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_norm_pv_cellMixture_le ν (p i) (q i) (hξ i) (hη i) (hi i) hs
  have hI := integrable_countable_cell_sum volume F (fun i => (hfm i).aestronglyMeasurable) hfi hfs
  have he (z : Mom d × Mom d) :
      pvKer s z.1 z.2*(∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) z.1 z.2) = ∑' i, F i z :=
    (tsum_mul_left).symm
  have hA : Integrable (fun z : Mom d × Mom d =>
      pvKer s z.1 z.2*(∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) z.1 z.2)) :=
    hI.congr (ae_of_all _ (fun z => (he z).symm))
  rw [pvTrunc_eq_integral_prod hA]
  calc
    _ = ∫ z : Mom d × Mom d, ∑' i, F i z := integral_congr_ae (ae_of_all _ he)
    _ = ∑' i, ∫ z : Mom d × Mom d, F i z :=
      (integral_tsum_of_summable_integral_norm hfi hfs).symm
    _ = _ := by
      apply tsum_congr
      intro i
      exact (pvTrunc_eq_integral_prod (hfi i)).symm.trans
        (pv_term (p i) (q i) (hξ i) (hη i) (hi i) hs).2.2

/-- Countably many translated source cells commute with the actual
principal value. Absolute coefficient mass replaces the finite-support
hypothesis; no support radius or derivative order grows with the family. -/
theorem pvOp_tsum_integral_cells {I : Type*} [Countable I] (hd : 3 ≤ d)
    (p q : I → Mom d) (ξ η : I → U → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hsm : ∀ i, StronglyMeasurable (h i))
    (hi : ∀ i, Integrable (h i) ν) (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) :
    pvOp (fun x y => ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y) =
      ∑' i, ∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν := by
  obtain ⟨M,hM,hcell⟩ := exists_pvCell hd
  have hb (i : I) {s : ℝ} (hs : 1 < s) :
      ‖∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν‖ ≤
        M*(∫ u, ‖h i u‖ ∂ν) := by
    apply (norm_integral_le_integral_norm _).trans
    have hiA := (pv_term (p i) (q i) (hξ i) (hη i) (hi i) (zero_lt_one.trans hs)).2.1.norm
    calc
      _ ≤ ∫ u, M*‖h i u‖ ∂ν := by
        apply integral_mono hiA ((hi i).norm.const_mul M)
        intro u
        change ‖h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u))‖ ≤ M*‖h i u‖
        rw [norm_mul,mul_comm M]
        exact mul_le_mul_of_nonneg_left ((hcell _ _ _ _).1 s hs) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have ht (i : I) : Tendsto (fun s : ℝ =>
      ∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν) atTop
      (𝓝 (∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
    refine (tendsto_pv_term hd (p i) (q i) (hξ i) (hη i) (hi i)).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (pv_term (p i) (q i) (hξ i) (hη i) (hi i) hs).2.2
  have hlim : Tendsto (fun s : ℝ => ∑' i,
      ∫ u, h i u*pvTrunc s (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν) atTop
      (𝓝 (∑' i, ∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
    apply tendsto_tsum_of_dominated_convergence (hsum.mul_left M) ht
    filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
    exact fun i => hb i hs
  have hfull : Tendsto (fun s : ℝ => pvTrunc s
      (fun x y => ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y)) atTop
      (𝓝 (∑' i, ∫ u, h i u*pvOp (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (pvTrunc_tsum_cellMixture ν p q ξ η hξ hη h hsm hi hsum hs).symm
  exact hfull.limUnder_eq

end WaveTurbulence.RegAsymp
