/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CountablePVCellMixture

/-! # Absolute hyperplane masses and countable source-cell delta exchange -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Filter

variable {d : ℕ}

/-- The absolute hyperplane mass of the original nonnegative cell. -/
def deltaCellMass (p q x : Mom d) : ℝ :=
  ‖x‖⁻¹ * ∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellAmp p q x w‖

theorem deltaCellMass_nonneg (p q x : Mom d) : 0 ≤ deltaCellMass p q x :=
  mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (integral_nonneg (fun _ => norm_nonneg _))

/-- Cell amplitudes have no sign cancellation in their physical mass. -/
theorem cellAmp_ofReal_norm (p q x y : Mom d) : (‖cellAmp p q x y‖ : ℂ) = cellAmp p q x y := by
  have hnorm (z : Mom d) : ‖thetaC z‖ = thetaMom d z := by
    rw [thetaC,Complex.norm_real,Real.norm_of_nonneg (thetaMom_nonneg _)]
  simp only [cellAmp,norm_mul]
  rw [hnorm,hnorm]
  exact Complex.ofReal_mul _ _

theorem cellFn_zero_eq_cellAmp (p q x y : Mom d) : cellFn p q 0 0 x y = cellAmp p q x y := by
  simp [cellFn,pairAmp]

/-- The absolute slice mass is the positive complex zero-frequency slice. -/
theorem deltaCellMass_ofReal (p q x : Mom d) : (deltaCellMass p q x : ℂ) =
    ((‖x‖⁻¹ : ℝ):ℂ)*(∫ w : ↥(ℝ ∙ x)ᗮ, cellFn p q 0 0 x w) := by
  rw [deltaCellMass,Complex.ofReal_mul,← integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun w => (cellAmp_ofReal_norm p q x w).trans (cellFn_zero_eq_cellAmp p q x w).symm)

theorem deltaCellMass_eq_norm (p q x : Mom d) : deltaCellMass p q x =
    ‖((‖x‖⁻¹ : ℝ):ℂ)*(∫ w : ↥(ℝ ∙ x)ᗮ, cellFn p q 0 0 x w)‖ := by
  rw [← deltaCellMass_ofReal,Complex.norm_real,Real.norm_of_nonneg (deltaCellMass_nonneg _ _ _)]

/-- Integrability of the literal absolute slice, from the landed
single-cell hyperplane exchange with a one-point coefficient measure. -/
theorem integrable_deltaCellMass (hd : 3 ≤ d) (p q : Mom d) : Integrable (deltaCellMass p q) := by
  have hunit : Integrable (fun _ : Unit => (1:ℂ)) (Measure.dirac ()) := integrable_const _
  have hbase := (delta_term (ν := Measure.dirac ()) hd p q
    (ξ := fun _ : Unit => (0:Mom d)) (η := fun _ : Unit => (0:Mom d))
    measurable_const measurable_const hunit).2.1
  simp only [integral_dirac,one_mul] at hbase
  exact hbase.norm.congr (ae_of_all _ (fun x => (deltaCellMass_eq_norm p q x).symm))

/-- The whole absolute mass equals the norm of the positive cell delta. -/
theorem integral_deltaCellMass_eq (p q : Mom d) :
    (∫ x, deltaCellMass p q x) = ‖NTSP.deltaInner (cellFn p q 0 0)‖ := by
  rw [NTSP.deltaInner]
  simp_rw [← deltaCellMass_ofReal]
  rw [integral_complex_ofReal,Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun x => deltaCellMass_nonneg p q x))]

/-- The absolute hyperplane mass is bounded uniformly in both cell centers. -/
theorem integral_deltaCellMass_le (hd : 3 ≤ d) (p q : Mom d) :
    (∫ x, deltaCellMass p q x) ≤ cellCa d := by
  rw [integral_deltaCellMass_eq]
  exact norm_deltaInner_cellFn_le hd p q 0 0

/-- The physical cell has an integrable restriction to every nonzero
hyperplane, without assumptions on where its center lies. -/
theorem integrable_cellAmp_slice (p q : Mom d) {x : Mom d} (hx : x ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ x)ᗮ => cellAmp p q x w) := by
  have hunit : Integrable (fun _ : Unit => (1:ℂ)) (Measure.dirac ()) := integrable_const _
  have hh := (delta_slice (ν := Measure.dirac ()) p q
    (ξ := fun _ : Unit => (0:Mom d)) (η := fun _ : Unit => (0:Mom d))
    measurable_const measurable_const hunit hx).1
  simpa only [integral_dirac,one_mul,cellFn_zero_eq_cellAmp] using hh

/-- Positivity identifies the absolute slice with its zero-frequency value. -/
theorem integral_norm_cellAmp_slice_eq (p q x : Mom d) :
    (∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellAmp p q x w‖) = ‖∫ w : ↥(ℝ ∙ x)ᗮ, cellFn p q 0 0 x w‖ := by
  have he : (((∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellAmp p q x w‖):ℝ):ℂ) =
      ∫ w : ↥(ℝ ∙ x)ᗮ, cellFn p q 0 0 x w := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact ae_of_all _ (fun w => (cellAmp_ofReal_norm p q x w).trans (cellFn_zero_eq_cellAmp p q x w).symm)
  rw [← he,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]

/-- A uniform unweighted slice mass supplies countable Fubini on each
individual nonzero hyperplane. -/
theorem integral_norm_cellAmp_slice_le (p q : Mom d) {x : Mom d} (hx : x ≠ 0) :
    (∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellAmp p q x w‖) ≤ cellConst d 1*NTSP.sliceConst d 2 := by
  have hB := ntBounds_cellAmp (d := d) 1 (c := 1) (by simp) p q
  have hh := NTSP.norm_sliceAmp_le hB two_pos p q 0 0 hx 0
  rw [NTSP.sliceAmp] at hh
  simp only [zero_smul,zero_add] at hh
  rw [amp_cellAmp_eq] at hh
  rw [integral_norm_cellAmp_slice_eq]
  apply hh.trans
  calc
    _ ≤ cellConst d 1*1*NTSP.sliceConst d 2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (NTSP.norm_chiScaled_le_one 2 (x-p)) hB.nonneg)
      (NTSP.sliceConst_nonneg d (by norm_num : (0:ℝ) ≤ 2))
    _ = _ := by rw [mul_one]

variable {U : Type*} [MeasurableSpace U] (ν : Measure U) [SFinite ν]

/-- The original spectral cell mixture has its actual absolute plane
mass bounded by the same cell plane mass times its coefficient L1 norm. -/
theorem integral_norm_cellMixture_slice_le (p q : Mom d) {ξ η : U → Mom d}
    (hξ : Measurable ξ) (hη : Measurable η) {h : U → ℂ} (hh : Integrable h ν)
    {x : Mom d} (hx : x ≠ 0) :
    (∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellMixture ν p q ξ η h x w‖) ≤
      (∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellAmp p q x w‖)*(∫ u, ‖h u‖ ∂ν) := by
  have hi := (delta_slice p q hξ hη hh hx).1.norm
  have hb := (integrable_cellAmp_slice p q hx).norm.mul_const (∫ u, ‖h u‖ ∂ν)
  calc
    _ ≤ ∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellAmp p q x w‖*(∫ u, ‖h u‖ ∂ν) :=
      integral_mono hi hb (fun w => norm_cellMixture_le ν p q ξ η h x w)
    _ = _ := integral_mul_const _ _

/-- The literal weighted hyperplane integrand of each mixture is
controlled by its positive absolute cell mass, pointwise in x. -/
theorem norm_delta_cellMixture_le (p q : Mom d) {ξ η : U → Mom d}
    (hξ : Measurable ξ) (hη : Measurable η) {h : U → ℂ} (hh : Integrable h ν) (x : Mom d) :
    ‖((‖x‖⁻¹ : ℝ):ℂ)*(∫ w : ↥(ℝ ∙ x)ᗮ, cellMixture ν p q ξ η h x w)‖ ≤
      (∫ u, ‖h u‖ ∂ν)*deltaCellMass p q x := by
  by_cases hx : x = 0
  · simp [hx,deltaCellMass]
  · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hh' := (norm_integral_le_integral_norm _).trans (integral_norm_cellMixture_slice_le ν p q hξ hη hh hx)
    exact (mul_le_mul_of_nonneg_left hh' (inv_nonneg.mpr (norm_nonneg _))).trans_eq (by unfold deltaCellMass; ring)

/-- The full weighted hyperplane L1 mass is uniformly bounded in the
centers and all modulation frequencies. -/
theorem integral_norm_delta_cellMixture_le (hd : 3 ≤ d) (p q : Mom d) {ξ η : U → Mom d}
    (hξ : Measurable ξ) (hη : Measurable η) {h : U → ℂ} (hh : Integrable h ν) :
    (∫ x : Mom d, ‖((‖x‖⁻¹ : ℝ):ℂ)*(∫ w : ↥(ℝ ∙ x)ᗮ, cellMixture ν p q ξ η h x w)‖) ≤
      cellCa d*(∫ u, ‖h u‖ ∂ν) := by
  have hi := (delta_term hd p q hξ hη hh).2.1.norm
  have hb := (integrable_deltaCellMass hd p q).const_mul (∫ u, ‖h u‖ ∂ν)
  calc
    _ ≤ ∫ x, (∫ u, ‖h u‖ ∂ν)*deltaCellMass p q x :=
      integral_mono hi hb (fun x => norm_delta_cellMixture_le ν p q hξ hη hh x)
    _ = (∫ u, ‖h u‖ ∂ν)*(∫ x, deltaCellMass p q x) := integral_const_mul _ _
    _ ≤ (∫ u, ‖h u‖ ∂ν)*cellCa d := mul_le_mul_of_nonneg_left
      (integral_deltaCellMass_le hd p q) (integral_nonneg (fun _ => norm_nonneg _))
    _ = _ := mul_comm _ _

/-- Countably many translated source cells commute with the actual
hyperplane delta functional. Both levels of Fubini use explicit absolute
slice masses, uniformly bounded in the source cell centers. -/
theorem deltaInner_tsum_integral_cells {I : Type*} [Countable I] (hd : 3 ≤ d)
    (p q : I → Mom d) (ξ η : I → U → Mom d)
    (hξ : ∀ i, Measurable (ξ i)) (hη : ∀ i, Measurable (η i))
    (h : I → U → ℂ) (hi : ∀ i, Integrable (h i) ν)
    (hsum : Summable (fun i => ∫ u, ‖h i u‖ ∂ν)) :
    NTSP.deltaInner (fun x y => ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x y) =
      ∑' i, ∫ u, h i u*NTSP.deltaInner (cellFn (p i) (q i) (ξ i u) (η i u)) ∂ν := by
  have hplane (x : Mom d) (hx : x ≠ 0) : Summable (fun i =>
      ∫ w : ↥(ℝ ∙ x)ᗮ, ‖cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x w‖) := by
    apply (hsum.mul_left (cellConst d 1*NTSP.sliceConst d 2)).of_norm_bounded
    intro i
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact (integral_norm_cellMixture_slice_le ν (p i) (q i) (hξ i) (hη i) (hi i) hx).trans
      (mul_le_mul_of_nonneg_right (integral_norm_cellAmp_slice_le (p i) (q i) hx)
        (integral_nonneg (fun _ => norm_nonneg _)))
  have heplane (x : Mom d) (hx : x ≠ 0) :
      (∫ w : ↥(ℝ ∙ x)ᗮ, ∑' i, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x w) =
        ∑' i, ∫ w : ↥(ℝ ∙ x)ᗮ, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x w :=
    (integral_tsum_of_summable_integral_norm
      (fun i => (delta_slice (p i) (q i) (hξ i) (hη i) (hi i) hx).1) (hplane x hx)).symm
  let F := fun (i : I) (x : Mom d) =>
    ((‖x‖⁻¹ : ℝ):ℂ)*(∫ w : ↥(ℝ ∙ x)ᗮ, cellMixture ν (p i) (q i) (ξ i) (η i) (h i) x w)
  have hFi (i : I) : Integrable (F i) := (delta_term hd (p i) (q i) (hξ i) (hη i) (hi i)).2.1
  have hFs : Summable (fun i => ∫ x : Mom d, ‖F i x‖) := by
    apply (hsum.mul_left (cellCa d)).of_norm_bounded
    intro i
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_norm_delta_cellMixture_le ν hd (p i) (q i) (hξ i) (hη i) (hi i)
  rw [NTSP.deltaInner]
  calc
    _ = ∫ x : Mom d, ∑' i, F i x := by
      apply integral_congr_ae
      filter_upwards [NTSP.ae_ne_zero_mom (show 0 < d by omega)] with x hx
      rw [heplane x hx]
      exact (tsum_mul_left).symm
    _ = ∑' i, ∫ x : Mom d, F i x := (integral_tsum_of_summable_integral_norm hFi hFs).symm
    _ = _ := by
      apply tsum_congr
      intro i
      exact (delta_term hd (p i) (q i) (hξ i) (hη i) (hi i)).2.2

end WaveTurbulence.RegAsymp
