/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Cells
public import WaveTurbulence.Foundations.ApproxNT.FourierW
public import WaveTurbulence.Foundations.ApproxNT.CellEstimate

/-!
# Decomposition of `I` and of the main integral into cells (packet NT6)

For a configuration `pq` and a frequency `τ = (ξ, η)`, `cellData pq τ` is the data of the core
estimate. With `W = ∫ Ŵ(τ) e(τ·(x,y)) dτ`:

* `approxSum (W · cellWeight pq) Ψ = ∫ Ŵ(τ) multiSum(cellData pq τ) dτ`;
* `approxInt (W · cellWeight pq) Ψ = ∫ Ŵ(τ) multiInt(cellData pq τ) dτ`;
* on a cell, the profile `Ψ` of (propertypsi1) coincides with the truncated profile.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped FourierTransform ContDiff

namespace WaveTurbulence.ApproxNT

variable {d n : ℕ}

/-- The cell data of a configuration `pq` and a frequency `τ`. -/
@[expose] def cellData (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) : CellData d (Fin n) :=
  ⟨fun j => NTSP.intVec (pq j).1, fun j => NTSP.intVec (pq j).2, τ.1, τ.2⟩

/-- The phase `e(∑_j ⟨x_j, ξ_j⟩ + ⟨y_j, η_j⟩)`. -/
@[expose] def wPhase (x y : Fin n → Mom d) (τ : (Fin n → Mom d) × (Fin n → Mom d)) : ℂ :=
  (𝐞 (∑ j, (inner ℝ (x j) (τ.1 j) + inner ℝ (y j) (τ.2 j))) : ℂ)

theorem multiAmp_cellData (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) (w : Fin n → Mom d × Mom d) :
    multiAmp (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ w =
      wPhase (fun j => (w j).1) (fun j => (w j).2) τ *
        cellWeight pq (fun j => (w j).1) (fun j => (w j).2) := by
  simp only [multiAmp, pairAmp, cellData, wPhase, cellWeight, Circle.smul_def, smul_eq_mul,
    prod_mul_distrib]
  rw [fourierChar_finset_sum]

/-- The pair-of-tuples form of a tuple of pairs. -/
@[expose] def unzipW (w : Fin n → Mom d × Mom d) : (Fin n → Mom d) × (Fin n → Mom d) :=
  (fun j => (w j).1, fun j => (w j).2)

theorem measurePreserving_unzipW :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow (Mom d) (Mom d) (Fin n)) := by
  have h := measurePreserving_arrowProdEquivProdArrow (Mom d) (Mom d) (Fin n)
    (fun _ => (volume : Measure (Mom d))) (fun _ => (volume : Measure (Mom d)))
  convert h using 1

theorem unzipW_eq (w : Fin n → Mom d × Mom d) :
    MeasurableEquiv.arrowProdEquivProdArrow (Mom d) (Mom d) (Fin n) w = unzipW w := rfl

/-- The lattice sum of one cell, in Fourier form. -/
theorem approxSum_cell {L : ℝ} (hL : 0 < L) (μ : ℝ) {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hinv : ∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ)
    (hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2))
    (Ψ : (Fin n → ℝ) → ℂ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    approxSum L μ (fun x y => W x y * cellWeight pq x y) Ψ =
      ∫ τ, fourierW W τ.1 τ.2 * multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ := by
  set e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  set G : Finset (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :=
    Fintype.piFinset fun j => cellIndex hL (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)
  have hcw : ∀ g ∉ G, cellWeight pq (fun j => latticePoint L (g j).1)
      (fun j => latticePoint L (g j).2) = 0 := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    simp only [not_forall] at hg
    obtain ⟨j, hj⟩ := hg
    exact prod_eq_zero (mem_univ j) (cellAmp_lattice_eq_zero hL hj)
  have hint : ∀ g ∈ G, Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      fourierW W τ.1 τ.2 * (wPhase (fun j => latticePoint L (g j).1)
        (fun j => latticePoint L (g j).2) τ * cellWeight pq (fun j => latticePoint L (g j).1)
          (fun j => latticePoint L (g j).2) *
          Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1) (latticePoint L (g j).2)))) := by
    intro g _
    refine hF.mul_bdd (c := ‖cellWeight pq (fun j => latticePoint L (g j).1)
        (fun j => latticePoint L (g j).2) * Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1)
          (latticePoint L (g j).2))‖) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine (Continuous.mul ?_ continuous_const).mul continuous_const
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_finsetSum _ fun j _ =>
          ((continuous_const.inner ((continuous_apply j).comp continuous_fst)).add
            (continuous_const.inner ((continuous_apply j).comp continuous_snd))))
    · refine Filter.Eventually.of_forall fun τ => ?_
      rw [mul_assoc, norm_mul]
      simp [wPhase]
  have hlhs : approxSum L μ (fun x y => W x y * cellWeight pq x y) Ψ =
      ∑ g ∈ G, W (fun j => latticePoint L (g j).1) (fun j => latticePoint L (g j).2) *
        cellWeight pq (fun j => latticePoint L (g j).1) (fun j => latticePoint L (g j).2) *
        Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1) (latticePoint L (g j).2)) := by
    rw [approxSum, ← e.tsum_eq]
    refine (tsum_eq_sum fun g hg => ?_).trans rfl
    change W (fun j => latticePoint L (g j).1) (fun j => latticePoint L (g j).2) *
      cellWeight pq (fun j => latticePoint L (g j).1) (fun j => latticePoint L (g j).2) *
      Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1) (latticePoint L (g j).2)) = 0
    rw [hcw g hg, mul_zero, zero_mul]
  rw [hlhs]
  calc ∑ g ∈ G, W (fun j => latticePoint L (g j).1) (fun j => latticePoint L (g j).2) *
        cellWeight pq (fun j => latticePoint L (g j).1) (fun j => latticePoint L (g j).2) *
        Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1) (latticePoint L (g j).2))
      = ∑ g ∈ G, ∫ τ, fourierW W τ.1 τ.2 * (wPhase (fun j => latticePoint L (g j).1)
          (fun j => latticePoint L (g j).2) τ * cellWeight pq (fun j => latticePoint L (g j).1)
            (fun j => latticePoint L (g j).2) *
            Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1) (latticePoint L (g j).2))) := by
        refine sum_congr rfl fun g _ => ?_
        rw [hinv, mul_assoc, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        ring
    _ = ∫ τ, ∑ g ∈ G, fourierW W τ.1 τ.2 * (wPhase (fun j => latticePoint L (g j).1)
          (fun j => latticePoint L (g j).2) τ * cellWeight pq (fun j => latticePoint L (g j).1)
            (fun j => latticePoint L (g j).2) *
            Ψ (fun j => μ * inner ℝ (latticePoint L (g j).1) (latticePoint L (g j).2))) :=
        (integral_finsetSum _ hint).symm
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only
        rw [← mul_sum, multiSum]
        congr 1
        rw [tsum_eq_sum (s := G) fun g hg => ?_]
        · refine sum_congr rfl fun g _ => ?_
          rw [multiAmp_cellData]
          rfl
        · rw [multiAmp_cellData]
          simp only [latPair]
          rw [hcw g hg, mul_zero, zero_mul]

/-- The integral of one cell, in Fourier form. -/
theorem approxInt_cell (μ : ℝ) {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hinv : ∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ)
    (hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2))
    (Ψ : (Fin n → ℝ) → ℂ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (hh : Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))))
    (hhm : Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))) :
    approxInt μ (fun x y => W x y * cellWeight pq x y) Ψ =
      ∫ τ, fourierW W τ.1 τ.2 * multiInt μ Ψ (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ := by
  have : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
  have hph : Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) ×
      ((Fin n → Mom d) × (Fin n → Mom d)) => wPhase p.1.1 p.1.2 p.2) := by
    refine (continuous_subtype_val.comp Real.continuous_fourierChar).comp ?_
    refine continuous_finsetSum _ fun j _ => ?_
    exact (((continuous_apply j).comp (continuous_fst.comp continuous_fst)).inner
      ((continuous_apply j).comp (continuous_fst.comp continuous_snd))).add
      (((continuous_apply j).comp (continuous_snd.comp continuous_fst)).inner
      ((continuous_apply j).comp (continuous_snd.comp continuous_snd)))
  have hjoint : Integrable (Function.uncurry fun (z : (Fin n → Mom d) × (Fin n → Mom d))
      (τ : (Fin n → Mom d) × (Fin n → Mom d)) => fourierW W τ.1 τ.2 *
        (wPhase z.1 z.2 τ * (cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))))
      ((volume : Measure ((Fin n → Mom d) × (Fin n → Mom d))).prod volume) := by
    have hp := hh.mul_prod hF
    refine hp.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine (hF.aestronglyMeasurable.comp_snd).mul ?_
      exact (hph.mul (hhm.comp continuous_fst)).aestronglyMeasurable
    · obtain ⟨z, τ⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      have h1 : ‖wPhase z.1 z.2 τ‖ = 1 := by simp [wPhase]
      rw [h1]; ring_nf; exact le_rfl
  calc approxInt μ (fun x y => W x y * cellWeight pq x y) Ψ
      = ∫ z : (Fin n → Mom d) × (Fin n → Mom d), ∫ τ, fourierW W τ.1 τ.2 *
          (wPhase z.1 z.2 τ * (cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))) := by
        rw [approxInt]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hinv z.1 z.2, mul_assoc, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        ring
    _ = ∫ τ, ∫ z : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
          (wPhase z.1 z.2 τ * (cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))) :=
        integral_integral_swap hjoint
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only
        rw [integral_const_mul, multiInt]
        congr 1
        rw [← measurePreserving_unzipW.integral_comp
          (MeasurableEquiv.arrowProdEquivProdArrow (Mom d) (Mom d) (Fin n)).measurableEmbedding]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only [unzipW_eq, unzipW, multiAmp_cellData]
        rw [mul_assoc]
        rfl

/-- The truncation levels of a cell configuration. -/
@[expose] def cellLevels (μ : ℝ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (j : Fin n) : ℕ :=
  ⌈μ * ((‖NTSP.intVec (pq j).1‖ + Real.sqrt d) * (‖NTSP.intVec (pq j).2‖ + Real.sqrt d))⌉₊

theorem norm_le_of_thetaMom_ne_zero {x p : Mom d} (h : thetaMom d (x - p) ≠ 0) :
    ‖x‖ ≤ ‖p‖ + Real.sqrt d := by
  have h1 := thetaMom_support_subset (d := d) h
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  calc ‖x‖ = ‖(x - p) + p‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem abs_le_cellLevels {μ : ℝ} (hμ : 0 ≤ μ) {pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)}
    {x y : Fin n → Mom d} (hw : cellWeight pq x y ≠ 0) (j : Fin n) :
    |μ * inner ℝ (x j) (y j)| ≤ 2 ^ cellLevels μ pq j := by
  have hj : cellAmp (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (x j) (y j) ≠ 0 :=
    fun h => hw (prod_eq_zero (mem_univ j) h)
  have h1 : thetaMom d (x j - NTSP.intVec (pq j).1) ≠ 0 := by
    intro h; apply hj; simp [cellAmp, thetaC, h]
  have h2 : thetaMom d (y j - NTSP.intVec (pq j).2) ≠ 0 := by
    intro h; apply hj; simp [cellAmp, thetaC, h]
  have hx := norm_le_of_thetaMom_ne_zero h1
  have hy := norm_le_of_thetaMom_ne_zero h2
  calc |μ * inner ℝ (x j) (y j)| = μ * |inner ℝ (x j) (y j)| := by rw [abs_mul, abs_of_nonneg hμ]
    _ ≤ μ * (‖x j‖ * ‖y j‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hμ
    _ ≤ μ * ((‖NTSP.intVec (pq j).1‖ + Real.sqrt d) * (‖NTSP.intVec (pq j).2‖ + Real.sqrt d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hx hy (norm_nonneg _) (by positivity)) hμ
    _ ≤ cellLevels μ pq j := Nat.le_ceil _
    _ ≤ 2 ^ cellLevels μ pq j := by exact_mod_cast (Nat.lt_two_pow_self).le

theorem resProfile_eq_truncProfile {μ : ℝ} (hμ : 0 ≤ μ) (J : Finset (Fin n))
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) {pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)}
    {x y : Fin n → Mom d} (hw : cellWeight pq x y ≠ 0) :
    resProfile J Ψ₁ (fun j => μ * inner ℝ (x j) (y j)) =
      truncProfile J (cellLevels μ pq) Ψ₁ (fun j => μ * inner ℝ (x j) (y j)) := by
  rw [resProfile, truncProfile]
  congr 1
  exact prod_congr rfl fun j _ => (mKer_eq (abs_le_cellLevels hμ hw j)).symm

theorem multiSum_res_eq_trunc {L μ : ℝ} (hμ : 0 ≤ μ) (J : Finset (Fin n))
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
    multiSum L μ (resProfile J Ψ₁) (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ
        (cellData pq τ).ζ =
      multiSum L μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ := by
  rw [multiSum, multiSum]
  refine tsum_congr fun g => ?_
  rw [multiAmp_cellData]
  by_cases hw : cellWeight pq (fun j => (latPair L (g j)).1) (fun j => (latPair L (g j)).2) = 0
  · rw [hw, mul_zero, zero_mul, zero_mul]
  · congr 1
    exact resProfile_eq_truncProfile hμ J Ψ₁ hw

theorem multiInt_res_eq_trunc {μ : ℝ} (hμ : 0 ≤ μ) (J : Finset (Fin n))
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
    multiInt μ (resProfile J Ψ₁) (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ
        (cellData pq τ).ζ =
      multiInt μ (truncProfile J (cellLevels μ pq) Ψ₁) (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ := by
  rw [multiInt, multiInt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [multiAmp_cellData]
  by_cases hw : cellWeight pq (fun j => (w j).1) (fun j => (w j).2) = 0
  · rw [hw, mul_zero, zero_mul, zero_mul]
  · congr 1
    exact resProfile_eq_truncProfile hμ J Ψ₁ hw

end WaveTurbulence.ApproxNT
