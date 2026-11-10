/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.CellBounds
public import WaveTurbulence.Foundations.WeylSums.MinorArcs2

/-!
# The minor-arc estimate for one cell: DH23 Lemma 6.6(2) (packet NT6)

With the minor-arc cutoff `1 - χ₀(s/(2L))`, which vanishes for `|s| ≤ L`, the landed
`WeylSums.dh23_minor2_normalized_bound` (DH23 Lemma 6.6(2), with `P = 2d`) gives
`∫ ⟨s/(δL^{2γ})⟩^{-2d} |(1-φ(s)) cellSum(s)| ds ≲ L^{2d-2(d-1)(1-γ)+η}`, uniformly in the cell
centers and frequencies.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

theorem natCast_le_infty (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- Extraction of one momentum from packed coordinates, as a continuous linear map. -/
@[expose] def unpackCLM (d : ℕ) (k : Fin 2) : EuclideanSpace ℝ (Fin d × Fin 2) →L[ℝ] Mom d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => PiLp.proj 2 (fun _ : Fin d × Fin 2 => ℝ) (j, k))

/-- The packed cell amplitude centered at the origin. -/
@[expose] def cellG (d : ℕ) (z : EuclideanSpace ℝ (Fin d × Fin 2)) : ℂ :=
  cellAmp 0 0 (WeylSums.unpackBilinear z 0) (WeylSums.unpackBilinear z 1)

theorem contDiff_cellG : ContDiff ℝ ∞ (cellG d) := by
  have h0 : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin d × Fin 2) =>
      thetaC (WeylSums.unpackBilinear z 0 - 0)) :=
    (contDiff_thetaC (d := d)).comp ((unpackCLM d 0).contDiff.sub contDiff_const)
  have h1 : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin d × Fin 2) =>
      thetaC (WeylSums.unpackBilinear z 1 - 0)) :=
    (contDiff_thetaC (d := d)).comp ((unpackCLM d 1).contDiff.sub contDiff_const)
  exact h0.mul h1

theorem hasCompactSupport_cellG : HasCompactSupport (cellG d) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d × Fin 2)) (Real.sqrt (2 * d))) ?_
  intro z hz
  have hz0 : thetaMom d (WeylSums.unpackBilinear z 0 - 0) ≠ 0 := by
    intro h; apply hz; rw [sub_zero] at h; simp [cellG, cellAmp, thetaC, h]
  have hz1 : thetaMom d (WeylSums.unpackBilinear z 1 - 0) ≠ 0 := by
    intro h; apply hz; rw [sub_zero] at h; simp [cellG, cellAmp, thetaC, h]
  have hc : ∀ jk : Fin d × Fin 2, |z jk| < 1 := by
    rintro ⟨j, k⟩
    fin_cases k
    · simpa [WeylSums.unpackBilinear] using abs_lt_one_of_thetaMom_ne_zero hz0 j
    · simpa [WeylSums.unpackBilinear] using abs_lt_one_of_thetaMom_ne_zero hz1 j
  rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ jk, ‖z jk‖ ^ 2 ≤ ∑ _jk : Fin d × Fin 2, (1 : ℝ) := by
        refine sum_le_sum fun jk _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        have := hc jk
        nlinarith [abs_nonneg (z jk), sq_abs (z jk)]
    _ = 2 * d := by simp [mul_comm]

/-- Uniform bounds for the derivatives of the packed cell amplitude. -/
theorem exists_iteratedFDeriv_cellG_le (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ N, ∀ z, ‖iteratedFDeriv ℝ j (cellG d) z‖ ≤ B := by
  have hb : ∀ j, ∃ B : ℝ, ∀ z, ‖iteratedFDeriv ℝ j (cellG d) z‖ ≤ B := by
    intro j
    exact (contDiff_cellG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_cellG.iteratedFDeriv j)
  choose B hB using hb
  refine ⟨∑ j ∈ range (N + 1), |B j|, sum_nonneg fun j _ => abs_nonneg _, fun j hj z => ?_⟩
  exact (hB j z).trans ((le_abs_self _).trans
    (single_le_sum (f := fun j => |B j|) (fun i _ => abs_nonneg _) (mem_range.2 (by omega))))

theorem unpack_sub (z w : EuclideanSpace ℝ (Fin d × Fin 2)) (k : Fin 2) :
    WeylSums.unpackBilinear (z - w) k = WeylSums.unpackBilinear z k - WeylSums.unpackBilinear w k := by
  ext j; simp [WeylSums.unpackBilinear]

theorem packed_cellAmp (c : ℂ) (p q : Mom d) (z : EuclideanSpace ℝ (Fin d × Fin 2)) :
    WeylSums.packedBilinearAmplitude (fun x y => c * cellAmp p q x y) z =
      c * cellG d (z - WeylSums.packBilinear p q) := by
  simp [WeylSums.packedBilinearAmplitude, cellG, cellAmp, unpack_sub]

theorem coordinateDerivativeBound_cellAmp (N : ℕ) {B : ℝ}
    (hB : ∀ j ≤ N, ∀ z, ‖iteratedFDeriv ℝ j (cellG d) z‖ ≤ B) {c : ℂ} (hc : ‖c‖ ≤ 1)
    (p q : Mom d) :
    WeylSums.CoordinateDerivativeBound N
      (WeylSums.packedBilinearAmplitude (fun x y => c * cellAmp p q x y)) B := by
  intro j hj z v
  have hfun : WeylSums.packedBilinearAmplitude (fun x y => c * cellAmp p q x y) =
      c • (fun z => cellG d (z - WeylSums.packBilinear p q)) := by
    funext z; rw [packed_cellAmp]; rfl
  have hsm : ContDiff ℝ ∞ (fun z => cellG d (z - WeylSums.packBilinear p q)) :=
    contDiff_cellG.comp (contDiff_id.sub contDiff_const)
  rw [hfun, iteratedFDeriv_const_smul_apply (hsm.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_sub]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp only [fun i => (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d × Fin 2)).1 i,
    prod_const_one, mul_one]
  rw [norm_smul]
  calc ‖c‖ * ‖iteratedFDeriv ℝ j (cellG d) (z - WeylSums.packBilinear p q)‖ ≤ 1 * B :=
        mul_le_mul hc (hB j hj _) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

theorem latticeCutoff_half_mul_thetaC (p x : Mom d) :
    ((WeylSums.latticeCutoff ((2 : ℝ)⁻¹ • (x - p)) : ℝ) : ℂ) * thetaC (x - p) = thetaC (x - p) := by
  by_cases h : thetaMom d (x - p) = 0
  · simp [thetaC, h]
  · have h1 : WeylSums.latticeCutoff ((2 : ℝ)⁻¹ • (x - p)) = 1 := by
      rw [WeylSums.latticeCutoff, Finset.prod_eq_one]
      intro i _
      apply Fourier.chi0_eq_one
      have hi := abs_lt_one_of_thetaMom_ne_zero h i
      have he : ((2 : ℝ)⁻¹ • (x - p)) i = 2⁻¹ * (x - p) i := by simp
      rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
      linarith
    rw [h1, Complex.ofReal_one, one_mul]

theorem e_eq_fourierChar (t : ℝ) : WeylSums.e t = (Real.fourierChar t : ℂ) := by
  rw [WeylSums.e, Real.fourierChar_apply]

theorem weightedBilinearLatticeSum_cell (L : ℝ) (p q ξ ζ : Mom d) (s : ℝ) :
    WeylSums.weightedBilinearLatticeSum (fun s x y => minorCut L s * cellAmp p q x y) L 2 s
      p q ξ ζ = minorCut L s * cellSum L p q ξ ζ s := by
  rw [WeylSums.weightedBilinearLatticeSum, cellSum, ← tsum_mul_left]
  refine tsum_congr fun gh => ?_
  set x := latticePoint L gh.1
  set y := latticePoint L gh.2
  have h1 := latticeCutoff_half_mul_thetaC p x
  have h2 := latticeCutoff_half_mul_thetaC q y
  rw [Circle.smul_def, e_eq_fourierChar]
  simp only [cellAmp, Complex.ofReal_mul]
  calc ((WeylSums.latticeCutoff ((2 : ℝ)⁻¹ • (x - p)) : ℝ) : ℂ) *
        ((WeylSums.latticeCutoff ((2 : ℝ)⁻¹ • (y - q)) : ℝ) : ℂ) *
        (minorCut L s * (thetaC (x - p) * thetaC (y - q))) *
        (Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) : ℂ)
      = minorCut L s * ((Real.fourierChar (inner ℝ x ξ + inner ℝ y ζ + s * inner ℝ x y) : ℂ) *
          ((((WeylSums.latticeCutoff ((2 : ℝ)⁻¹ • (x - p)) : ℝ) : ℂ) * thetaC (x - p)) *
          (((WeylSums.latticeCutoff ((2 : ℝ)⁻¹ • (y - q)) : ℝ) : ℂ) * thetaC (y - q)))) := by ring
    _ = _ := by rw [h1, h2, smul_eq_mul]

/-- DH23 Lemma 6.6(2) for one cell (with `P = 2d`). -/
theorem exists_lintegral_minor_le (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 2 ≤ L → ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 → ∀ p q ξ ζ : Mom d,
      ∫⁻ s, ENNReal.ofReal (WeylSums.japaneseTimeWeight (δ * L ^ (2 * γ)) (2 * d) s) *
          ‖minorCut L s * cellSum L p q ξ ζ s‖ₑ ≤
        ENNReal.ofReal (C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)) := by
  obtain ⟨C, hC, hmain⟩ := WeylSums.dh23_minor2_normalized_bound d hd γ hγ η hη
  obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_cellG_le (d := d) (10 * d)
  refine ⟨C * B * 2 ^ (4 * d), by positivity, ?_⟩
  intro L hL δ hδ p q ξ ζ
  have hL0 : 0 < L := by linarith
  set Φ : ℝ → Mom d → Mom d → ℂ := fun s x y => minorCut L s * cellAmp p q x y
  have hmeas : ∀ x y, Measurable (fun s => Φ s x y) := fun x y =>
    ((continuous_minorCut L).mul continuous_const).measurable
  have hsmooth : ∀ s, ContDiff ℝ (10 * d) (WeylSums.packedBilinearAmplitude (Φ s)) := by
    intro s
    have h : WeylSums.packedBilinearAmplitude (Φ s) =
        fun z => minorCut L s * cellG d (z - WeylSums.packBilinear p q) := by
      funext z; exact packed_cellAmp _ p q z
    rw [h]
    have h10 : (10 * (d : WithTop ℕ∞)) = ((10 * d : ℕ) : WithTop ℕ∞) := by push_cast; rfl
    rw [h10]
    exact (contDiff_const.mul (contDiff_cellG.comp (contDiff_id.sub contDiff_const))).of_le
      (natCast_le_infty _)
  have hsupp : ∀ s, |s| < L → ∀ x y, Φ s x y = 0 := by
    intro s hs x y
    simp only [Φ, minorCut_eq_zero hL0 hs.le, zero_mul]
  have hcoord : ∀ s, WeylSums.CoordinateDerivativeBound (10 * d)
      (WeylSums.packedBilinearAmplitude (Φ s)) B :=
    fun s => coordinateDerivativeBound_cellAmp _ hB (norm_minorCut_le L s) p q
  obtain ⟨hint, hle⟩ := hmain L 2 δ (2 * d) hL (by norm_num) hδ le_rfl Φ hmeas hsmooth hsupp B hB0
    hcoord p q ξ ζ
  have hrw : ∀ s, WeylSums.weightedBilinearLatticeSum Φ L 2 s p q ξ ζ =
      minorCut L s * cellSum L p q ξ ζ s := fun s => weightedBilinearLatticeSum_cell L p q ξ ζ s
  simp_rw [hrw] at hint hle
  have hw : ∀ s, 0 ≤ WeylSums.japaneseTimeWeight (δ * L ^ (2 * γ)) (2 * d) s :=
    fun s => WeylSums.japaneseTimeWeight_nonneg _ _ _
  calc ∫⁻ s, ENNReal.ofReal (WeylSums.japaneseTimeWeight (δ * L ^ (2 * γ)) (2 * d) s) *
          ‖minorCut L s * cellSum L p q ξ ζ s‖ₑ
      = ∫⁻ s, ENNReal.ofReal (WeylSums.japaneseTimeWeight (δ * L ^ (2 * γ)) (2 * d) s *
          ‖minorCut L s * cellSum L p q ξ ζ s‖) := by
        refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_mul (hw s), ofReal_norm]
    _ = ENNReal.ofReal (∫ s, WeylSums.japaneseTimeWeight (δ * L ^ (2 * γ)) (2 * d) s *
          ‖minorCut L s * cellSum L p q ξ ζ s‖) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun s => mul_nonneg (hw s) (norm_nonneg _))).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (hle.trans (le_of_eq ?_))
        ring

end WaveTurbulence.ApproxNT
