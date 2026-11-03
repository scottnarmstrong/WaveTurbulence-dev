/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Cell
public import WaveTurbulence.Foundations.NTSP.Lemma65Two

/-!
# One-cell estimates from DH23 Lemma 6.5 (packet NT6)

For one cell, with `φ(s) = χ₀(s/(2L))` (the major-arc cutoff `K = 2L`):

* `‖cellInt(s)‖ ≲ ⟨s⟩^{-d}` (stationary phase), hence `∫|cellInt| ≲ 1` and the tail
  `∫ (1-φ)|cellInt| ≲ L^{-1}`;
* `∫ |φ (cellInt + cellModes)| ≲ 1` (DH23 (NTSPest2), `NTSP.ntsp_two_all`);
* `∫ |φ cellModes| ≲ L^{-1+2η} (1+|ξ|+|η|)` (DH23 Lemma 6.5(2), `NTSP.ntsp_two`).

All constants depend only on `d` (and `η`); they are uniform in the centers and frequencies.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-! ### Finite support of the cell lattice sum -/

theorem finite_thetaLattice {L : ℝ} (hL : 0 < L) (p : Mom d) :
    {g : Fin d → ℤ | thetaMom d (latticePoint L g - p) ≠ 0}.Finite := by
  refine (Set.finite_Icc (fun j => ⌊L * (p j - 1)⌋) (fun j => ⌈L * (p j + 1)⌉)).subset ?_
  intro g hg
  have hj : ∀ j, |(g j : ℝ) / L - p j| < 1 := by
    intro j
    have := abs_lt_one_of_thetaMom_ne_zero hg j
    simpa [latticePoint] using this
  constructor
  · intro j
    have hh := (abs_lt.mp (hj j)).1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hL] at hh
    exact Int.floor_le_iff.mpr (by exact_mod_cast (by linarith : L * (p j - 1) < (g j : ℝ) + 1))
  · intro j
    have hh := (abs_lt.mp (hj j)).2
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hL] at hh
    exact Int.le_ceil_iff.mpr (by exact_mod_cast (by linarith : (g j : ℝ) - 1 < L * (p j + 1)))

/-- The finite set of lattice indices that can contribute to a cell sum. -/
@[expose] def cellIndex {L : ℝ} (hL : 0 < L) (p q : Mom d) : Finset ((Fin d → ℤ) × (Fin d → ℤ)) :=
  (finite_thetaLattice hL p).toFinset ×ˢ (finite_thetaLattice hL q).toFinset

theorem cellAmp_lattice_eq_zero {L : ℝ} (hL : 0 < L) {p q : Mom d}
    {gh : (Fin d → ℤ) × (Fin d → ℤ)} (hgh : gh ∉ cellIndex hL p q) :
    cellAmp p q (latticePoint L gh.1) (latticePoint L gh.2) = 0 := by
  simp only [cellIndex, Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    not_and_or, not_not] at hgh
  rcases hgh with h | h <;> simp [cellAmp, thetaC, h]

theorem cellSum_eq_finset {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) (s : ℝ) :
    cellSum L p q ξ η s = ∑ gh ∈ cellIndex hL p q,
      Real.fourierChar (inner ℝ (latticePoint L gh.1) ξ + inner ℝ (latticePoint L gh.2) η +
        s * inner ℝ (latticePoint L gh.1) (latticePoint L gh.2)) •
        cellAmp p q (latticePoint L gh.1) (latticePoint L gh.2) := by
  rw [cellSum]
  exact tsum_eq_sum fun gh hgh => by rw [cellAmp_lattice_eq_zero hL hgh, smul_zero]

theorem continuous_cellSum {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) :
    Continuous (cellSum L p q ξ η) := by
  have h : cellSum L p q ξ η = fun s => ∑ gh ∈ cellIndex hL p q,
      Real.fourierChar (inner ℝ (latticePoint L gh.1) ξ + inner ℝ (latticePoint L gh.2) η +
        s * inner ℝ (latticePoint L gh.1) (latticePoint L gh.2)) •
        cellAmp p q (latticePoint L gh.1) (latticePoint L gh.2) := by
    funext s; exact cellSum_eq_finset hL p q ξ η s
  rw [h]
  refine continuous_finsetSum _ fun gh _ => ?_
  exact ((Real.continuous_fourierChar.comp (continuous_const.add
    (continuous_id.mul continuous_const))).smul continuous_const)

/-- A crude bound on the cell sum (the number of contributing lattice points). -/
theorem norm_cellSum_le {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) (s : ℝ) :
    ‖cellSum L p q ξ η s‖ ≤ (cellIndex hL p q).card := by
  rw [cellSum_eq_finset hL]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ gh ∈ cellIndex hL p q, ‖Real.fourierChar (inner ℝ (latticePoint L gh.1) ξ +
        inner ℝ (latticePoint L gh.2) η + s * inner ℝ (latticePoint L gh.1) (latticePoint L gh.2)) •
        cellAmp p q (latticePoint L gh.1) (latticePoint L gh.2)‖
      ≤ ∑ _gh ∈ cellIndex hL p q, (1 : ℝ) := by
        refine sum_le_sum fun gh _ => ?_
        rw [Circle.norm_smul]
        exact norm_cellAmp_le_one _ _ _ _
    _ = (cellIndex hL p q).card := by simp

/-! ### The cell integral -/

theorem cellInt_eq_prod (p q ξ η : Mom d) (s : ℝ) :
    cellInt p q ξ η s = ∫ z : Mom d × Mom d,
      Real.fourierChar (inner ℝ z.1 ξ + inner ℝ z.2 η + s * inner ℝ z.1 z.2) •
        cellAmp p q z.1 z.2 := by
  have hint := ((contDiff_cellIntegrand p q ξ η s).continuous).integrable_of_hasCompactSupport
    (μ := (volume : Measure (Mom d × Mom d))) (hasCompactSupport_cellIntegrand p q ξ η s)
  have h2 := integral_prod_symm _ hint
  simp only at h2
  rw [cellInt_eq]
  exact h2.symm

theorem integrable_cellAmp (p q : Mom d) :
    Integrable (fun z : Mom d × Mom d => cellAmp p q z.1 z.2) := by
  have h := ((contDiff_cellIntegrand p q 0 0 0).continuous).integrable_of_hasCompactSupport
    (μ := (volume : Measure (Mom d × Mom d))) (hasCompactSupport_cellIntegrand p q 0 0 0)
  refine h.norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (((contDiff_thetaC (d := d)).continuous.comp (continuous_fst.sub continuous_const)).mul
      ((contDiff_thetaC (d := d)).continuous.comp (continuous_snd.sub continuous_const))).aestronglyMeasurable
  · simp

theorem continuous_cellInt (p q ξ η : Mom d) : Continuous (cellInt p q ξ η) := by
  have h : cellInt p q ξ η = fun s => ∫ z : Mom d × Mom d,
      Real.fourierChar (inner ℝ z.1 ξ + inner ℝ z.2 η + s * inner ℝ z.1 z.2) •
        cellAmp p q z.1 z.2 := by
    funext s; exact cellInt_eq_prod p q ξ η s
  rw [h]
  refine continuous_of_dominated (bound := fun z => ‖cellAmp p q z.1 z.2‖) (fun s => ?_)
    (fun s => Filter.Eventually.of_forall fun z => ?_) (integrable_cellAmp p q).norm
    (Filter.Eventually.of_forall fun z => ?_)
  · exact ((contDiff_cellIntegrand p q ξ η s).continuous).aestronglyMeasurable
  · rw [Circle.norm_smul]
  · exact ((Real.continuous_fourierChar.comp (continuous_const.add
      (continuous_id.mul continuous_const))).smul continuous_const)

/-- The stationary-phase constant of one cell. -/
@[expose] def cellK0 (d : ℕ) : ℝ := NTSP.termConst d (d + 1) * cellConst d (d + 1) * 2 ^ (2 * d)

theorem cellK0_nonneg (d : ℕ) : 0 ≤ cellK0 d := by
  have := NTSP.termConst_nonneg d (d + 1); have := cellConst_nonneg d (d + 1)
  unfold cellK0; positivity

/-- Stationary phase for one cell: `‖cellInt(s)‖ ≤ K₀ (1+|s|)^{-d}`. -/
theorem norm_cellInt_le (p q ξ η : Mom d) (s : ℝ) :
    ‖cellInt p q ξ η s‖ ≤ cellK0 d * ((1 + |s|) ^ d)⁻¹ := by
  have hB := ntBounds_cellAmp (d := d) (d + 1) (c := 1) (by simp) p q
  have h := NTSP.norm_ntIntegral_le_stat le_rfl hB (by norm_num : (1 : ℝ) ≤ 2) p q ξ η s
  rw [ntIntegral_const_mul_cellAmp, one_mul] at h
  calc ‖cellInt p q ξ η s‖ ≤ _ := h
    _ = cellK0 d * ((1 + |s|) ^ d)⁻¹ := by unfold cellK0; ring

theorem integrable_cellInt (hd : 2 ≤ d) (p q ξ η : Mom d) : Integrable (cellInt p q ξ η) := by
  refine ((NTSP.integrable_inv_one_add_abs_pow hd).const_mul (cellK0 d)).mono'
    (continuous_cellInt p q ξ η).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  exact norm_cellInt_le p q ξ η s

theorem lintegral_cellInt_le (hd : 2 ≤ d) (p q ξ η : Mom d) :
    ∫⁻ s, ‖cellInt p q ξ η s‖ₑ ≤ ENNReal.ofReal (cellK0 d * NTSP.sInt d) :=
  NTSP.lintegral_le_of_le_inv_pow hd (cellK0_nonneg d) fun s => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_cellInt_le p q ξ η s)

/-- The major-arc cutoff `φ(s) = χ₀(s/(2L))`. -/
@[expose] def majorCut (L s : ℝ) : ℂ := (Fourier.chi0 (s / (2 * L)) : ℂ)

/-- The minor-arc cutoff `1 - φ(s)`. -/
@[expose] def minorCut (L s : ℝ) : ℂ := (Fourier.chiInfinity (s / (2 * L)) : ℂ)

theorem majorCut_add_minorCut (L s : ℝ) : majorCut L s + minorCut L s = 1 := by
  simp [majorCut, minorCut, Fourier.chiInfinity]

theorem norm_majorCut_le (L s : ℝ) : ‖majorCut L s‖ ≤ 1 := by
  rw [majorCut, Complex.norm_real, Real.norm_of_nonneg (Fourier.chi0_nonneg _)]
  exact Fourier.chi0_le_one _

theorem norm_minorCut_le (L s : ℝ) : ‖minorCut L s‖ ≤ 1 := by
  have h0 := Fourier.chi0_nonneg (s / (2 * L)); have h1 := Fourier.chi0_le_one (s / (2 * L))
  rw [minorCut, Complex.norm_real, Fourier.chiInfinity, Real.norm_of_nonneg (by linarith)]
  linarith

theorem continuous_majorCut (L : ℝ) : Continuous (majorCut L) :=
  Complex.continuous_ofReal.comp ((Fourier.chi0_contDiff (n := 0)).continuous.comp
    (continuous_id.div_const _))

theorem continuous_minorCut (L : ℝ) : Continuous (minorCut L) :=
  Complex.continuous_ofReal.comp ((continuous_const.sub (Fourier.chi0_contDiff (n := 0)).continuous).comp
    (continuous_id.div_const _))

theorem majorCut_eq_zero {L s : ℝ} (hL : 0 < L) (hs : 2 * L < |s|) : majorCut L s = 0 := by
  rw [majorCut, Fourier.chi0_eq_zero, Complex.ofReal_zero]
  rw [abs_div, abs_of_pos (by linarith : 0 < 2 * L), le_div_iff₀ (by linarith)]
  linarith

theorem minorCut_eq_zero {L s : ℝ} (hL : 0 < L) (hs : |s| ≤ L) : minorCut L s = 0 := by
  rw [minorCut, Fourier.chiInfinity, Fourier.chi0_eq_one, sub_self, Complex.ofReal_zero]
  rw [abs_div, abs_of_pos (by linarith : 0 < 2 * L), div_le_iff₀ (by linarith)]
  linarith

/-- The major-arc tail of the cell integral: `∫ |(1-φ) cellInt| ≲ L^{-1}`. -/
theorem lintegral_minorCut_cellInt_le (hd : 3 ≤ d) {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) :
    ∫⁻ s, ‖minorCut L s * cellInt p q ξ η s‖ₑ ≤
      ENNReal.ofReal (cellK0 d * L⁻¹ * NTSP.sInt (d - 1)) := by
  have hK := cellK0_nonneg d
  have hC : 0 ≤ cellK0 d * L⁻¹ := mul_nonneg hK (inv_nonneg.2 hL.le)
  refine NTSP.lintegral_le_of_le_inv_pow (by omega) hC fun s => ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hs : |s| ≤ L
  · rw [minorCut_eq_zero hL hs, zero_mul, norm_zero]; positivity
  · rw [not_le] at hs
    rw [norm_mul]
    have h1 := norm_minorCut_le L s
    have h2 := norm_cellInt_le p q ξ η s
    have hpos : 0 < 1 + |s| := by positivity
    have hpow : (1 + |s|) ^ d = (1 + |s|) * (1 + |s|) ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h3 : ((1 + |s|) ^ d)⁻¹ ≤ L⁻¹ * ((1 + |s|) ^ (d - 1))⁻¹ := by
      rw [hpow, mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact inv_anti₀ hL (by linarith)
    calc ‖minorCut L s‖ * ‖cellInt p q ξ η s‖ ≤ 1 * (cellK0 d * ((1 + |s|) ^ d)⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ ≤ cellK0 d * L⁻¹ * ((1 + |s|) ^ (d - 1))⁻¹ := by
          rw [one_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hK

/-! ### The major arc: DH23 Lemma 6.5(2) and (NTSPest2) -/

/-- The amplitude `φ(s) θ(x-p) θ(y-q)` used with Lemma 6.5. -/
theorem ntIntegral_majorCut (L : ℝ) (p q ξ η : Mom d) (s : ℝ) :
    NTSP.ntIntegral 2 (fun x y => majorCut L s * cellAmp p q x y) p q ξ η s =
      majorCut L s * cellInt p q ξ η s :=
  ntIntegral_const_mul_cellAmp _ p q ξ η s

theorem majorCut_mul_cellSum {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) (s : ℝ) :
    majorCut L s * (cellInt p q ξ η s + cellModes L p q ξ η s) =
      ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), NTSP.ntIntegral 2
        (fun x y => majorCut L s * cellAmp p q x y) p q
        (L • NTSP.intVec gh.1 + ξ) (L • NTSP.intVec gh.2 + η) s := by
  have hL2 : ((L ^ (2 * d) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL _).ne'
  simp_rw [ntIntegral_majorCut]
  rw [tsum_mul_left]
  congr 1
  have h := cellSum_eq_poisson hL p q ξ η s
  rw [cellModes, h]
  field_simp
  ring

/-- (NTSPest2) for one cell, with the major-arc cutoff. -/
theorem exists_lintegral_major_le (hd : 3 ≤ d) {η : ℝ} (hη : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → 2 ≤ L ^ η → ∀ p q ξ ζ : Mom d,
      ∫⁻ s, ‖majorCut L s * (cellInt p q ξ ζ s + cellModes L p q ξ ζ s)‖ₑ ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := NTSP.ntsp_two_all d hd (κ := 2) (by norm_num) hη
  refine ⟨max (C * cellConst d (10 * d) * 2 ^ (2 * d)) 0, le_max_right _ _, ?_⟩
  intro L hL hLη p q ξ ζ
  have hL0 : 0 < L := by linarith
  have hB : ∀ s, NTSP.NTBounds (10 * d) (cellConst d (10 * d))
      (fun x y => majorCut L s * cellAmp p q x y) :=
    fun s => ntBounds_cellAmp _ (norm_majorCut_le L s) p q
  have hsupp : ∀ s, 2 * L < |s| → ∀ x y, majorCut L s * cellAmp p q x y = 0 := by
    intro s hs x y; rw [majorCut_eq_zero hL0 hs, zero_mul]
  have h := hC (cellConst d (10 * d)) L 2 (fun s x y => majorCut L s * cellAmp p q x y) hL
    (by norm_num) hLη hB hsupp p q ξ ζ
  simp_rw [majorCut_mul_cellSum hL0]
  exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- DH23 Lemma 6.5(2) for one cell, with the major-arc cutoff. -/
theorem exists_lintegral_modes_le (hd : 3 ≤ d) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → 2 ≤ L ^ η → ∀ p q ξ ζ : Mom d,
      ∫⁻ s, ‖majorCut L s * cellModes L p q ξ ζ s‖ₑ ≤
        ENNReal.ofReal (C * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖)) := by
  obtain ⟨C, hC⟩ := NTSP.ntsp_two d hd (κ := 2) (by norm_num) hη0 hη
  refine ⟨max (C * cellConst d (10 * d) * 2 ^ (2 * d)) 0, le_max_right _ _, ?_⟩
  intro L hL hLη p q ξ ζ
  have hL0 : 0 < L := by linarith
  have hB : ∀ s, NTSP.NTBounds (10 * d) (cellConst d (10 * d))
      (fun x y => majorCut L s * cellAmp p q x y) :=
    fun s => ntBounds_cellAmp _ (norm_majorCut_le L s) p q
  have hsupp : ∀ s, 2 * L < |s| → ∀ x y, majorCut L s * cellAmp p q x y = 0 := by
    intro s hs x y; rw [majorCut_eq_zero hL0 hs, zero_mul]
  obtain ⟨hsum, h⟩ := hC (cellConst d (10 * d)) L 2 (fun s x y => majorCut L s * cellAmp p q x y)
    hL (by norm_num) hLη hB hsupp p q ξ ζ
  have heq : ∀ s, majorCut L s * cellModes L p q ξ ζ s =
      ∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0}, NTSP.ntIntegral 2
        (fun x y => majorCut L s * cellAmp p q x y) p q
        (L • NTSP.intVec gh.1.1 + ξ) (L • NTSP.intVec gh.1.2 + ζ) s := by
    intro s
    set f : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun gh => NTSP.ntIntegral 2
      (fun x y => majorCut L s * cellAmp p q x y) p q
      (L • NTSP.intVec gh.1 + ξ) (L • NTSP.intVec gh.2 + ζ) s
    have hs : Summable f := (hsum s).of_norm
    have h0 : f 0 = majorCut L s * cellInt p q ξ ζ s := by
      simp only [f, Prod.fst_zero, Prod.snd_zero, NTSP.intVec_zero, smul_zero, zero_add]
      exact ntIntegral_majorCut L p q ξ ζ s
    have hsplit : ∑' gh, f gh = f 0 + ∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0}, f gh := by
      rw [← hs.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton]
      rfl
    have hall := majorCut_mul_cellSum hL0 p q ξ ζ s
    rw [hsplit, h0, mul_add] at hall
    exact add_left_cancel hall
  simp_rw [heq]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hn : 0 ≤ 1 + ‖ξ‖ + ‖ζ‖ := by positivity
  have hLp : 0 ≤ L ^ (-1 + 2 * η) := Real.rpow_nonneg hL0.le _
  have h2 : C * cellConst d (10 * d) * 2 ^ (2 * d) ≤ max (C * cellConst d (10 * d) * 2 ^ (2 * d)) 0 :=
    le_max_left _ _
  calc C * cellConst d (10 * d) * 2 ^ (2 * d) * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖)
      ≤ max (C * cellConst d (10 * d) * 2 ^ (2 * d)) 0 * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖) := by
        gcongr
    _ = _ := rfl

end WaveTurbulence.ApproxNT
